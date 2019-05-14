#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/Transforms/Obfuscation/OpaquePredicate.h"
#include "llvm/Transforms/Obfuscation/CFGFlatObfuscator.h"
#include "llvm/Pass.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/User.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/CodeGen/RegAllocRegistry.h"
#include "llvm/Support/raw_ostream.h"
#include <vector>
#include <set>



using namespace llvm;

#define DEBUG

#ifdef DEBUG

#define log() outs()

#else

#define log() nulls()

#endif

typedef struct CFGNode{
	BasicBlock *beginBB;
	BasicBlock *endBB;
	bool isSame;

	CFGNode(BasicBlock *begin, BasicBlock *end, bool is) : beginBB(begin), endBB(end), isSame(is) {}

	CFGNode(BasicBlock *begin, BasicBlock *end) : beginBB(begin), endBB(end)
	{
		if (begin == end)
			isSame = true;
		else
			isSame = false;
	}

	CFGNode(BasicBlock *begin) : beginBB(begin), endBB(begin), isSame(true) {}

	BasicBlock *getBeginBB() {
		return beginBB;
	}
	BasicBlock *getEndBB() {
		return endBB;	
	}

}CFGNode;



static void handle_main(Function &F);

static void GenOutLineCFG(Function &F, std::vector<CFGNode> &cfgVec);
static void genWhileSwitchStructure(Function &F, size_t caseNumber, SwitchInst **swINC, BasicBlock **obfENTRYBB, BasicBlock **swEPIBB, BasicBlock **whileENDBB);
static void InsertCase(Function &F, SwitchInst *swInc, BasicBlock *obfENTRYBB, BasicBlock *swEPIBB, BasicBlock *whileENDBB, std::vector<CFGNode> &cfgVec);

namespace {

	struct CFGFlatObfuscator : public FunctionPass {
		static char ID;	
		bool flag;
	
		CFGFlatObfuscator() : FunctionPass(ID) {}	
		CFGFlatObfuscator(bool flag) : FunctionPass(ID) {this->flag = flag;}	
	
		bool runOnFunction(Function &F) override {

			if (flag == true) {
				//log() << "即将进行flattening混淆\n";
				log() << "enable CFGFlatObfuscator\n";
				handle_main(F);
				return true;
			}
		
			return false;	
		}

	};
}

char CFGFlatObfuscator::ID = 0;


static RegisterPass<CFGFlatObfuscator> X("CFGFlatObfuscator", "welcome to CFGFlatObfuscator Pass");

Pass *llvm::createFlattening(bool flag){return new CFGFlatObfuscator(flag);}


static BasicBlock* getTargetMergeBBCore(BasicBlock *BB, const char *bbName, std::set<BasicBlock*> &hasHandleBB)
{
	BasicBlock *bb = nullptr;

	if (BB->getName().contains(bbName))
		return BB;

	for(auto it = succ_begin(BB), et = succ_end(BB); it != et; ++it)
	{
		BasicBlock* successorBB = *it;	

		if(hasHandleBB.find(successorBB) == hasHandleBB.end())
			bb = getTargetMergeBBCore(successorBB, bbName, hasHandleBB);

		if (bb)
			return bb;

		hasHandleBB.insert(successorBB);
	}
	return nullptr;
}

static BasicBlock* getTargetMergeBB(BasicBlock *BB, const char *bbName)
{
	std::set<BasicBlock*> hasHandleBB;
	return getTargetMergeBBCore(BB, bbName, hasHandleBB);
}

// POINT 当前函数只有一个ret
// POINT 只处理函数最外层进行分割
static void GenOutLineCFG(Function &F, std::vector<CFGNode> &cfgVec)
{
	// 1. 获取entryBB, 将entryBB以Alloca指令为依据拆分(方便之后更改主控制流)
	BasicBlock *BB = &(F.front());
	cfgVec.emplace_back(BB);	
	//BasicBlock *splitEntryBB = BB->splitBasicBlock(BB->begin(), "entry.split");
	BasicBlock *splitEntryBB = SplitBasicBlockByAlloca(BB, "entry.split");
	BB = splitEntryBB;

	int retFlag = 0;
	while(!retFlag) {

		if (!cfgVec.empty())
			log() << "beginBB name: " << cfgVec.back().getBeginBB()->getName() << "\n"
					<< "endBB name: " << cfgVec.back().getEndBB()->getName() << "\n";
		if (!BB) {
			errs() << "ERROR: BB is nullptr\n";
			return ;
		}

		// 2. 获取BB的BBName, 最后一条指令的Opcode
		//    BB 为当前流程的起始BB
		Instruction &backInstr = BB->back();
		StringRef BBName = BB->getName();
	
		// 3. 确定endBB
		// 	  endBB 为当前流程的结尾BB
		BasicBlock *endBB;   
		switch(backInstr.getOpcode())
		{
		case Instruction::Br:		
			log() << "find br instruction\n";

			// 判断当前bb属于哪个控制流
			if (BBName.contains("for.cond")) {

				endBB = dyn_cast<BasicBlock>(backInstr.getOperand(1)); // 注意 operand 1为for.end
				cfgVec.emplace_back(BB, endBB);  	
				BB = SplitBasicBlockByTerminatorCond(endBB, "for.end.split");
			} else if (BBName.contains("while.cond")) {

				endBB = dyn_cast<BasicBlock>(backInstr.getOperand(1)); // 注意 operand 1为for.end
				cfgVec.emplace_back(BB, endBB);  	
				BB = SplitBasicBlockByTerminatorCond(endBB, "while.end.split");
			
			} else if (BBName.contains("do.body")){
				// 寻找do.cond, 进而找到do.end	
				for(auto it = pred_begin(BB), et = pred_end(BB); it != et; ++it) {
					BasicBlock *predecessorBB = *it;
					if ((*predecessorBB).getName().contains("do.cond")) {
						endBB = dyn_cast<BasicBlock>((*predecessorBB).back().getOperand(1));	
						cfgVec.emplace_back(BB, endBB);	
						break;
					}
				}
				BB = SplitBasicBlockByTerminatorCond(endBB, "do.end.split");
			}

			// 处理直接跳转
			else if (backInstr.getNumOperands() == 1)  {
				cfgVec.emplace_back(BB);
				BB = dyn_cast<BasicBlock>(backInstr.getOperand(0));
			} else {
			// 处理if.then else	
				endBB = getTargetMergeBB(BB, "if.end");
				cfgVec.emplace_back(BB, endBB);
				BB = SplitBasicBlockByTerminatorCond(endBB, "if.end.split");
			}
			break;

		case Instruction::Switch:	
			log() << "find switch instruction\n";

			endBB = getTargetMergeBB(BB, "sw.epilog"); // POINT: 传入的要准确, 应该为sw.epilog+number
			cfgVec.emplace_back(BB, endBB);
			BB = SplitBasicBlockByTerminatorCond(endBB, "sw.epilog.split");
			break;

		case Instruction::Ret:
			log() << "find ret instruction\n";
			cfgVec.emplace_back(BB);
			retFlag = 1;	
			break;

		default:
			errs() << "come default branch. error\n";
			endBB = BB;	
		}
	}
}

static void genWhileSwitchStructure(Function &F, size_t caseNumber, SwitchInst **swINC, BasicBlock **obfENTRYBB, BasicBlock **swEPIBB, BasicBlock **whileENDBB)
{
	log() << "即将产生while-switch框架" << "\n";
	// 初始化Builder
	LLVMContext &Context = F.getContext();
	IRBuilder<> Builder(Context);

	// 1. 创建obf.entry
	BasicBlock *obfEntry = BasicBlock::Create(Context, "obf.entry");
	F.getBasicBlockList().push_back(obfEntry);
	Builder.SetInsertPoint(obfEntry);
	auto *swVar = Builder.CreateAlloca(Type::getInt32Ty(Context), nullptr, "swVar");
	auto *terminateNumber= Builder.CreateAlloca(Type::getInt32Ty(Context), nullptr, "terminateNumber");
	//auto *caseNum = ConstantInt::get(Type::getInt32Ty(Context), caseNumber);
	auto *termNum = ConstantInt::get(Type::getInt32Ty(Context), caseNumber * 2 -1);
	Builder.CreateAlignedStore(ConstantInt::get(Type::getInt32Ty(Context), 1), swVar, 4, false);
	Builder.CreateAlignedStore(termNum, terminateNumber, 4, false);
	
	// Set Callee Argu
	*obfENTRYBB = obfEntry;


	// 2. 创建obf.switch.default 和 obf.switch.epilog, 并设置 default br epilog
	BasicBlock *obfSWDefault = BasicBlock::Create(Context, "obf.sw.default");
	F.getBasicBlockList().push_back(obfSWDefault);
	BasicBlock *obfSWEpilog = BasicBlock::Create(Context, "obf.sw.epilog");
	F.getBasicBlockList().push_back(obfSWEpilog);
	Builder.SetInsertPoint(obfSWDefault);
	Builder.CreateBr(obfSWEpilog);

	// set Callee Argu
	*swEPIBB = obfSWEpilog;	

	// 3. 创建obf.while.body obf.while.end
	BasicBlock *obfWhileBody = BasicBlock::Create(Context, "obf.while.body");
	BasicBlock *obfWhileEnd = BasicBlock::Create(Context, "obf.while.end");
	F.getBasicBlockList().push_back(obfWhileBody);
	F.getBasicBlockList().push_back(obfWhileEnd);
	Builder.SetInsertPoint(obfWhileBody);
	auto *swV1 = Builder.CreateAlignedLoad(swVar, 4);

	// set Callee Argu
	*whileENDBB = obfWhileEnd;	

	// 4. obf.entry设置跳转指令
	Builder.SetInsertPoint(obfEntry);
	Builder.CreateBr(obfWhileBody);

	// 5. 创建sw跳转
	Builder.SetInsertPoint(obfWhileBody);
	// setCalleeArgu
	*swINC = Builder.CreateSwitch(swV1, obfSWDefault, caseNumber*2);

	// 6. 设置obf.sw.epilog
	Builder.SetInsertPoint(obfSWEpilog);
	auto *swV2 = Builder.CreateAlignedLoad(swVar, 4);
	auto *swAdd1 = Builder.CreateAdd(swV2, ConstantInt::get(Type::getInt32Ty(Context), 2));
	Builder.CreateStore(swAdd1, swVar, false);

	// 6.2 创建循环终止条件
	auto *swV3 = Builder.CreateAlignedLoad(swVar, 4);
	auto *termV1 = Builder.CreateAlignedLoad(terminateNumber, 4);
	auto *cmpV1 = Builder.CreateICmpUGT(swV3, termV1);

	BasicBlock *obfIfThen = BasicBlock::Create(Context, "obf.if.then");
	BasicBlock *obfIfEnd  = BasicBlock::Create(Context, "obf.if.end");
	F.getBasicBlockList().push_back(obfIfThen);
	F.getBasicBlockList().push_back(obfIfEnd);

	Builder.SetInsertPoint(obfIfThen);
	Builder.CreateBr(obfWhileEnd);

	Builder.SetInsertPoint(obfIfEnd);
	Builder.CreateBr(obfWhileBody);

	Builder.SetInsertPoint(obfSWEpilog);
	Builder.CreateCondBr(cmpV1, obfIfThen, obfIfEnd);


	log() << "while-switch框架已经产生" << "\n";
}

static void InsertCase(Function &F, SwitchInst *swInc, BasicBlock *obfENTRYBB, BasicBlock *swEPIBB, BasicBlock *whileENDBB, std::vector<CFGNode> &cfgVec) 
{
	LLVMContext &Context = F.getContext();
	IRBuilder<> Builder(Context);

	auto &entry = cfgVec.front();
	auto &ret   = cfgVec.back();
	// 1. 更改entry
	entry.getBeginBB()->back().eraseFromParent();  // 删除原始的br指令
	Builder.SetInsertPoint(entry.getBeginBB());
	Builder.CreateBr(obfENTRYBB);                  // 创建 br obfENTRYBB 指令

	// 2. 插入真实控制流
	for(unsigned i = 1; i < cfgVec.size(); i++)
	{
		swInc->addCase(ConstantInt::get(Type::getInt32Ty(Context), i*2-1), cfgVec[i].getBeginBB());   // case分支指向真实控制流
		if (cfgVec[i].getEndBB()->back().getOpcode() == Instruction::Br) {
			cfgVec[i].getEndBB()->back().eraseFromParent();  // 删除最后控制流的跳转指令
			Builder.SetInsertPoint(cfgVec[i].getEndBB());
			Builder.CreateBr(swEPIBB);
		}
	}


	// 3. 插入虚假控制流
	for(unsigned i = 1; i < cfgVec.size(); i++)
	{
		BasicBlock *obfCase = weakOpaqueCodegen(F, swEPIBB, nullptr, "def.obf.weakobque");	
		swInc->addCase(ConstantInt::get(Type::getInt32Ty(Context), i*2), obfCase);	
	}

	// 4. 创建while.end返回值
	Builder.SetInsertPoint(whileENDBB);
	//Builder.CreateRet(ret.getEndBB()->back().getOperand(0));
	if(ret.getEndBB()->back().getNumOperands() == 1)	
		Builder.CreateRet(ConstantInt::get(Type::getInt32Ty(Context), 0)); // 自行构造返回值
	else {
		log() << "原始函数没有返回值\n"; 
		Builder.CreateRetVoid();
	}
}

static void handle_main(Function &F)
{
	log() << "welcome to handle_main" << "\n";


	std::vector<CFGNode> cfgVec;
	// 1. 预处理, 构建F的CFG节点
	GenOutLineCFG(F, cfgVec);

	log() << "拆分后的模块数量为: " << cfgVec.size() << "\n";

	SwitchInst *swInc;
	BasicBlock *obfENTRYBB, *swEPIBB, *whileENDBB;
	// 2. 构建while-switch结构
 	genWhileSwitchStructure(F, cfgVec.size(), &swInc, &obfENTRYBB, &swEPIBB, &whileENDBB);

	log() << *swInc << "\n" << *swEPIBB << "\n" << *whileENDBB << "\n";

	// 3. 向while-switch结构中插入case
	InsertCase(F, swInc, obfENTRYBB, swEPIBB, whileENDBB, cfgVec);

}


