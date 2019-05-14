#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/Transforms/Obfuscation/OpaquePredicate.h"
#include "llvm/Transforms/Obfuscation/RedundancyObfuscator.h"
#include "llvm/Pass.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/User.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;


#define DEBUG 

#ifdef DEBUG

#else

#define outs() nulls()

#endif

void ObfSingleBasicBlock(Function &F);
void ObfForControlFlow(Function &F);

namespace {

	struct RedundancyObfuscator : public FunctionPass {
		static char ID;
		bool flag;

		RedundancyObfuscator() : FunctionPass(ID){}			
		RedundancyObfuscator(bool flag) : FunctionPass(ID){ this->flag = flag; }			
	
		bool runOnFunction(Function &F) override {

			//outs() << "welcome to RedundancyObfuscator Pass runOnFunction\n";
		
			if (flag == false)
				return false;

			outs() << "enable RedundancyObfuscator\n";

			// 1. 处理循环基本块
			ObfForControlFlow(F);
		
			// 2. 处理基本块--基本块混淆
			ObfSingleBasicBlock(F);
		
			return true;
		}	
	};
}

char RedundancyObfuscator::ID = 0;
static RegisterPass<RedundancyObfuscator> X("RedundancyObfuscator", "RedundancyObfuscator Pass");

Pass *llvm::createRedundancyObf(bool flag) { return new RedundancyObfuscator(flag); }

void ObfSingleBasicBlock(Function &F)
{
	LLVMContext &TheContext = F.getContext();
	IRBuilder<> Builder(TheContext);

	outs() << "即将处理single基本块\n";

	// 一、当前函数末尾创建不透明谓词基本块
	//BasicBlock *singleObfBB = weakOpaqueCodegen(F);
	// 二、遍历全部基本块, 以基本块为单位处理
	for(auto &bb : F) {

		//outs() << "has " << bb.size() << " instructions" << "\n";

		if (bb.getName().contains("obf") || bb.getName().contains("split") || bb.size() < 2) {
			//outs() << "continue!" << "\n";
			continue;
		}

		// 只针对最后一条指令是直接br or ret的BasicBlock
		if (bb.back().getOpcode() != Instruction::Br && bb.back().getOpcode() != Instruction::Ret)
			continue;

		//outs() << "number Operands(): " << bb.back().getNumOperands() << "\n";

		if (bb.back().getOpcode() == Instruction::Br && bb.back().getNumOperands() > 1)
			continue;

		BasicBlock *jumpBB = nullptr;

		if (bb.back().getOpcode() == Instruction::Br) {
			jumpBB = dyn_cast<BasicBlock>(bb.back().getOperand(0));	
			outs() << "BB Name: " << bb.getName() << "\t jumpBB Name: " << jumpBB->getName() << "\n";
		}

		if (jumpBB && jumpBB->getName().contains("split"))   // 即该basicBlock已经被拆分过
			continue;

		if (jumpBB && jumpBB->getName().contains("obf.entry"))   // 如果跳转的bb是我们的构造的flat主bb, 则不处理
			continue;

		outs() << "BB " << bb.getName() << " 即将拆分\n";

		// 1. 拆分基本块(由于涉及拆分指令, 所以我们只处理包含指令个数>=2的基本块)
		//BasicBlock::iterator iter = bb.begin();
		Instruction &backInstr = bb.back();

		//size_t indexI = bb.size() / 2;
		//for(size_t i = 0; i < indexI; i++)
			//iter++;

		BasicBlock *sp2 = bb.splitBasicBlock(&backInstr, "single.split.BB"); // POINT: 如何正确的分割?

		Instruction &modI = sp2->getUniquePredecessor()->back();
		Builder.SetInsertPoint(&modI);  // 顺便设置插入点
		//outs() << (sp2->getUniquePredecessor()->back()) << "\n";


		// 2. 创建singleObfBB.
		BasicBlock *singleObfBB = weakOpaqueCodegen(F, sp2, &(F.back()), "single.obf");


		// 3. 插入跳转指令
	 	Builder.CreateBr(singleObfBB);
		modI.eraseFromParent();
	
	}	

}

// 注意: 测试时不要开启mem2reg, 因为涉及phi指令(phi指令难以处理和修改和跳转)
void ObfForControlFlow(Function &F)
{
	LLVMContext &TheContext = F.getContext();
	IRBuilder<> Builder(TheContext);

	outs() << "即将处理for循环基本块\n";

	for (auto iter = F.begin(); iter != F.end(); iter++) 
	{
		BasicBlock &bb = *iter;

		outs() << "bb Name: " << bb.getName() << "\n";

		// 排除掉我们插入的obf BasicBlock.
		if (bb.getName().contains("obf") || bb.getName().contains("split"))
			continue;

		if (bb.back().getOpcode() == Instruction::Br && bb.back().getNumOperands() == 1) {
			outs() << "find it" << "\n";	
			// 1. 得到它jump的BasicBlock.
			BasicBlock *condBB = dyn_cast<BasicBlock>(bb.back().getOperand(0));


			outs() << "jumpBB Name: " << condBB->getName() << "\n";

			// core
			// jumpBB包含for.cond,但是不包含split(排除我们新建的BB)
			if (condBB->getName().contains("for.cond") && !condBB->getName().contains("split") && !bb.getName().contains("for.inc")) {
				// 现在已经获得了for.cond基本块和它的直接br基本块

				//outs() << "1 predecessor: " << condBB->hasNPredecessors(1) << "\n";
				//outs() << "2 predecessor: " << condBB->hasNPredecessors(2) << "\n";
				
				// 2. 获取for.cond的另一个前节点
				bb.back().eraseFromParent();
				//outs() << "1 predecessor: " << condBB->hasNPredecessors(1) << "\n";
				//outs() << "2 predecessor: " << condBB->hasNPredecessors(2) << "\n";
				auto precessorBB = pred_begin(condBB);
				BasicBlock *preCondInForBB = *precessorBB;
				Builder.SetInsertPoint(&bb);
				Builder.CreateBr(condBB);

				outs() << *preCondInForBB << "\n";

				outs() << "ready handling" << "\n";

				// 3. 拆分BB.
				
				if (bb.canSplitPredecessors()) {
					BasicBlock *splitCondPreBB = SplitBasicBlockByTerminatorCond(&bb, "for.cond.pre.split.BB");

					// 4. 新建 for.obf.P
					BasicBlock *obfPBB = weakOpaqueCodegen(F, splitCondPreBB, condBB, "for.obf.P");

					// 5. 跳转到for.obf.P
					bb.back().eraseFromParent();
					Builder.SetInsertPoint(&bb);
					Builder.CreateBr(obfPBB);

					// 6. 新建 for.obf.Q
					BasicBlock *obfQBB = weakOpaqueCodegen(F, condBB, splitCondPreBB, "for.obf.Q");

					// 7. 更改preCondInForBB的最后一条跳转指令, 跳转到obfQBB;
					(*preCondInForBB).back().eraseFromParent();
					Builder.SetInsertPoint(preCondInForBB);
					Builder.CreateBr(obfQBB);

				}

			
			}
		
		}
	
	}

	/*
	for (auto &bb : F) {
	
		// 判断当前BasicBlock的名字是否是for.cond
	
		outs() << "bb Name: " << bb.getName() << "\n";

		if (bb.getName().contains("for.cond")) {
			outs() << "find for.cond!" << "\n";

			// method 1: 找到前面predecessor   放弃
			//BasicBlock *predecessorBB = bb.getSinglePredecessor();

			//outs() << predecessorBB << "\n";

			//if (!predecessorBB)
				//continue;

			//outs() << "predecessorBB Name: " << predecessorBB->getName() << "\n";

			// method 2: 拆分for.cond基本块, 最后一条跳转指令单独一个BasicBlock 
			bb.splitBasicBlock(&(bb.back()), "for.split");
	
		}
	}
	*/

}

