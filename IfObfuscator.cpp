#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/Transforms/Obfuscation/OpaquePredicate.h"
#include "llvm/Transforms/Obfuscation/IfObfuscator.h"
#include "llvm/Pass.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/IR/User.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Constant.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Support/RandomNumberGenerator.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cstdlib>

using namespace llvm;


namespace {


	struct IfObfuscator : public FunctionPass {
		static char ID;

		bool flag;

		IfObfuscator() : FunctionPass(ID) {}

		IfObfuscator(bool flag) : FunctionPass(ID) { this->flag = flag; }

		bool runOnFunction(Function &F) override {

			//outs() << "runOnFunction" << "\n";

			if (flag == false)
				return false;

			outs() << "enable IfObfuscator\n";
			//outs() << "即将进行扩展判断条件混淆\n";

			IRBuilder<> Builder(F.getContext());
		
			for(BasicBlock &BB : F) {
				//outs() << BB.getName() << "\n";
			
				//outs() << "Basic block (name=" << BB.getName() << ") has"\
					" " << BB.size() << " instructions.\n";

				// 过滤掉我们的ifObf块
				if(BB.getName().contains("if.obf.lhs.true") || BB.getName().contains("obf"))
					continue;

				auto rbegin = BB.rbegin();   // 获取该BasicBlock的最后一条指令

				outs() << "rbegin OpcodeName: " << (*rbegin).getOpcodeName() << "\t"\
					"NumOperands: " << (*rbegin).getNumOperands() << "\n";

				// 修改条件跳转指令

	            if (!(StringRef((*rbegin).getOpcodeName()).compare("br")) && (*rbegin).getNumOperands() == 3) {

   				    outs() << "find cond br instruction, exec modify!" << "\n";
   
					// 1. 设置插入点
   				    Builder.SetInsertPoint(&(*rbegin));

					// 2. 插入跳转指令

					//Builder.CreateCondBr((*i).getOperand(0), static_cast<BasicBlock*>((*i).getOperand(2)), static_cast<BasicBlock*>((*i).getOperand(1)));

   				    BasicBlock *IfObfBB = weakOpaqueCodegen(F, dyn_cast<BasicBlock>((*rbegin).getOperand(2)), dyn_cast<BasicBlock>((*rbegin).getOperand(1)), "if.obf.lhs.true");
   				    // cond T:ifObf  F:if.else
                    Builder.CreateCondBr(rbegin->getOperand(0), IfObfBB, static_cast<BasicBlock*>(rbegin->getOperand(1)));
					// 3. 移除原始指令
   				    (*rbegin).eraseFromParent();
				}
		    }
			return true;
		}	

	};

}

char IfObfuscator::ID = 0;
static RegisterPass<IfObfuscator> X("IfObfuscator", "welcome to if obf pass");


Pass *llvm::createIfObfExtend(bool flag) { return new IfObfuscator(flag);}

