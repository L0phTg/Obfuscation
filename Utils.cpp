#include "llvm/Transforms/Obfuscation/Utils.h"

using namespace llvm;


// split包装函数: by alloca
BasicBlock* llvm::SplitBasicBlockByAlloca(BasicBlock *BB, const char *splitBBName)
{
	for(auto &instr : *BB)
		if (instr.getOpcode() != Instruction::Alloca)
			return BB->splitBasicBlock(&instr, splitBBName);
	return nullptr;
}

// split包装函数: by terminator, conditional
BasicBlock* llvm::SplitBasicBlockByTerminatorCond(BasicBlock *BB, const char *splitBBName)
{
	Instruction &instr = BB->back();	
	Instruction &frontInstr = BB->front();

	BasicBlock *splitBB = nullptr;

	if (instr.getOpcode() == Instruction::Br) {
		if (instr.getNumOperands() == 1)
			splitBB = BB->splitBasicBlock(&instr, splitBBName);
		else 
			splitBB = BB->splitBasicBlock(&frontInstr, splitBBName);
			//splitBB = BB->splitBasicBlock(dyn_cast<Instruction>(instr.getOperand(0)), splitBBName);
	
	}
	else if (instr.getOpcode() == Instruction::Ret) {           // POINT 未完成
		//splitBB = BB->splitBasicBlock(&instr, splitBBName);
		splitBB = BB->splitBasicBlock(&frontInstr, splitBBName);
	}
	else if (instr.getOpcode() == Instruction::Switch) {
		splitBB = BB->splitBasicBlock(&frontInstr, splitBBName);
		//splitBB = BB->splitBasicBlock(dyn_cast<Instruction>(instr.getOperand(0)), splitBBName);
	}
	
	return splitBB;
}

