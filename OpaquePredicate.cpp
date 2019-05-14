#include "llvm/Transforms/Obfuscation/OpaquePredicate.h"
#include "llvm/Transforms/Obfuscation/Utils.h"

using namespace llvm;

BasicBlock* llvm::weakOpaqueCodegen(Function &F, BasicBlock *B1, BasicBlock *B2, const char *bbName)
{

	LLVMContext &TheContext= F.getContext(); 
	
	// 0. 创建基本块. 存放我们的weak obaque predicate
	BasicBlock *IfObfBB = BasicBlock::Create(TheContext, bbName);
	//BasicBlock *IfObfBB = BasicBlock::Create(TheContext);
	F.getBasicBlockList().push_back(IfObfBB);
	IRBuilder<> Builder(TheContext);
	Builder.SetInsertPoint(IfObfBB);		

	// 1. 产生随机数, max = 不透明谓词的个数 
	uint32_t rNumber= 1 + rand() % 4;
	auto *rn = ConstantInt::get(Type::getInt32Ty(TheContext), rand() % 512 + 1);
	// 2. 将自变量x压入栈中, 命名为condX
	auto *condX = Builder.CreateAlloca(Type::getInt32Ty(F.getContext()), nullptr, "numberX");
	Builder.CreateStore(rn, condX, false);
	Builder.CreateAlignedLoad(condX, 4);

	// 3. 随机对各个函数产生不透明谓词
	Value *result = nullptr;
	switch (rNumber) {
		case 1:
			// x*(x+1)%2;
			{
				auto *n1 = Builder.CreateLoad(condX);
				auto *n2 = Builder.CreateLoad(condX);
				auto *add = Builder.CreateAdd(n2, ConstantInt::get(Type::getInt32Ty(TheContext), 1));
				auto *mul = Builder.CreateMul(n1, add);
				auto *rem = Builder.CreateURem(mul, ConstantInt::get(Type::getInt32Ty(TheContext), 2));
				result = rem;
			}
			break;
		case 2:
			// x*(x+1)*(x+2)%3;
			{
				auto *n1 = Builder.CreateLoad(condX);
				auto *n2 = Builder.CreateLoad(condX);
				auto *add1 = Builder.CreateAdd(n2, ConstantInt::get(Type::getInt32Ty(TheContext), 1));
				auto *mul1 = Builder.CreateMul(n1, add1);
				auto *n3 = Builder.CreateLoad(condX);
				auto *add2 = Builder.CreateAdd(n3, ConstantInt::get(Type::getInt32Ty(TheContext), 2));
				auto *mul2 = Builder.CreateMul(mul1, add2);
				auto *rem = Builder.CreateURem(mul2, ConstantInt::get(Type::getInt32Ty(TheContext), 3));
				result = rem;
			}
			
			break;
		case 3:
			// x*x*(x+1)*(x+1) % 4;
			{
				auto *n1 = Builder.CreateLoad(condX);
				auto *n2 = Builder.CreateLoad(condX);
				auto *mul1 = Builder.CreateMul(n1, n2);
				auto *n3 = Builder.CreateLoad(condX);
				auto *add1 = Builder.CreateAdd(n3, ConstantInt::get(Type::getInt32Ty(TheContext), 1));
				auto *mul2 = Builder.CreateMul(mul1, add1);
				auto *n4 = Builder.CreateLoad(condX);
				auto *add2 = Builder.CreateAdd(n4, ConstantInt::get(Type::getInt32Ty(TheContext), 1));
				auto *mul3 = Builder.CreateMul(mul2, add2);
				auto *rem = Builder.CreateURem(mul3, ConstantInt::get(Type::getInt32Ty(TheContext), 4));
				result = rem;
			}

			break;
		case 4:
			// (4*x*x + 4) % 19;
			{
				auto *n1 = Builder.CreateLoad(condX);
				auto *mul1 = Builder.CreateMul(n1, ConstantInt::get(Type::getInt32Ty(TheContext), 4));
				auto *n2 = Builder.CreateLoad(condX);
				auto *mul2 = Builder.CreateMul(mul1, n2);
				auto *add = Builder.CreateAdd(mul2, ConstantInt::get(Type::getInt32Ty(TheContext), 4));
				auto *rem = Builder.CreateURem(add, ConstantInt::get(Type::getInt32Ty(TheContext), 19));
				result = rem;
			}

			break;
		default:
			errs() << "gen weak obaque error!" << "\n";
	}

	if (B1 && B2) {
		auto *Cond = Builder.CreateICmpEQ(result, ConstantInt::get(Type::getInt32Ty(TheContext), 0));
		Builder.CreateCondBr(Cond, B1, B2);
	}else if (B1) {
		Builder.CreateBr(B1);		
	}else if (B2){
		Builder.CreateBr(B2);	
	} else {
		//Builder.CreateBr(B1);
		//Builder.CreateRet(ConstantInt::get(Type::getInt32Ty(TheContext), 0)); // debug用
		//return IfObfBB;
		Builder.CreateRetVoid();
	}
	return IfObfBB;
}
