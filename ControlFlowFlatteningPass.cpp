#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Plugins/PassPlugin.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Local.h"

#include <vector>

#include "ChakravyuhaReport.h"
#include "EmitReportPass.h"
#include "FakeCodeInsertionPass.h"
#include "InitialIRMetricsPass.h"
#include "StringEncryptionPass.h"

using namespace llvm;

namespace {

static void demoteValuesToMemory(Function &F) {
  BasicBlock &Entry = F.getEntryBlock();
  IRBuilder<> AllocaBuilder(&Entry, Entry.getFirstInsertionPt());

  std::vector<PHINode *> PhisToRemove;
  for (BasicBlock &BB : F)
    for (Instruction &I : BB)
      if (auto *PN = dyn_cast<PHINode>(&I))
        PhisToRemove.push_back(PN);

  for (PHINode *PN : PhisToRemove) {
    AllocaInst *Alloca = AllocaBuilder.CreateAlloca(
        PN->getType(), nullptr, PN->getName() + ".phialloca");

    IRBuilder<> InitBuilder(Entry.getTerminator());
    InitBuilder.CreateStore(UndefValue::get(PN->getType()), Alloca);

    for (unsigned i = 0; i < PN->getNumIncomingValues(); ++i) {
      Value *IncomingVal = PN->getIncomingValue(i);
      BasicBlock *IncomingBB = PN->getIncomingBlock(i);
      IRBuilder<> StoreBuilder(IncomingBB->getTerminator());
      StoreBuilder.CreateStore(IncomingVal, Alloca);
    }

    std::vector<Use *> UsesToReplace;
    for (Use &U : PN->uses())
      UsesToReplace.push_back(&U);

    for (Use *U : UsesToReplace) {
      if (auto *UserInst = dyn_cast<Instruction>(U->getUser())) {
        IRBuilder<> LoadBuilder(PN->getParent(),
                                PN->getParent()->getFirstInsertionPt());
        LoadInst *Load = LoadBuilder.CreateLoad(PN->getType(), Alloca,
                                                PN->getName() + ".reload");
        U->set(Load);
      }
    }

    PN->eraseFromParent();
  }

  std::vector<Instruction *> ToDemote;
  for (BasicBlock &BB : F) {
    for (Instruction &I : BB) {
      if (I.isTerminator() || isa<AllocaInst>(I) || isa<PHINode>(I))
        continue;

      bool UsedOutside = false;
      for (User *U : I.users())
        if (auto *UI = dyn_cast<Instruction>(U))
          if (UI->getParent() != &BB) {
            UsedOutside = true;
            break;
          }

      if (UsedOutside)
        ToDemote.push_back(&I);
    }
  }

  for (Instruction *I : ToDemote) {
    AllocaInst *Alloca = AllocaBuilder.CreateAlloca(I->getType(), nullptr,
                                                    I->getName() + ".alloca");

    IRBuilder<> StoreBuilder(I);
    StoreBuilder.SetInsertPoint(I->getParent(), ++I->getIterator());
    StoreBuilder.CreateStore(I, Alloca);

    std::vector<Use *> UsesToReplace;
    for (Use &U : I->uses())
      UsesToReplace.push_back(&U);

    for (Use *U : UsesToReplace) {
      if (auto *UserInst = dyn_cast<Instruction>(U->getUser())) {
        if (auto *SI = dyn_cast<StoreInst>(UserInst))
          if (SI->getPointerOperand() == Alloca)
            continue;

        IRBuilder<> LoadBuilder(UserInst);
        LoadInst *Load = LoadBuilder.CreateLoad(I->getType(), Alloca,
                                                I->getName() + ".reload");
        U->set(Load);
      }
    }
  }
}

static Value *buildNextStateForTerm(IRBuilder<> &B, Instruction *T,
                                    DenseMap<BasicBlock *, unsigned> &Id,
                                    unsigned DefaultState = 0) {
  if (auto *Br = dyn_cast<BranchInst>(T)) {
    if (Br->isUnconditional()) {
      auto It = Id.find(Br->getSuccessor(0));
      if (It != Id.end())
        return B.getInt32(It->second);
      return nullptr;
    }

    auto It1 = Id.find(Br->getSuccessor(0));
    auto It2 = Id.find(Br->getSuccessor(1));

    if (It1 != Id.end() && It2 != Id.end()) {
      Value *TState = B.getInt32(It1->second);
      Value *FState = B.getInt32(It2->second);
      return B.CreateSelect(Br->getCondition(), TState, FState, "cff.next");
    }
    return nullptr;
  }

  if (auto *Sw = dyn_cast<SwitchInst>(T)) {
    bool HasFlattenedSuccessor = false;
    auto DefaultIt = Id.find(Sw->getDefaultDest());
    if (DefaultIt != Id.end())
      HasFlattenedSuccessor = true;

    for (auto &C : Sw->cases()) {
      if (Id.find(C.getCaseSuccessor()) != Id.end()) {
        HasFlattenedSuccessor = true;
        break;
      }
    }
    if (!HasFlattenedSuccessor)
      return nullptr;

    Value *Cond = Sw->getCondition();
    Value *NS = (DefaultIt != Id.end()) ? B.getInt32(DefaultIt->second)
                                        : B.getInt32(DefaultState);

    for (auto &C : Sw->cases()) {
      auto CaseIt = Id.find(C.getCaseSuccessor());
      if (CaseIt != Id.end()) {
        Value *Is = B.CreateICmpEQ(Cond, C.getCaseValue());
        Value *S = B.getInt32(CaseIt->second);
        NS = B.CreateSelect(Is, S, NS, "cff.case.select");
      }
    }
    return NS;
  }

  return nullptr;
}

static bool isSupportedTerminator(Instruction *T) {
  return isa<BranchInst>(T) || isa<SwitchInst>(T) || isa<ReturnInst>(T) ||
         isa<UnreachableInst>(T);
}

static bool hasUnsupportedControlFlow(Function &F) {
  for (BasicBlock &BB : F) {
    if (BB.isEHPad() || BB.isLandingPad())
      return true;
    Instruction *T = BB.getTerminator();
    if (!isSupportedTerminator(T))
      return true;
  }
  return false;
}

struct ControlFlowFlatteningPass
    : public PassInfoMixin<ControlFlowFlatteningPass> {
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM) {
    bool Changed = false;
    unsigned int flattenedFunctions = 0;
    unsigned int flattenedBlocks = 0;
    unsigned int skippedFunctions = 0;

    auto &R = chakravyuha::ReportData::get();
    R.enableControlFlowFlattening = true;
    R.passesRun.push_back("ControlFlowFlattening");

    for (Function &F : M) {
      if (F.isDeclaration() || F.isIntrinsic())
        continue;
      if (F.size() < 2)
        continue;

      if (chakravyuha::shouldSkipFunction(F) || hasUnsupportedControlFlow(F)) {
        skippedFunctions++;
        continue;
      }

      unsigned blocksBefore = F.size();
      if (flattenFunction(F)) {
        Changed = true;
        flattenedFunctions++;
        flattenedBlocks += blocksBefore - 1;
      }
    }

    R.flattenedFunctions += flattenedFunctions;
    R.flattenedBlocks += flattenedBlocks;
    R.skippedFunctions += skippedFunctions;

    if (Changed) {
      return PreservedAnalyses::none();
    }
    return PreservedAnalyses::all();
  }

private:
  bool flattenFunction(Function &F) {
    if (F.isDeclaration() || F.isIntrinsic() || F.size() < 2)
      return false;
    if (hasUnsupportedControlFlow(F) || chakravyuha::shouldSkipFunction(F))
      return false;

    LLVMContext &Ctx = F.getContext();
    demoteValuesToMemory(F);

    BasicBlock *Entry = &F.getEntryBlock();

    SmallVector<BasicBlock *, 32> OriginalBlocks;
    for (BasicBlock &BB : F)
      OriginalBlocks.push_back(&BB);

    DenseMap<BasicBlock *, unsigned> BlockId;
    SmallVector<BasicBlock *, 32> FlattenTargets;
    unsigned NextId = 1;

    for (BasicBlock *BB : OriginalBlocks) {
      if (BB == Entry)
        continue;
      BlockId[BB] = NextId++;
      FlattenTargets.push_back(BB);
    }

    if (FlattenTargets.empty())
      return false;

    IRBuilder<> EntryBuilder(Ctx);
    EntryBuilder.SetInsertPoint(Entry, Entry->getFirstInsertionPt());
    AllocaInst *StateVar =
        EntryBuilder.CreateAlloca(Type::getInt32Ty(Ctx), nullptr, "cff.state");

    BasicBlock *Dispatcher = BasicBlock::Create(Ctx, "cff.dispatch", &F);
    BasicBlock *DefaultBlock = BasicBlock::Create(Ctx, "cff.default", &F);
    IRBuilder<> DefaultBuilder(DefaultBlock);
    DefaultBuilder.CreateUnreachable();

    Instruction *EntryTerm = Entry->getTerminator();
    {
      IRBuilder<> InitBuilder(EntryTerm);
      if (auto *Br = dyn_cast<BranchInst>(EntryTerm)) {
        if (Br->isUnconditional()) {
          auto It = BlockId.find(Br->getSuccessor(0));
          if (It != BlockId.end()) {
            InitBuilder.CreateStore(InitBuilder.getInt32(It->second), StateVar);
          } else {
            return false;
          }
        } else {
          auto It1 = BlockId.find(Br->getSuccessor(0));
          auto It2 = BlockId.find(Br->getSuccessor(1));
          if (It1 != BlockId.end() && It2 != BlockId.end()) {
            Value *InitState = InitBuilder.CreateSelect(
                Br->getCondition(), InitBuilder.getInt32(It1->second),
                InitBuilder.getInt32(It2->second), "cff.init");
            InitBuilder.CreateStore(InitState, StateVar);
          } else {
            return false;
          }
        }
      } else {
        Value *InitialState =
            buildNextStateForTerm(InitBuilder, EntryTerm, BlockId);
        if (InitialState) {
          InitBuilder.CreateStore(InitialState, StateVar);
        } else {
          return false;
        }
      }
    }

    EntryTerm->eraseFromParent();
    IRBuilder<> NewEntryBuilder(Entry);
    NewEntryBuilder.CreateBr(Dispatcher);

    IRBuilder<> DispatchBuilder(Dispatcher);
    Value *CurrentState =
        DispatchBuilder.CreateLoad(Type::getInt32Ty(Ctx), StateVar, "cff.cur");
    SwitchInst *DispatchSwitch = DispatchBuilder.CreateSwitch(
        CurrentState, DefaultBlock, FlattenTargets.size());

    for (BasicBlock *BB : FlattenTargets)
      DispatchSwitch->addCase(DispatchBuilder.getInt32(BlockId[BB]), BB);

    for (BasicBlock *BB : FlattenTargets) {
      Instruction *Term = BB->getTerminator();

      if (isa<ReturnInst>(Term) || isa<UnreachableInst>(Term))
        continue;

      IRBuilder<> TermBuilder(Term);

      if (auto *Br = dyn_cast<BranchInst>(Term)) {
        if (Br->isUnconditional()) {
          auto It = BlockId.find(Br->getSuccessor(0));
          if (It != BlockId.end()) {
            TermBuilder.CreateStore(TermBuilder.getInt32(It->second), StateVar);
            TermBuilder.CreateBr(Dispatcher);
            Term->eraseFromParent();
          }
        } else {
          auto It1 = BlockId.find(Br->getSuccessor(0));
          auto It2 = BlockId.find(Br->getSuccessor(1));
          if (It1 != BlockId.end() && It2 != BlockId.end()) {
            Value *NextState = TermBuilder.CreateSelect(
                Br->getCondition(), TermBuilder.getInt32(It1->second),
                TermBuilder.getInt32(It2->second), "cff.next");
            TermBuilder.CreateStore(NextState, StateVar);
            TermBuilder.CreateBr(Dispatcher);
            Term->eraseFromParent();
          }
        }
      } else if (auto *Sw = dyn_cast<SwitchInst>(Term)) {
        Value *NextState = buildNextStateForTerm(TermBuilder, Term, BlockId);
        if (NextState) {
          TermBuilder.CreateStore(NextState, StateVar);
          TermBuilder.CreateBr(Dispatcher);
          Term->eraseFromParent();
        }
      }
    }

    removeUnreachableBlocks(F);
    return true;
  }
};

} // end anonymous namespace

extern "C" LLVM_ATTRIBUTE_WEAK PassPluginLibraryInfo llvmGetPassPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "ChakravyuhaPassesPlugin", "v0.3",
          [](PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, ModulePassManager &MPM,
                   ArrayRef<PassBuilder::PipelineElement>) {
                  if (Name == "chakravyuha-initial-metrics") {
                    MPM.addPass(InitialIRMetricsPass());
                    return true;
                  }
                  if (Name == "chakravyuha-control-flow-flatten") {
                    MPM.addPass(ControlFlowFlatteningPass());
                    return true;
                  }
                  if (Name == "chakravyuha-string-encrypt") {
                    MPM.addPass(StringEncryptionPass());
                    return true;
                  }
                  if (Name == "chakravyuha-emit-report") {
                    MPM.addPass(EmitChakravyuhaReportPass());
                    return true;
                  }
                  if (Name == "chakravyuha-fake-code-insertion") {
                    MPM.addPass(FakeCodeInsertionPass());
                    return true;
                  }
                  if (Name == "chakravyuha-all") {
                    MPM.addPass(InitialIRMetricsPass());
                    MPM.addPass(StringEncryptionPass());
                    MPM.addPass(ControlFlowFlatteningPass());
                    MPM.addPass(FakeCodeInsertionPass());
                    MPM.addPass(EmitChakravyuhaReportPass());
                    return true;
                  }
                  return false;
                });
          }};
}
