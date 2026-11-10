import SteppedFlapjack.Concrete.TwoProgramNativeEntry
import SteppedFlapjack.PanToCrepSteps.FullInitAssignLoopInputs
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.Concrete SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.PanToCrepSteps
open SteppedFlapjack.WordToStackSteps
namespace SteppedFlapjack.Concrete

/-- The zero-argument scalar entry meets the existing full-initialization
machine theorem's frame condition for every initial Stack space. -/
theorem twoProgram_assignLoopFrameFits {F : Type}
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture) (name callee : MlString)
    (body : CrepProgHOL 64) (fresh : name ≠ callee) (shape : ScalarProgram body)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    assignLoopFrameFits arch (twoPrograms name callee body)
      countdownRiscVBackend.wordToWordConf riscvConfig branchingLoopEntry stack := by
  change nativeEntryFrameSize (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length))
    (nativeTailEntryCode countdownRiscVBackend.wordToWordConf riscvConfig
      (loopToWordCompileHOL (compileProgHOLExact arch (twoPrograms name callee body))) 64
      (loopToWordCompFuncHOL 64 [] branchingLoopEntry)) ≤ stack.stackSpace
  rw [twoProgram_selectedEntry arch name callee body fresh shape]
  have zero : nativeEntryFrameSize (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) countdownOptimizedEntry = 0 := by
    with_unfolding_all rfl
  rw [zero]
  omega
end SteppedFlapjack.Concrete
