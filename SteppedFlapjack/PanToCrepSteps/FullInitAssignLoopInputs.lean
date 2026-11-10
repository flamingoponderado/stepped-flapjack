import SteppedFlapjack.LoopToWordSteps.FullInitNativeSetup
import SteppedFlapjack.PanToCrepSteps.CountedAssignLoopNative

/-! Compiler-derived full-initialization bounds for source entries. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.LabToTargetSteps SteppedFlapjack.WordToStackSteps

/-- The compiled assignment-loop entry fits in the initial Stack space. -/
def assignLoopFrameFits {F : Type} (arch : AsmArchitecture)
    (crepPrograms : List (MlString × List Nat × CrepProgHOL 64))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (entry : HolLoopProg 64) (stack : StackSemStateFiniteExact 64 LabToTarget.Config F) : Prop :=
  nativeEntryFrameSize (ac.regCount-(5+ac.avoidRegs.length))
    (fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac
      ((firstLoopName,1,(LoopToWord.compHOL (assignLoopEntryWordContext entry) entry (firstLoopName,2)).1),
        entryColour wc (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms)) firstLoopName)).2.2 ≤ stack.stackSpace

/-- Shared actual compiler inputs with the full initialization machine context. -/
structure FullInitAssignLoopInputs {F : Type}
    (declarations : List (DeclHOL 64)) (start : MlString) (caller : PanToCrepContextExact 64)
    (loopCtxt : CrepToLoopContextExact) (entry : HolLoopProg 64) (limit : Nat)
    (loop : LoopSemStateFiniteExact 64 F)
    extends AssignLoopCompilerInputs declarations start caller loopCtxt entry limit loop where
  backend : FullInitMachineContext stack
  frameFits : assignLoopFrameFits arch crepPrograms wc ac entry stack

end SteppedFlapjack.PanToCrepSteps
