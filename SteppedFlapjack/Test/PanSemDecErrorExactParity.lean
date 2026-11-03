import Flapjack.Test.PanSemDecErrorExactParity
import SteppedFlapjack.PanValueFfiSemantics

/-!
The non-clocked evaluator rejects the `Dec` failures of
`Flapjack.Test.PanSemDecErrorExactParity` with `Error`.
Moved from flapjack with the stepped semantics (flapjack#1251).
-/

namespace Flapjack.Test.PanSemDecErrorExactParity

open Flapjack
open Flapjack.RiscV

private def nonClockedEvaluate (program : Prog Word64)
    (memoryAccess : Option (PanValueMemoryAccess Word64) := none) :
    Option (PanValueFfiSteppedResult Word64 Unit) :=
  evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [] 0 100 (BitVec.ofNat 64 8) 5 localsWithX
    (fun _ => none) exactMemory statefulTestFfiState program
    (memoryAccess := memoryAccess)

/-- A stepped `Error` that keeps local `x` at `localValue`. -/
private def isErrorKeepingStepped (localValue : Nat)
    (result : Option (PanValueFfiSteppedResult Word64 Unit)) : Bool :=
  match result with
  | some (.error locals _ _ _, _) =>
      (match locals "x" with
       | some (.word value) => value == BitVec.ofNat 64 localValue
       | _ => false)
  | _ => false

private def decNonClockedEvalFailGuard : Bool :=
  isErrorKeepingStepped 3 (nonClockedEvaluate decEvalFailProgram (some emptyAccess))

private def decNonClockedShapeMismatchGuard : Bool :=
  isErrorKeepingStepped 3 (nonClockedEvaluate decShapeMismatchProgram)

#guard decNonClockedEvalFailGuard
#guard decNonClockedShapeMismatchGuard

end Flapjack.Test.PanSemDecErrorExactParity
