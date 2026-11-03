import Flapjack.Test.PanSemIteErrorExactParity
import SteppedFlapjack.PanValueFfiSemantics

/-!
The non-clocked evaluator rejects the `If` failures of
`Flapjack.Test.PanSemIteErrorExactParity` with `Error`.
Moved from flapjack with the stepped semantics (flapjack#1251).
-/

namespace Flapjack.Test.PanSemIteErrorExactParity

open Flapjack
open Flapjack.RiscV

private def nonClockedEvaluate (program : Prog Word64)
    (memoryAccess : Option (PanValueMemoryAccess Word64) := none) :
    Option (PanValueFfiSteppedResult Word64 Unit) :=
  evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive statefulTestHandler
    [] [] 0 100 (BitVec.ofNat 64 8) 5 localsWordX (fun _ => none) exactMemory
    statefulTestFfiState program (memoryAccess := memoryAccess)

private def isErrorKeepingXStepped (value : Nat)
    (result : Option (PanValueFfiSteppedResult Word64 Unit)) : Bool :=
  match result with
  | some (.error locals globals _ _, _) =>
      isWordOption value (locals "x") && (globals "g").isNone
  | _ => false

private def iteNonClockedNonwordGuard : Bool :=
  isErrorKeepingXStepped 3 (nonClockedEvaluate nonwordConditionProgram
    (memoryAccess := some exactAccess))

private def iteNonClockedFailedGuard : Bool :=
  isErrorKeepingXStepped 3 (nonClockedEvaluate failedConditionProgram
    (memoryAccess := some exactAccess))

#guard iteNonClockedNonwordGuard
#guard iteNonClockedFailedGuard

end Flapjack.Test.PanSemIteErrorExactParity
