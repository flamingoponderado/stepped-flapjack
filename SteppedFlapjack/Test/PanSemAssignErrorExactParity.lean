import Flapjack.Test.PanSemAssignErrorExactParity
import SteppedFlapjack.PanValueFfiSemantics

/-!
The non-clocked evaluator rejects the `Assign` failures of
`Flapjack.Test.PanSemAssignErrorExactParity` with `Error`.
Moved from flapjack with the stepped semantics (flapjack#1251).
-/

namespace Flapjack.Test.PanSemAssignErrorExactParity

open Flapjack
open Flapjack.RiscV

private def nonClockedEvaluate (program : Prog Word64)
    (memoryAccess : Option (PanValueMemoryAccess Word64) := none) :
    Option (PanValueFfiSteppedResult Word64 Unit) :=
  evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [] 0 100 (BitVec.ofNat 64 8) 5 localsWordX
    (fun _ => none) exactMemory statefulTestFfiState program
    (memoryAccess := memoryAccess)

private def isErrorSteppedKeepingX (value : Nat)
    (result : Option (PanValueFfiSteppedResult Word64 Unit)) : Bool :=
  match result with
  | some (.error locals globals _ _, _) =>
      (match locals "x" with
       | some (.word word) => word == BitVec.ofNat 64 value
       | _ => false) &&
        (globals "g").isNone
  | _ => false

private def assignNonClockedEvalFailGuard : Bool :=
  isErrorSteppedKeepingX 3 (nonClockedEvaluate assignLocalEvalFailProgram
    (memoryAccess := some exactAccess))

private def assignNonClockedInvalidGuard : Bool :=
  isErrorSteppedKeepingX 3 (nonClockedEvaluate assignFreshLocalProgram
    (memoryAccess := some exactAccess))

#guard assignNonClockedEvalFailGuard
#guard assignNonClockedInvalidGuard

end Flapjack.Test.PanSemAssignErrorExactParity
