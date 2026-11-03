import Flapjack.Pancake.Semantics.PanSemStateEval
import SteppedFlapjack.Test.PanValueFfiSemantics

/-!
The non-clocked evaluator rejects the `Assign` failures of
`Flapjack.Test.PanSemAssignErrorExactParity` with `Error`.
Split from that module (flapjack#1251), with copies of the fixtures it
uses, so that this package does not import Flapjack's tests.
-/

namespace Flapjack.Test.PanSemAssignErrorExactParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

private def exactDomain : Word64 → Bool :=
  fun address => address == 8

private def exactAccess : PanValueMemoryAccess Word64 :=
  panValueMemoryAccessOfModel panSemBitVec64WordModel exactDomain
    (fun _ => false) false

private def exactMemory : Word64 → Option (PanValue Word64) :=
  fun _ => some (.word 0)

private def localsWordX : VarName → Option (PanValue Word64) :=
  fun name => if name == "x" then some (.word 3) else none

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

private def assignLocalEvalFailProgram : Prog Word64 :=
  .assign .local "x" (.var .local "z")

private def assignFreshLocalProgram : Prog Word64 :=
  .assign .local "y" (.const 9)

private def assignNonClockedEvalFailGuard : Bool :=
  isErrorSteppedKeepingX 3 (nonClockedEvaluate assignLocalEvalFailProgram
    (memoryAccess := some exactAccess))

private def assignNonClockedInvalidGuard : Bool :=
  isErrorSteppedKeepingX 3 (nonClockedEvaluate assignFreshLocalProgram
    (memoryAccess := some exactAccess))

#guard assignNonClockedEvalFailGuard
#guard assignNonClockedInvalidGuard

end Flapjack.Test.PanSemAssignErrorExactParity
