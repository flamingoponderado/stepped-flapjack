import Flapjack.Pancake.Semantics.PanSemStateEval
import SteppedFlapjack.Test.PanValueFfiSemantics

/-!
The non-clocked evaluator rejects the `If` failures of
`Flapjack.Test.PanSemIteErrorExactParity` with `Error`.
Split from that module (flapjack#1251), with copies of the fixtures it
uses, so that this package does not import Flapjack's tests.
-/

namespace Flapjack.Test.PanSemIteErrorExactParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

private def exactDomain (address : Word64) : Bool := address == 8

private def exactAccess : PanValueMemoryAccess Word64 :=
  panValueMemoryAccessOfModel panSemBitVec64WordModel exactDomain (fun _ => false) false

private def exactMemory : Word64 → Option (PanValue Word64) := fun _ => some (.word 0)

private def localsWordX : VarName → Option (PanValue Word64) :=
  fun name => if name == "x" then some (.word 3) else none

private def nonClockedEvaluate (program : Prog Word64)
    (memoryAccess : Option (PanValueMemoryAccess Word64) := none) :
    Option (PanValueFfiSteppedResult Word64 Unit) :=
  evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive statefulTestHandler
    [] [] 0 100 (BitVec.ofNat 64 8) 5 localsWordX (fun _ => none) exactMemory
    statefulTestFfiState program (memoryAccess := memoryAccess)

private def isWordOption (expected : Nat) : Option (PanValue Word64) → Bool
  | some (.word value) => value == BitVec.ofNat 64 expected
  | _ => false

private def isErrorKeepingXStepped (value : Nat)
    (result : Option (PanValueFfiSteppedResult Word64 Unit)) : Bool :=
  match result with
  | some (.error locals globals _ _, _) =>
      isWordOption value (locals "x") && (globals "g").isNone
  | _ => false

/-- A non-word condition value (`RStruct []`). -/
private def nonwordConditionProgram : Prog Word64 :=
  .ite (.rStruct []) .skip .skip

/-- A condition whose evaluation fails (unbound local `z`). -/
private def failedConditionProgram : Prog Word64 :=
  .ite (.var .local "z") .skip .skip

private def iteNonClockedNonwordGuard : Bool :=
  isErrorKeepingXStepped 3 (nonClockedEvaluate nonwordConditionProgram
    (memoryAccess := some exactAccess))

private def iteNonClockedFailedGuard : Bool :=
  isErrorKeepingXStepped 3 (nonClockedEvaluate failedConditionProgram
    (memoryAccess := some exactAccess))

#guard iteNonClockedNonwordGuard
#guard iteNonClockedFailedGuard

end Flapjack.Test.PanSemIteErrorExactParity
