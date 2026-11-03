import Flapjack.Pancake.Semantics.PanSemStateEval
import SteppedFlapjack.Test.PanValueFfiSemantics

/-!
The non-clocked evaluator rejects the `Store` failures of
`Flapjack.Test.PanSemStoreErrorExactParity` with `Error`.
Split from that module (flapjack#1251), with copies of the fixtures it
uses, so that this package does not import Flapjack's tests.
-/

namespace Flapjack.Test.PanSemStoreErrorExactParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

private def exactDomain (address : Word64) : Bool := address == 8

/-- A memory access whose store never succeeds: the domain is empty. -/
private def emptyAccess : PanValueMemoryAccess Word64 :=
  panValueMemoryAccessOfModel panSemBitVec64WordModel (fun _ => false) (fun _ => false) false

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

private def storeAddressFailProgram : Prog Word64 :=
  .store (.var .local "z") (.const 7)

private def storeDomainFailProgram : Prog Word64 :=
  .store (.const 0) (.const 7)

private def storeNonClockedAddressFailGuard : Bool :=
  isErrorKeepingXStepped 3 (nonClockedEvaluate storeAddressFailProgram
    (memoryAccess := some (panValueMemoryAccessOfModel panSemBitVec64WordModel exactDomain
      (fun _ => false) false)))

private def storeNonClockedDomainFailGuard : Bool :=
  isErrorKeepingXStepped 3 (nonClockedEvaluate storeDomainFailProgram
    (memoryAccess := some emptyAccess))

#guard storeNonClockedAddressFailGuard
#guard storeNonClockedDomainFailGuard

end Flapjack.Test.PanSemStoreErrorExactParity
