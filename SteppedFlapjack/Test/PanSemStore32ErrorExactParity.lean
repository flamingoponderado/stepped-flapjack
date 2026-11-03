import Flapjack.Test.PanSemStore32ErrorExactParity
import SteppedFlapjack.PanValueFfiSemantics

/-!
The non-clocked evaluator rejects the `Store32`/`StoreByte` failures of
`Flapjack.Test.PanSemStore32ErrorExactParity` with `Error`.
Moved from flapjack with the stepped semantics (flapjack#1251).
-/

namespace Flapjack.Test.PanSemStore32ErrorExactParity

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

private def store32NonClockedAddressFailGuard : Bool :=
  isErrorKeepingXStepped 3 (nonClockedEvaluate store32AddressFailProgram
    (memoryAccess := some keywordAccess))

private def store32NonClockedDomainFailGuard : Bool :=
  isErrorKeepingXStepped 3 (nonClockedEvaluate store32DomainFailProgram
    (memoryAccess := some emptyAccess))

private def storeByteNonClockedAddressFailGuard : Bool :=
  isErrorKeepingXStepped 3 (nonClockedEvaluate storeByteAddressFailProgram
    (memoryAccess := some keywordAccess))

private def storeByteNonClockedDomainFailGuard : Bool :=
  isErrorKeepingXStepped 3 (nonClockedEvaluate storeByteDomainFailProgram
    (memoryAccess := some emptyAccess))

#guard store32NonClockedAddressFailGuard
#guard store32NonClockedDomainFailGuard
#guard storeByteNonClockedAddressFailGuard
#guard storeByteNonClockedDomainFailGuard

end Flapjack.Test.PanSemStore32ErrorExactParity
