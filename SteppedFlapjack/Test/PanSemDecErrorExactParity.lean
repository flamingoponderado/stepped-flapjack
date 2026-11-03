import Flapjack.Pancake.Semantics.PanSemStateEval
import SteppedFlapjack.Test.PanValueFfiSemantics

/-!
The non-clocked evaluator rejects the `Dec` failures of
`Flapjack.Test.PanSemDecErrorExactParity` with `Error`.
Split from that module (flapjack#1251), with copies of the fixtures it
uses, so that this package does not import Flapjack's tests.
-/

namespace Flapjack.Test.PanSemDecErrorExactParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

/-- Source memory with a present word cell at address `8` and a zero fallback. -/
private def exactMemory : Word64 → Option (PanValue Word64) :=
  fun address =>
    if address == 8 then some (.word (BitVec.ofNat 64 0x77)) else some (.word 0)

/-- Access whose `memaddrs`-style domain is empty, so every read misses. -/
private def emptyAccess : PanValueMemoryAccess Word64 :=
  panValueMemoryAccessOfModel panSemBitVec64WordModel (fun _ => false)
    (fun _ => false) false

private def localsWithX : VarName → Option (PanValue Word64) :=
  fun name => if name == "x" then some (.word 3) else none

private def decEvalFailProgram : Prog Word64 :=
  .dec "d" Shape.one (.load Shape.one (.const 11)) .skip

private def decShapeMismatchProgram : Prog Word64 :=
  .dec "d" (Shape.named "Other") (.const 7) .skip

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
