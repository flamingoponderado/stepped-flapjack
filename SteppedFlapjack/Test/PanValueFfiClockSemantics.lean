import Flapjack.PanValueFfiClockSemantics
import SteppedFlapjack.PanValueFfiClockProjection
import SteppedFlapjack.Test.PanValueFfiSemantics

/-!
Clocked results compared with the stepped evaluator and projected to stepped
results, on the programs of `Flapjack.Test.PanValueFfiClockSemantics`.
Split from that module (flapjack#1251), with copies of the fixtures it
uses, so that this package does not import Flapjack's tests.
-/

namespace Flapjack

open RiscV

def clockedTickAtZero :
    Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [] 0 100 8 20 (fun _ => none) (fun _ => none)
    (fun _ => none) statefulTestFfiState 0 .tick

def clockedTickAtOne :
    Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [] 0 100 8 20 (fun _ => none) (fun _ => none)
    (fun _ => none) statefulTestFfiState 1 .tick

def clockedFinalFfi : Option (PanValueFfiClockResult (Word 64) Unit) :=
  evalPanValueFfiClockProg statefulTestContext statefulTestPrimitive
    statefulTestHandler [] [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
    (BitVec.ofNat 64 8) 10 (fun _ => none) (fun _ => none) (fun _ => none)
    statefulTestFinalState 10
    ((.dec "x" .one (.const (BitVec.ofNat 64 0))
      (.shMemLoad .op8 .local "x" (.const (BitVec.ofNat 64 10)))) : Prog (Word 64))

def clockedCallFinalFfiFunctions : List (FunName × List VarName × Prog (Word 64)) :=
  [("finalExt", [],
    .extCall "final" (.const (BitVec.ofNat 64 8))
      (.const (BitVec.ofNat 64 1)) (.const (BitVec.ofNat 64 8))
      (.const (BitVec.ofNat 64 1)))]

def clockedCallFinalFfiSteps : Option (PanValueFfiSteppedResult (Word 64) Unit) :=
  evalPanValueFfiCallSteps statefulTestContext statefulTestPrimitive
    statefulTestHandler [] clockedCallFinalFfiFunctions
    (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8)
    10 (fun _ => none) (fun _ => none) statefulTestMemory
    statefulTestFinalState none "finalExt" []
    (memoryAccess := some (panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel))

#guard
  match clockedCallFinalFfiSteps with
  | some (.finalFfi locals _ _ _ event, _) =>
      locals "x" = none && event.name = .extCall "final" &&
        event.outcome = .failed
  | _ => false

/- The named result projection keeps the exact source state and remaining
   clock while making timeout and terminal FFI outcomes distinct. -/
#guard
  match clockedTickAtZero.map panValueFfiClockResultProjection with
  | some (.timeout locals globals memory ffi 0) =>
      locals "x" = none && globals "x" = none && memory (BitVec.ofNat 64 0) = none &&
        ffi.state = ()
  | _ => false

#guard
  match clockedTickAtOne.map panValueFfiClockResultProjection with
  | some (.normal locals globals memory ffi 0) =>
      locals "x" = none && globals "x" = none && memory (BitVec.ofNat 64 0) = none &&
        ffi.state = ()
  | _ => false

#guard
  match clockedFinalFfi.map panValueFfiClockResultProjection with
  | some (.finalFfi locals globals memory ffi event 10) =>
      locals "x" = none && globals "x" = none && memory (BitVec.ofNat 64 0) = none &&
        ffi.state = () && event.name = .sharedMem .mappedRead &&
        event.outcome = .failed
  | _ => false

end Flapjack
