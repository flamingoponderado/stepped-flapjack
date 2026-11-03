import Flapjack.Test.PanMemoryModel
import SteppedFlapjack.PanSteppedSemantics

/-!
The stepped evaluator on the memory-model programs of `Flapjack.Test.PanMemoryModel`, including step counts.
Moved from flapjack with the stepped semantics (flapjack#1251).
-/

namespace Flapjack

def memoryModelSteppedStructuredFlatProgram : Bool :=
  match evalPanValueSteppedProg (α := RiscV.Word 64)
      (fun _ _ => none) (fun _ _ _ _ _ locals => some locals) [] []
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 20
      (fun _ => none) (fun _ => none) (fun _ => none)
      structuredFlatProgram
      (memoryAccess := some (panValueMemoryAccessOfModel memoryModel
        structuredFlatDomain)) with
  | some (.returned _ _ memory [.rStruct [.word left, .word right]], _) =>
      match memory (BitVec.ofNat 64 8), memory (BitVec.ofNat 64 16) with
      | some (.word storedLeft), some (.word storedRight) =>
          left == BitVec.ofNat 64 3 && right == BitVec.ofNat 64 5 &&
          storedLeft == BitVec.ofNat 64 3 && storedRight == BitVec.ofNat 64 5
      | _, _ => false
  | _ => false

#guard memoryModelSteppedStructuredFlatProgram

def memoryModelSteppedByteProgram : Option (RiscV.Word 64 × Nat) :=
  (evalPanValueSteppedProg (fun _ _ => none) (fun _ _ _ _ _ locals => some locals)
      [] [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 20
      (fun _ => none) (fun _ => none)
      (fun _ => some (.word 0))
      (.seq (.storeByte (.const (BitVec.ofNat 64 9))
          (.const (BitVec.ofNat 64 0xaa)))
        (.return (.loadByte (.const (BitVec.ofNat 64 9)))))
      (memoryAccess := some (panValueMemoryAccessOfModel memoryModel))).bind
    fun result => match result.1 with
      | .returned _ _ _ [.word value] => some (value, result.2)
      | _ => none

def memoryModelSteppedShared16Program : Option (RiscV.Word 64 × Nat) :=
  (evalPanValueSteppedProg (fun _ _ => none) (fun _ _ _ _ _ locals => some locals)
      [] [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 20
      (fun name => if name == "x" then some (.word 0) else none)
      (fun _ => none) (fun address => (memoryModelMemory address).map .word)
      (.seq (.shMemStore .op16 (.const (BitVec.ofNat 64 8))
          (.const (BitVec.ofNat 64 0xbeef)))
        (.seq (.shMemLoad .op16 .local "x" (.const (BitVec.ofNat 64 8)))
          (.return (.var .local "x"))))
      (memoryAccess := some (panValueMemoryAccessOfModel memoryModel))).bind
    fun result => match result.1 with
      | .returned _ _ _ [.word value] => some (value, result.2)
      | _ => none

def memoryModelSteppedSharedOutOfDomain : Option (RiscV.Word 64 × Nat) :=
  (evalPanValueSteppedProg (fun _ _ => none) (fun _ _ _ _ _ locals => some locals)
      [] [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 20
      (fun name => if name == "x" then some (.word 0) else none)
      (fun _ => none) (fun address => (memoryModelMemory address).map .word)
      (.shMemLoad .op8 .local "x" (.const (BitVec.ofNat 64 9)))
      (memoryAccess := some (panValueMemoryAccessOfModel memoryModel
        (domain := fun _ => true) (sharedDomain := fun _ => false)))).bind
    fun result => match result.1 with
      | .normal _ _ _ => some (BitVec.ofNat 64 0, result.2)
      | _ => none

def memoryModelSteppedVariadicAdd : Option (RiscV.Word 64 × Nat) :=
  (evalPanValueSteppedProg (fun _ _ => none) (fun _ _ _ _ _ locals => some locals)
      [] [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 20
      (fun _ => none) (fun _ => none) (fun _ => some (.word 0))
      (.return (.op .add [.const (BitVec.ofNat 64 1), .const (BitVec.ofNat 64 2),
        .const (BitVec.ofNat 64 3)]))
      (memoryAccess := some (panValueMemoryAccessOfModel memoryModel))).bind
    fun result => match result.1 with
      | .returned _ _ _ [.word value] => some (value, result.2)
      | _ => none

#guard memoryModelSteppedByteProgram = some (BitVec.ofNat 64 0xaa, 7)
#guard memoryModelSteppedShared16Program = some (BitVec.ofNat 64 0xbeef, 9)
#guard memoryModelSteppedSharedOutOfDomain = none
#guard memoryModelSteppedVariadicAdd = some (BitVec.ofNat 64 6, 5)

end Flapjack
