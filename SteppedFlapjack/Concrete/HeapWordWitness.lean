import SteppedFlapjack.Concrete.SourceState
import SteppedFlapjack.PanValueFfiSemantics
import Flapjack.Pancake.Semantics.CrepRuntimeTarget

/-! A concrete source witness for ordinary heap word stores and loads. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang SteppedFlapjack.PanToCrepSteps

/-- Store seven in the initialized heap and return the word read back. -/
def heapWordWitness : Prog (RiscV.Word 64) :=
  .seq (.store (.const 0xa1000100) (.const 7))
    (.return (.load .one (.const 0xa1000100)))

/-- The witness is representable by the compiler's byte-string source syntax. -/
theorem heapWordWitness_ranged : ProgByteRanged heapWordWitness := by
  simp [heapWordWitness,ProgByteRanged,ExpByteRanged,ShapeByteRanged]

/-- The selected word belongs to the ordinary heap and is beyond its headers. -/
theorem heapWordWitness_address : ordinaryAddress 0xa1000100 ∧ sourceBase + 40 ≤ (0xa1000100 : BitVec 64).toNat := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- On the init-e-shaped source memory the witness takes seven source steps,
returns seven, and updates exactly the selected word. -/
theorem heapWordWitness_run :
    evalPanValueFfiProgSteps (riscv64PanValueFfiContext (fun _ => false))
      (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) [] []
      sourceProduction.baseAddress sourceProduction.topAddress 8 10
      sourceProduction.locals sourceProduction.globals sourceProduction.memory sourceProduction.ffi heapWordWitness
      (memoryAccess := some (panSemBitVec64MemoryAccess sourceProduction)) (contracts := none) =
        some (.returned sourceProduction.locals sourceProduction.globals
          (updatePanValueMemory sourceProduction.memory 0xa1000100 (.word 7)) sourceProduction.ffi [.word 7], 7) := by
  with_unfolding_all rfl

end SteppedFlapjack.Concrete
