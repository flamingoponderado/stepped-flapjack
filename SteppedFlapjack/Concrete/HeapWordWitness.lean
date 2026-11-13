import SteppedFlapjack.Concrete.SourceState
import SteppedFlapjack.Concrete.CountedSource
import SteppedFlapjack.PanValueFfiSemantics
import SteppedFlapjack.PanToCrepSteps.CountedAssign
import Flapjack.Pancake.Semantics.CrepRuntimeTarget

/-! A concrete source witness for ordinary heap word stores and loads. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang SteppedFlapjack.PanToCrepSteps

/-- Read a word from ordinary heap memory. -/
def heapWordLoad : Prog (RiscV.Word 64) :=
  .return (.load .one (.const 0xa1000100))

/-- The load is accepted by the public source fragment. -/
theorem heapWordLoad_supported : ScalarSupported heapWordLoad := by
  refine ⟨.base (.ret (.load (.const _))), ?_⟩
  simp [heapWordLoad,ProgByteRanged,ExpByteRanged,ShapeByteRanged]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The initialized heap contains zero at the selected address. -/
theorem heapWordLoad_run :
    evalPanValueFfiProgSteps (riscv64PanValueFfiContext (fun _ => false))
      (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) [] []
      sourceProduction.baseAddress sourceProduction.topAddress 8 10
      sourceProduction.locals sourceProduction.globals sourceProduction.memory sourceProduction.ffi heapWordLoad
      (memoryAccess := some (panSemBitVec64MemoryAccess sourceProduction)) (contracts := none) =
        some (.returned sourceProduction.locals sourceProduction.globals sourceProduction.memory sourceProduction.ffi [.word 0], 3) := by
  with_unfolding_all rfl

/-- Read the second field of a two-word heap structure. -/
def heapPairField : Prog (RiscV.Word 64) :=
  .return (.rField 1 (.load (.comb [.one, .one]) (.const 0xa1000100)))

/-- The structured load is accepted by the public source fragment. -/
theorem heapPairField_supported (shapes : VarName → Option ShapeHOL) : Supported shapes heapPairField := by
  refine ⟨.ret (.heapField [.one, .one] 1 (by rfl) (.local (.const _))), ?_⟩
  simp [heapPairField, ProgByteRanged, ExpByteRanged, ShapeByteRanged]

/-- Store seven in the initialized heap and return the word read back. -/
def heapWordWitness : Prog (RiscV.Word 64) :=
  .seq (.store (.const 0xa1000100) (.const 7))
    (.return (.load .one (.const 0xa1000100)))

/-- Both the store and subsequent load are in the public supported fragment. -/
theorem heapWordWitness_supported : ScalarSupported heapWordWitness := by
  refine ⟨.base (.seq (.store (.const _) (.const _)) (.ret (.load (.const _)))), ?_⟩
  simp [heapWordWitness,ProgByteRanged,ExpByteRanged,ShapeByteRanged]

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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The store in the witness has a matching HOL memory update and preserves
its executable/HOL state relation. -/
theorem heapWordStore_corresponds :
    let body := progToHOL heapWordWitness
    let source := exactState body
    let production := executableState body
    ∃ memory,
      source.evaluateHOLFiniteState (.store (expToHOL (.const 0xa1000100)) (expToHOL (.const 7))) =
        (none,{source with memory := memory}) ∧
      PanSemStateRelExec {production with memory := updatePanValueMemory production.memory 0xa1000100 (.word 7)}
        {source with memory := memory}.toExact ∧
      controlSteps (.store (expToHOL (.const 0xa1000100)) (expToHOL (.const 7))) source ≤ 3 := by
  let body := progToHOL heapWordWitness
  let source := exactState body
  let production := executableState body
  have rel : PanSemStateRelExec production source.toExact := source_related body
  have ranged : PanSemStateRelExecRanged production := source_ranged body
  let _ : DecidablePred source.memaddrs := by change DecidablePred ordinaryAddress; infer_instance
  have aeval : evalPanSemStateExp production (.const 0xa1000100) = some (.word 0xa1000100) := by simp [evalPanSemStateExp_64_eq_previous,evalPanValueExp]
  have veval : evalPanSemStateExp production (.const 7) = some (.word 7) := by simp [evalPanSemStateExp_64_eq_previous,evalPanValueExp]
  have store : panValueStoreWithAccess production.memory panSemBitVec64BytesInWord 0xa1000100 (.word 7)
      (some (panSemBitVec64MemoryAccess production)) =
        some (updatePanValueMemory production.memory 0xa1000100 (.word 7)) := by
    with_unfolding_all rfl
  obtain ⟨memory,_,holRun,holRel,_,bound⟩ := counted_store_value production source rel ranged
    (.const 0xa1000100) (.const 7) (by simp [ExpByteRanged]) (by simp [ExpByteRanged])
    0xa1000100 (.word 7) aeval veval (updatePanValueMemory production.memory 0xa1000100 (.word 7)) store
    (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) [] 0
  exact ⟨memory,holRun,holRel,by simpa [panValueExpStepCost] using bound⟩
end SteppedFlapjack.Concrete
