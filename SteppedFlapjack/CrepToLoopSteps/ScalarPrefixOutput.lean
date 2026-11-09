import SteppedFlapjack.CrepToLoopSteps.ScalarUnmarked
import SteppedFlapjack.CrepToLoopSteps.ConditionShape
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack SteppedFlapjack.LoopToWordSteps
variable {width : Nat} [NeZero width]

theorem while_prefix_le_control {condition : CrepExpHOL width} (conditionShape : CompiledScalar condition)
    {body : CrepProgHOL width}
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    LoopSteps.structuralWeight (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live condition).1) ≤
      loopVisitWeight (compileHOLExact ctxt live (.while condition body)) := by
  obtain ⟨code,value,next,outLive,compiled,branch,_⟩ := condition_prefix_shape conditionShape ctxt (ctxt.vmax+1) live
  have branch' := nestedSeq_branched code branch
  have prefixWeight := nestedSeq_append_weight code
    [.assign next value, .ite .notEqual next (.imm (0 : BitVec width))
      (.seq (compileHOLExact ctxt live body) (.continue 0)) (.break 0) live]
  have inner : loopVisitWeight (loopNestedSeqHOL code) ≤
      loopVisitWeight (compileHOLExact ctxt live (.while condition body)) := by
    simp only [compileHOLExact,compiled,loopVisitWeight]
    omega
  simp only [compiled] at *
  rw [← branched_visitWeight branch']
  exact inner
theorem ite_prefix_le_control {condition : CrepExpHOL width} (conditionShape : CompiledScalar condition)
    {a b : CrepProgHOL width}
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    LoopSteps.structuralWeight (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live condition).1) ≤
      loopVisitWeight (compileHOLExact ctxt live (.ite condition a b)) := by
  obtain ⟨code,value,next,outLive,compiled,branch,_⟩ := condition_prefix_shape conditionShape ctxt (ctxt.vmax+1) live
  have branch' := nestedSeq_branched code branch
  have prefixWeight := nestedSeq_append_weight code
    [.assign next value, .ite .notEqual next (.imm (0 : BitVec width))
      (compileHOLExact ctxt live a) (compileHOLExact ctxt live b) live]
  have inner : loopVisitWeight (loopNestedSeqHOL code) ≤
      loopVisitWeight (compileHOLExact ctxt live (.ite condition a b)) := by
    simp only [compileHOLExact,compiled]
    exact prefixWeight
  simp only [compiled] at *
  rw [← branched_visitWeight branch']
  exact inner

theorem dec_prefix_le_control (name : Nat) {init : CrepExpHOL width} (initShape : CompiledScalar init)
    {body : CrepProgHOL width}
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    LoopSteps.structuralWeight (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live init).1) ≤
      loopVisitWeight (compileHOLExact ctxt live (.dec name init body)) := by
  obtain ⟨code,value,next,outLive,compiled,branch,_⟩ := condition_prefix_shape initShape ctxt (ctxt.vmax+1) live
  have branch' := nestedSeq_branched code branch
  have inner : loopVisitWeight (loopNestedSeqHOL code) ≤
      loopVisitWeight (compileHOLExact ctxt live (.dec name init body)) := by
    simp only [compileHOLExact,compiled,loopVisitWeight]
    omega
  simp only [compiled] at *
  rw [← branched_visitWeight branch']
  exact inner

private theorem nested_member (xs : List (HolLoopProg width)) (p : HolLoopProg width)
    (h : p ∈ xs) : loopVisitWeight p ≤ loopVisitWeight (loopNestedSeqHOL xs) := by
  induction xs with
  | nil => simp at h
  | cons q rest ih =>
    simp only [List.mem_cons] at h
    simp only [loopNestedSeqHOL,loopVisitWeight]
    rcases h with rfl | h
    · omega
    · have hh := ih h; omega

theorem while_body_weight {condition : CrepExpHOL width} {body : CrepProgHOL width}
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    loopVisitWeight (compileHOLExact ctxt live body) <
      loopVisitWeight (compileHOLExact ctxt live (.while condition body)) := by
  rcases h : compileExpHOLExact ctxt (ctxt.vmax+1) live condition with ⟨code,value,next,outLive⟩
  let branch : HolLoopProg width := .ite .notEqual next (.imm (0 : BitVec width))
    (.seq (compileHOLExact ctxt live body) (.continue 0)) (.break 0) live
  have member : branch ∈ code ++ [.assign next value,branch] := by simp
  have bound := nested_member _ branch member
  simp only [branch,loopVisitWeight] at bound
  simp only [compileHOLExact,h,loopVisitWeight]
  omega
theorem ite_children_weight {condition : CrepExpHOL width} {a b : CrepProgHOL width}
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    loopVisitWeight (compileHOLExact ctxt live a) < loopVisitWeight (compileHOLExact ctxt live (.ite condition a b)) ∧
    loopVisitWeight (compileHOLExact ctxt live b) < loopVisitWeight (compileHOLExact ctxt live (.ite condition a b)) := by
  rcases h : compileExpHOLExact ctxt (ctxt.vmax+1) live condition with ⟨code,value,next,outLive⟩
  let branch : HolLoopProg width := .ite .notEqual next (.imm (0 : BitVec width))
    (compileHOLExact ctxt live a) (compileHOLExact ctxt live b) live
  have member : branch ∈ code ++ [.assign next value,branch] := by simp
  have bound := nested_member _ branch member
  simp only [branch,loopVisitWeight] at bound
  simp only [compileHOLExact,h]
  omega

theorem dec_body_weight (name : Nat) {init : CrepExpHOL width} {body : CrepProgHOL width}
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    let tmp := (compileExpHOLExact ctxt (ctxt.vmax+1) live init).2.2.1
    loopVisitWeight (compileHOLExact {ctxt with vars := ctxt.vars.updateEq (name,tmp), vmax := tmp}
      (sptInsert tmp () live) body) < loopVisitWeight (compileHOLExact ctxt live (.dec name init body)) := by
  rcases h : compileExpHOLExact ctxt (ctxt.vmax+1) live init with ⟨code,value,next,outLive⟩
  simp only [compileHOLExact,h,loopVisitWeight]
  omega

theorem seq_children_weight (a b : CrepProgHOL width) (ctxt : CrepToLoopContextExact) (live : NumSet) :
    loopVisitWeight (compileHOLExact ctxt live a) < loopVisitWeight (compileHOLExact ctxt live (.seq a b)) ∧
    loopVisitWeight (compileHOLExact ctxt live b) < loopVisitWeight (compileHOLExact ctxt live (.seq a b)) := by
  simp only [compileHOLExact,loopVisitWeight]
  omega

theorem nestedSeq_append_weight_sum (a b : List (HolLoopProg width)) :
    loopVisitWeight (loopNestedSeqHOL a) + loopVisitWeight (loopNestedSeqHOL b) ≤
      loopVisitWeight (loopNestedSeqHOL (a ++ b)) + 1 := by
  induction a with
  | nil => simp [loopNestedSeqHOL,loopVisitWeight]; omega
  | cons p rest ih => simp only [List.cons_append,loopNestedSeqHOL,loopVisitWeight]; omega

theorem while_prefix_body_weight {condition : CrepExpHOL width} (conditionShape : CompiledScalar condition)
    {body : CrepProgHOL width} (ctxt : CrepToLoopContextExact) (live : NumSet) :
    LoopSteps.structuralWeight (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live condition).1) +
      loopVisitWeight (compileHOLExact ctxt live body) + 2 ≤
      loopVisitWeight (compileHOLExact ctxt live (.while condition body)) := by
  obtain ⟨code,value,next,outLive,compiled,branch,_⟩ := condition_prefix_shape conditionShape ctxt (ctxt.vmax+1) live
  have branchShape := nestedSeq_branched code branch
  have pref := nestedSeq_append_weight_sum code
    [.assign next value, .ite .notEqual next (.imm (0 : BitVec width))
      (.seq (compileHOLExact ctxt live body) (.continue 0)) (.break 0) live]
  simp only [compiled]
  rw [← branched_visitWeight branchShape]
  rw [compileHOLExact,compiled]
  simp only [loopNestedSeqHOL,loopVisitWeight] at pref ⊢
  omega

theorem ite_prefix_body_weight {condition : CrepExpHOL width} (conditionShape : CompiledScalar condition)
    {a b : CrepProgHOL width} (ctxt : CrepToLoopContextExact) (live : NumSet) :
    LoopSteps.structuralWeight (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live condition).1) +
      max (loopVisitWeight (compileHOLExact ctxt live a)) (loopVisitWeight (compileHOLExact ctxt live b)) + 1 ≤
      loopVisitWeight (compileHOLExact ctxt live (.ite condition a b)) := by
  obtain ⟨code,value,next,outLive,compiled,branch,_⟩ := condition_prefix_shape conditionShape ctxt (ctxt.vmax+1) live
  have branchShape := nestedSeq_branched code branch
  have pref := nestedSeq_append_weight_sum code
    [.assign next value, .ite .notEqual next (.imm (0 : BitVec width))
      (compileHOLExact ctxt live a) (compileHOLExact ctxt live b) live]
  simp only [compiled]
  rw [← branched_visitWeight branchShape]
  rw [compileHOLExact,compiled]
  simp only [loopNestedSeqHOL,loopVisitWeight] at pref ⊢
  omega

theorem decl_prefix_body_weight (name : Nat) {init : CrepExpHOL width} (initShape : CompiledScalar init)
    {body : CrepProgHOL width} (ctxt : CrepToLoopContextExact) (live : NumSet) :
    let tmp := (compileExpHOLExact ctxt (ctxt.vmax+1) live init).2.2.1
    LoopSteps.structuralWeight (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live init).1) +
      loopVisitWeight (compileHOLExact {ctxt with vars := ctxt.vars.updateEq (name,tmp), vmax := tmp}
        (sptInsert tmp () live) body) ≤ loopVisitWeight (compileHOLExact ctxt live (.dec name init body)) := by
  obtain ⟨code,value,next,outLive,compiled,branch,_⟩ := condition_prefix_shape initShape ctxt (ctxt.vmax+1) live
  have branchShape := nestedSeq_branched code branch
  simp only [compiled]
  rw [← branched_visitWeight branchShape]
  simp only [compileHOLExact,compiled,loopVisitWeight]
  omega
end SteppedFlapjack.CrepToLoopSteps
