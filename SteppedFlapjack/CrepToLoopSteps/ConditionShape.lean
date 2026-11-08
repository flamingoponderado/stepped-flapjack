import SteppedFlapjack.CrepToLoopSteps.BranchExtraClock
import SteppedFlapjack.LoopSteps.ClockConsumption
import SteppedFlapjack.CrepToLoopSteps.ScalarPrefix

/-! Scalar conditions whose compiled expression prefixes are loop-free. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.LoopToWordSteps

/-- Direct conditions and comparisons of direct expressions. -/
inductive BranchCondition {width : Nat} [NeZero width] : CrepExpHOL width → Prop
  | direct {e} : DirectExpression e → BranchCondition e
  | cmp (op) {a b} : DirectExpression a → DirectExpression b → BranchCondition (.cmp op a b)

/-- Legacy simple conditions belong to the full scalar fragment. -/
theorem BranchCondition.toScalar {width : Nat} [NeZero width] {e : CrepExpHOL width}
    (shape : BranchCondition e) : CompiledScalar e := by
  cases shape with
  | direct h => exact .direct h
  | cmp op a b => exact .cmp op (.direct a) (.direct b)

instance {width : Nat} [NeZero width] {e : CrepExpHOL width} :
    Coe (BranchCondition e) (CompiledScalar e) where
  coe := BranchCondition.toScalar

/-- Each generated prefix statement is loop-free and supported by instruction
selection; this exposes the actual compiler output and fresh temporaries. -/
theorem condition_prefix_shape {width : Nat} [NeZero width] {e : CrepExpHOL width}
    (shape : CompiledScalar e) (ctxt : CrepToLoopContextExact) (tmp : Nat) (live : NumSet) :
    ∃ code value next outLive,
      compileExpHOLExact ctxt tmp live e = (code,value,next,outLive) ∧
      (∀ p ∈ code, BranchedProgram p) ∧
      (∀ p ∈ code, LoopSelectProgram p) := by
  obtain ⟨code,value,next,outLive,compiled,branch,selected,_⟩ :=
    compiledScalar_prefix shape ctxt tmp live
  exact ⟨code,value,next,outLive,compiled,branch,selected⟩

/-- A nested sequence of loop-free statements is loop-free. -/
theorem nestedSeq_branched {width : Nat} [NeZero width] (code : List (HolLoopProg width))
    (shape : ∀ p ∈ code, BranchedProgram p) : BranchedProgram (loopNestedSeqHOL code) := by
  induction code with
  | nil => exact .leaf .skip
  | cons p code ih =>
    simp only [loopNestedSeqHOL]
    exact .seq (shape p (by simp)) (ih (by intro q hq; exact shape q (by simp [hq])))

/-- The actual Loop prefix for a generalized scalar expression has a
literal-independent visit bound, with no execution or fuel premise. -/
theorem compiledScalar_prefix_steps {width : Nat} [NeZero width] {σ : Type}
    {e : CrepExpHOL width} (shape : CompiledScalar e)
    (ctxt : CrepToLoopContextExact) (tmp : Nat) (live : NumSet)
    (state : LoopSemStateFiniteExact width σ) :
    let code := (compileExpHOLExact ctxt tmp live e).1
    LoopSteps.steps (loopNestedSeqHOL code) state ≤
      LoopSteps.structuralWeight (loopNestedSeqHOL code) := by
  obtain ⟨code,value,next,outLive,compiled,branch,_⟩ := compiledScalar_prefix shape ctxt tmp live
  have bounded := LoopSteps.branchedProgram_structural_bound (nestedSeq_branched code branch) state
  simpa [compiled] using bounded

/-- A nested sequence of selected statements is selected. -/
theorem nestedSeq_select {width : Nat} [NeZero width] (code : List (HolLoopProg width))
    (shape : ∀ p ∈ code, LoopSelectProgram p) : LoopSelectProgram (loopNestedSeqHOL code) := by
  induction code with
  | nil => exact .leaf .skip
  | cons p code ih =>
    simp only [loopNestedSeqHOL]
    exact .seq (shape p (by simp)) (ih (by intro q hq; exact shape q (by simp [hq])))

/-- Every correctness clock witness for a compiled branch condition prefix is
bounded by that prefix's syntax size. -/
theorem condition_extraClock_bound {width : Nat} [NeZero width] {σ : Type}
    (source : CrepSemHOLState width σ) (target post : LoopSemStateFiniteExact width σ)
    (code : List (HolLoopProg width)) (extra : Nat)
    (shape : ∀ p ∈ code, BranchedProgram p)
    (stateRel : crepToLoopStateRelExact source target)
    (run : evaluate (loopNestedSeqHOL code) {target with clock := target.clock+extra} = (none,post))
    (postRel : crepToLoopStateRelExact source post) : extra ≤ sizeOf (loopNestedSeqHOL code) := by
  have hshape := nestedSeq_branched code shape
  have consumed := LoopSteps.branchedProgram_clock_consumed hshape
    {target with clock := target.clock+extra} post none run
  have visits := LoopSteps.branchedProgram_static_bound hshape {target with clock := target.clock+extra}
  have initial := stateRel.2.2.1
  have final := postRel.2.2.1
  simp only at consumed
  omega


/-- The actual loop body generated for a supported condition. -/
def branchConditionWhileBody {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (live : NumSet) (code : List (HolLoopProg width))
    (value : HolLoopExp width) (next : Nat) (body : CrepProgHOL width) : HolLoopProg width :=
  loopNestedSeqHOL (code ++ [.assign next value,
    .ite .notEqual next (.imm (0 : BitVec width))
      (.seq (compileHOLExact ctxt live body) (.continue 0)) (.break 0) live])

/-- Scalar conditions compile to a loop whose body is loop-free
and accepted by the selected RISC-V backend. -/
theorem branchCondition_compileWhile {width : Nat} [NeZero width]
    (condition : CrepExpHOL width) (conditionShape : CompiledScalar condition)
    (body : CrepProgHOL width) (bodyShape : LoopFreeCrep body)
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    ∃ code value next outLive,
      compileExpHOLExact ctxt (ctxt.vmax+1) live condition = (code,value,next,outLive) ∧
      compileHOLExact ctxt live (.while condition body) =
        .loop live (branchConditionWhileBody ctxt live code value next body) live ∧
      BranchedProgram (branchConditionWhileBody ctxt live code value next body) ∧
      LoopSelectProgram (compileHOLExact ctxt live (.while condition body)) := by
  obtain ⟨code,value,next,outLive,compiled,branch,selected⟩ :=
    condition_prefix_shape conditionShape ctxt (ctxt.vmax+1) live
  have fullBranch : ∀ p ∈ code ++ [.assign next value,
      .ite .notEqual next (.imm (0 : BitVec width))
        (.seq (compileHOLExact ctxt live body) (.continue 0)) (.break 0) live], BranchedProgram p := by
    intro p hp
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with h | rfl | rfl
    · exact branch p h
    · exact .leaf (.assign _ _)
    · exact .ite _ _ _ _ (.seq (compile_loopFreeCrep bodyShape ctxt live) (.leaf (.continue 0))) (.leaf (.break 0))
  have fullSelect : ∀ p ∈ code ++ [.assign next value,
      .ite .notEqual next (.imm (0 : BitVec width))
        (.seq (compileHOLExact ctxt live body) (.continue 0)) (.break 0) live], LoopSelectProgram p := by
    intro p hp
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with h | rfl | rfl
    · exact selected p h
    · exact .assign _ _
    · exact .ite _ _ _ _ (.seq (compile_loopFreeCrep_select bodyShape ctxt live) (.leaf (.continue 0))) (.leaf (.break 0))
  have hcomp : compileHOLExact ctxt live (.while condition body) =
      .loop live (branchConditionWhileBody ctxt live code value next body) live := by
    simp only [compileHOLExact,compiled,branchConditionWhileBody]
  refine ⟨code,value,next,outLive,compiled,hcomp,?_,?_⟩
  · exact nestedSeq_branched _ fullBranch
  · rw [hcomp]
    exact .loop _ _ (nestedSeq_select _ fullSelect)

end SteppedFlapjack.CrepToLoopSteps
