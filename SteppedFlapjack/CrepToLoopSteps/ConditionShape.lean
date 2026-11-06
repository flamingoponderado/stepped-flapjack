import SteppedFlapjack.CrepToLoopSteps.BranchExtraClock

/-! Conditions whose compiled expression prefixes are loop-free. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.LoopToWordSteps

/-- Direct conditions and comparisons of direct expressions. -/
inductive BranchCondition {width : Nat} [NeZero width] : CrepExpHOL width → Prop
  | direct {e} : DirectExpression e → BranchCondition e
  | cmp (op) {a b} : DirectExpression a → DirectExpression b → BranchCondition (.cmp op a b)

/-- Each generated prefix statement is loop-free and supported by instruction
selection; this exposes the actual compiler output and fresh temporaries. -/
theorem condition_prefix_shape {width : Nat} [NeZero width] {e : CrepExpHOL width}
    (shape : BranchCondition e) (ctxt : CrepToLoopContextExact) (tmp : Nat) (live : NumSet) :
    ∃ code value next outLive,
      compileExpHOLExact ctxt tmp live e = (code,value,next,outLive) ∧
      (∀ p ∈ code, BranchedProgram p) ∧
      (∀ p ∈ code, LoopSelectProgram p) := by
  cases shape with
  | direct h =>
    obtain ⟨value,compiled⟩ := directExpression_noCode h ctxt tmp live
    exact ⟨[],value,tmp,live,compiled,by simp,by simp⟩
  | @cmp op a b ha hb =>
    obtain ⟨va,ca⟩ := directExpression_noCode ha ctxt tmp live
    obtain ⟨vb,cb⟩ := directExpression_noCode hb ctxt tmp live
    refine ⟨[.assign (tmp+1) va, .assign (tmp+2) vb,
      .ite op (tmp+1) (.reg (tmp+2)) (.assign (tmp+1) (.const 1))
        (.assign (tmp+1) (.const 0)) (sptListInsert [tmp+1,tmp+2] live)],
      .var (tmp+1),tmp+3,sptListInsert [tmp+1,tmp+2] live,?_,?_,?_⟩
    · simp only [compileExpHOLExact,ca,cb,progIfHOLExact,List.nil_append]
    · intro p hp
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact .leaf (.assign _ _)
      · exact .leaf (.assign _ _)
      · exact .ite _ _ _ _ (.leaf (.assign _ _)) (.leaf (.assign _ _))
    · intro p hp
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact .assign _ _
      · exact .assign _ _
      · exact .ite _ _ _ _ (.assign _ _) (.assign _ _)

/-- A nested sequence of loop-free statements is loop-free. -/
theorem nestedSeq_branched {width : Nat} [NeZero width] (code : List (HolLoopProg width))
    (shape : ∀ p ∈ code, BranchedProgram p) : BranchedProgram (loopNestedSeqHOL code) := by
  induction code with
  | nil => exact .leaf .skip
  | cons p code ih =>
    simp only [loopNestedSeqHOL]
    exact .seq (shape p (by simp)) (ih (by intro q hq; exact shape q (by simp [hq])))

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


/-- The existing expression-correctness witness has a statically bounded
extra clock for both direct and comparison conditions. -/
theorem condition_correct_with_bounded_extra {width : Nat} [NeZero width] {σ : Type}
    (e : CrepExpHOL width) (shape : BranchCondition e) (source : CrepSemHOLState width σ)
    (v : HolWordLab width) (target : LoopSemStateFiniteExact width σ)
    (ctxt : CrepToLoopContextExact) (tmp : Nat) (live : NumSet)
    (evalSource : evalCrepSemHOLExp source e = some v)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (fresh : ctxt.vmax < tmp) :
    ∃ code value next outLive extra post,
      compileExpHOLExact ctxt tmp live e = (code,value,next,outLive) ∧
      (∀ p ∈ code, BranchedProgram p) ∧ (∀ p ∈ code, LoopSelectProgram p) ∧
      evaluate (loopNestedSeqHOL code) {target with clock := target.clock+extra} = (none,post) ∧
      LoopSemStateFiniteExact.eval post value = some (wlabWlocExact v) ∧
      crepToLoopStateRelExact source post ∧
      crepToLoopMemRelHOLExact source.memory post.memory source.memaddrs ∧
      crepToLoopGlobalsRelHOLExact source.globals post.globals ∧
      crepToLoopCodeRelExact ctxt source.code post.code ∧
      crepToLoopLocalsRelExact ctxt outLive source.locals post.locals ∧
      extra ≤ sizeOf (loopNestedSeqHOL code) := by
  obtain ⟨code,value,next,outLive,compiled,branch,selected⟩ := condition_prefix_shape shape ctxt tmp live
  obtain ⟨extra,post,run,he,hs,hm,hg,hc,hl⟩ :=
    crepToLoop_comp_exp_preserves_eval source e v target ctxt tmp live code value next outLive
      ⟨evalSource,stateRel,memRel,globalsRel,codeRel,localsRel,compiled,fresh⟩
  exact ⟨code,value,next,outLive,extra,post,compiled,branch,selected,run,he,hs,hm,hg,hc,hl,
    condition_extraClock_bound source target post code extra branch stateRel run hs⟩

/-- The actual loop body generated for a supported condition. -/
def branchConditionWhileBody {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (live : NumSet) (code : List (HolLoopProg width))
    (value : HolLoopExp width) (next : Nat) (body : CrepProgHOL width) : HolLoopProg width :=
  loopNestedSeqHOL (code ++ [.assign next value,
    .ite .notEqual next (.imm (0 : BitVec width))
      (.seq (compileHOLExact ctxt live body) (.continue 0)) (.break 0) live])

/-- Comparison conditions still compile to a loop whose body is loop-free
and accepted by the selected RISC-V backend. -/
theorem branchCondition_compileWhile {width : Nat} [NeZero width]
    (condition : CrepExpHOL width) (conditionShape : BranchCondition condition)
    (body : CrepProgHOL width) (bodyShape : BranchProgram body)
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
    · exact .ite _ _ _ _ (.seq (compile_branchProgram bodyShape ctxt live) (.leaf (.continue 0))) (.leaf (.break 0))
  have fullSelect : ∀ p ∈ code ++ [.assign next value,
      .ite .notEqual next (.imm (0 : BitVec width))
        (.seq (compileHOLExact ctxt live body) (.continue 0)) (.break 0) live], LoopSelectProgram p := by
    intro p hp
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with h | rfl | rfl
    · exact selected p h
    · exact .assign _ _
    · exact .ite _ _ _ _ (.seq (compile_branchProgram_select bodyShape ctxt live) (.leaf (.continue 0))) (.leaf (.break 0))
  have hcomp : compileHOLExact ctxt live (.while condition body) =
      .loop live (branchConditionWhileBody ctxt live code value next body) live := by
    simp only [compileHOLExact,compiled,branchConditionWhileBody]
  refine ⟨code,value,next,outLive,compiled,hcomp,?_,?_⟩
  · exact nestedSeq_branched _ fullBranch
  · rw [hcomp]
    exact .loop _ _ (nestedSeq_select _ fullSelect)

end SteppedFlapjack.CrepToLoopSteps
