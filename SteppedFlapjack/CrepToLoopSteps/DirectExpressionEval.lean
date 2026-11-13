import SteppedFlapjack.CrepToLoopSteps.BranchExtraClock
import SteppedFlapjack.CrepToLoopSteps.ConditionShape

/-! Direct Crep expressions preserve evaluation without additional clock. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- A direct expression has no compiled prefix: its Loop expression evaluates
in the original related state, with no extra clock or state transition. -/
theorem directExpression_preserves_eval {width : Nat} [NeZero width] {σ : Type}
    (e : CrepExpHOL width) (shape : DirectExpression e)
    (source : CrepSemHOLState width σ) (v : HolWordLab width)
    (target : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact)
    (tmp : Nat) (live : NumSet)
    (evalSource : evalCrepSemHOLExp source e = some v)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (fresh : ctxt.vmax < tmp) :
    ∃ value, compileExpHOLExact ctxt tmp live e = ([],value,tmp,live) ∧
      LoopSemStateFiniteExact.eval target value = some (wlabWlocExact v) := by
  obtain ⟨value,compiled⟩ := directExpression_noCode shape ctxt tmp live
  obtain ⟨extra,post,run,evalTarget,postRel,_,_,_,_⟩ :=
    crepToLoop_comp_exp_preserves_eval source e v target ctxt tmp live [] value tmp live
      ⟨evalSource,stateRel,memRel,globalsRel,codeRel,localsRel,compiled,fresh⟩
  have postEq : post = {target with clock := target.clock + extra} := by
    simpa [loopNestedSeqHOL,LoopSemStateFiniteExact.evaluate] using run.symm
  have zero : extra = 0 := by
    have initial := stateRel.2.2.1
    have final := postRel.2.2.1
    rw [postEq] at final
    simp only at final
    omega
  subst extra
  simp only [Nat.add_zero] at postEq
  subst post
  exact ⟨value,compiled,evalTarget⟩

/-- Direct arguments compile and evaluate in the original related Loop state. -/
theorem directExpressions_preserves_eval {width : Nat} [NeZero width] {σ : Type}
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, DirectExpression e)
    (source : CrepSemHOLState width σ) (values : List (HolWordLab width))
    (target : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (tmp : Nat) (live : NumSet)
    (evaluated : args.mapM (evalCrepSemHOLExp source) = some values)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) (fresh : ctxt.vmax < tmp) :
    ∃ les, compileExpsHOLExact ctxt tmp live args = ([],les,tmp,live) ∧
      les.mapM (LoopSemStateFiniteExact.eval target) = some (values.map wlabWlocExact) := by
  have mapped := (optMmapEqSome args _ _).mp evaluated
  induction args generalizing values with
  | nil =>
    cases values <;> simp_all [compileExpsHOLExact]
  | cons e es ih =>
    cases values with
    | nil => simp at mapped
    | cons v vs =>
      simp only [List.map_cons,List.cons.injEq] at mapped
      obtain ⟨hv,ht⟩ := mapped
      obtain ⟨le,hcomp,heval⟩ := directExpression_preserves_eval e (shape e (by simp)) source v target ctxt tmp live
        hv stateRel memRel globalsRel codeRel localsRel fresh
      have hevalTail : es.mapM (evalCrepSemHOLExp source) = some vs := (optMmapEqSome es _ _).mpr ht
      obtain ⟨les,hrest,hevals⟩ := ih (fun x hx => shape x (by simp [hx])) vs hevalTail ht
      refine ⟨le :: les,?_,?_⟩
      · simp [compileExpsHOLExact,hcomp,hrest]
      · apply (optMmapEqSome _ _ _).mpr
        simp only [List.map_cons,heval]
        exact congrArg (List.cons _) ((optMmapEqSome les _ _).mp hevals)


/-- Scalar argument prefixes preserve values and have an explicit clock cost
computed from the code emitted for those arguments. -/
theorem scalarExpressions_preserves_eval_bounded {width : Nat} [NeZero width] {σ : Type}
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, CompiledScalar e)
    (source : CrepSemHOLState width σ) (values : List (HolWordLab width))
    (target : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (tmp : Nat) (live : NumSet)
    (evaluated : args.mapM (evalCrepSemHOLExp source) = some values)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) (fresh : ctxt.vmax < tmp) :
    let compiled := compileExpsHOLExact ctxt tmp live args
    ∃ extra post,
      evaluate (loopNestedSeqHOL compiled.1) {target with clock := target.clock+extra} = (none,post) ∧
      compiled.2.1.mapM (LoopSemStateFiniteExact.eval post) = some (values.map wlabWlocExact) ∧
      crepToLoopStateRelExact source post ∧
      crepToLoopMemRelHOLExact source.memory post.memory source.memaddrs ∧
      crepToLoopGlobalsRelHOLExact source.globals post.globals ∧
      crepToLoopCodeRelExact ctxt source.code post.code ∧
      crepToLoopLocalsRelExact ctxt compiled.2.2.2 source.locals post.locals ∧
      extra ≤ LoopSteps.structuralWeight (loopNestedSeqHOL compiled.1) := by
  obtain ⟨code,les,next,outLive,compiled,_,prefixShape⟩ :=
    compiledScalars_prefix args shape ctxt tmp live
  obtain ⟨extra,post,run,evals,state,mem,globals,codeRelPost,locals⟩ :=
    crepToLoop_comp_exps_preserves_eval args source values target ctxt tmp live code les next outLive
      ⟨evaluated,stateRel,memRel,globalsRel,codeRel,localsRel,compiled,fresh⟩
  have bound := condition_extraClock_bound source target post code extra prefixShape.1 stateRel run state
  exact ⟨extra,post,by simpa [compiled] using run,by simpa [compiled] using evals,
    state,mem,globals,codeRelPost,by simpa [compiled] using locals,by simpa [compiled] using bound⟩

end SteppedFlapjack.CrepToLoopSteps
