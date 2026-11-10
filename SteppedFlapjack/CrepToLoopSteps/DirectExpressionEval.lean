import SteppedFlapjack.CrepToLoopSteps.BranchExtraClock

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


end SteppedFlapjack.CrepToLoopSteps
