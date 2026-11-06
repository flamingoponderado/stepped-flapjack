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

end SteppedFlapjack.CrepToLoopSteps
