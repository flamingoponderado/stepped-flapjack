import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Assembly

/-! Local relations for a bounded execution of the actual compiler output. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- An execution with the correct result has the compiler's local relation:
for non-timeout results both runs agree after adding enough clock, and timeout
has no local-state obligation. -/
theorem compiler_run_locals {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (source sourceFinal : CrepSemHOLState width σ)
    (result : Option (CrepResultHOLExact width)) (target post : LoopSemStateFiniteExact width σ)
    (ctxt : CrepToLoopContextExact) (live : NumSet) (extra : Nat)
    (run : evalCrepSemHOLProgExact source p = (result,sourceFinal)) (nonerror : result ≠ some .error)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (targetRun : evaluate (compileHOLExact ctxt live p) {target with clock := target.clock+extra} =
      (resultToLoop result,post)) :
    localsResultRel ctxt live result sourceFinal post := by
  obtain ⟨other,out,otherPost,otherRun,_,_,_,_,map,otherLocals⟩ :=
    crepToLoop_ncompile_correct p source result sourceFinal target ctxt live
      ⟨run,nonerror,stateRel,memRel,globalsRel,codeRel,localsRel⟩
  subst out
  by_cases nontimeout : resultToLoop result ≠ some .timeOut
  · let reserve := max extra other
    have lift₁ := evaluate_add_clock_eq (compileHOLExact ctxt live p) {target with clock := target.clock+extra}
      (resultToLoop result) post (reserve-extra) targetRun nontimeout
    have lift₂ := evaluate_add_clock_eq (compileHOLExact ctxt live p) {target with clock := target.clock+other}
      (resultToLoop result) otherPost (reserve-other) otherRun nontimeout
    have clk₁ : target.clock+extra+(reserve-extra) = target.clock+reserve := by dsimp [reserve]; omega
    have clk₂ : target.clock+other+(reserve-other) = target.clock+reserve := by dsimp [reserve]; omega
    have equalPost : {post with clock := post.clock+(reserve-extra)} =
        {otherPost with clock := otherPost.clock+(reserve-other)} := by
      have h₁ : evaluate (compileHOLExact ctxt live p) {target with clock := target.clock+reserve} =
          (resultToLoop result,{post with clock := post.clock+(reserve-extra)}) := by simpa [clk₁] using lift₁
      have h₂ : evaluate (compileHOLExact ctxt live p) {target with clock := target.clock+reserve} =
          (resultToLoop result,{otherPost with clock := otherPost.clock+(reserve-other)}) := by simpa [clk₂] using lift₂
      exact (Prod.mk.inj (h₁.symm.trans h₂)).2
    have localEq : post.locals = otherPost.locals := congrArg (fun s => s.locals) equalPost
    cases result with
    | none => simpa [localsResultRel,localEq] using otherLocals
    | some r => cases r <;> simp [localsResultRel,localEq] at otherLocals ⊢ <;> assumption
  · cases result with
    | none => simp [resultToLoop] at nontimeout
    | some r => cases r <;> simp_all [resultToLoop,localsResultRel]
end SteppedFlapjack.CrepToLoopSteps
