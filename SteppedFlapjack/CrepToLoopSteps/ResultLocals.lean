import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Assembly

/-! Local relations for a bounded execution of the actual compiler output. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- An explicit non-timeout run has the compiler-proved final state relations. -/
theorem compiler_run_relations {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (source sourceFinal : CrepSemHOLState width σ)
    (result : Option (CrepResultHOLExact width)) (target post : LoopSemStateFiniteExact width σ)
    (ctxt : CrepToLoopContextExact) (live : NumSet) (extra : Nat)
    (run : evalCrepSemHOLProgExact source p = (result,sourceFinal)) (nonerror : result ≠ some .error)
    (nonTimeout : resultToLoop result ≠ some .timeOut)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (targetRun : evaluate (compileHOLExact ctxt live p) {target with clock := target.clock+extra} =
      (resultToLoop result,post)) :
    crepToLoopStateRelExact sourceFinal {post with clock := sourceFinal.clock} ∧
    crepToLoopMemRelHOLExact sourceFinal.memory post.memory sourceFinal.memaddrs ∧
    crepToLoopGlobalsRelHOLExact sourceFinal.globals post.globals ∧
    crepToLoopCodeRelExact ctxt sourceFinal.code post.code ∧
    localsResultRel ctxt live result sourceFinal post := by
  obtain ⟨other,out,otherPost,otherRun,otherState,otherMem,otherGlobals,otherCode,map,otherLocals⟩ :=
    crepToLoop_ncompile_correct p source result sourceFinal target ctxt live
      ⟨run,nonerror,stateRel,memRel,globalsRel,codeRel,localsRel⟩
  subst out
  let reserve := max extra other
  have lift₁ := evaluate_add_clock_eq (compileHOLExact ctxt live p) {target with clock := target.clock+extra}
    (resultToLoop result) post (reserve-extra) targetRun nonTimeout
  have lift₂ := evaluate_add_clock_eq (compileHOLExact ctxt live p) {target with clock := target.clock+other}
    (resultToLoop result) otherPost (reserve-other) otherRun nonTimeout
  have clk₁ : target.clock+extra+(reserve-extra) = target.clock+reserve := by dsimp [reserve]; omega
  have clk₂ : target.clock+other+(reserve-other) = target.clock+reserve := by dsimp [reserve]; omega
  have equalPost : {post with clock := post.clock+(reserve-extra)} =
      {otherPost with clock := otherPost.clock+(reserve-other)} := by
    have h₁ : evaluate (compileHOLExact ctxt live p) {target with clock := target.clock+reserve} =
        (resultToLoop result,{post with clock := post.clock+(reserve-extra)}) := by simpa [clk₁] using lift₁
    have h₂ : evaluate (compileHOLExact ctxt live p) {target with clock := target.clock+reserve} =
        (resultToLoop result,{otherPost with clock := otherPost.clock+(reserve-other)}) := by simpa [clk₂] using lift₂
    exact (Prod.mk.inj (h₁.symm.trans h₂)).2
  have normEq : {post with clock := sourceFinal.clock} = {otherPost with clock := sourceFinal.clock} := by
    have h := congrArg (fun (s : LoopSemStateFiniteExact width σ) => {s with clock := sourceFinal.clock}) equalPost
    exact h
  have localEq : post.locals = otherPost.locals := congrArg (fun s => s.locals) equalPost
  have memEq : post.memory = otherPost.memory := congrArg (fun s => s.memory) equalPost
  have globalEq : post.globals = otherPost.globals := congrArg (fun s => s.globals) equalPost
  have codeEq : post.code = otherPost.code := congrArg (fun s => s.code) equalPost
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [normEq]
    have hclock := otherState.2.2.1
    simpa [crepToLoopStateRelExact,hclock] using otherState
  · simpa [memEq] using otherMem
  · simpa [globalEq] using otherGlobals
  · simpa [codeEq] using otherCode
  · cases result with
    | none => simpa [localsResultRel,localEq] using otherLocals
    | some r => cases r <;> simp [localsResultRel,localEq] at otherLocals ⊢ <;> assumption
/-- The corresponding locals relation also holds for timeout outcomes. -/
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
      (resultToLoop result,post)) : localsResultRel ctxt live result sourceFinal post := by
  by_cases h : resultToLoop result ≠ some .timeOut
  · exact (compiler_run_relations p source sourceFinal result target post ctxt live extra run nonerror h
      stateRel memRel globalsRel codeRel localsRel targetRun).2.2.2.2
  · cases result with
    | none => simp [resultToLoop] at h
    | some r => cases r <;> simp_all [resultToLoop,localsResultRel]


end SteppedFlapjack.CrepToLoopSteps
