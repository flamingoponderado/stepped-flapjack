import SteppedFlapjack.CrepToLoopSteps.ScalarClockCompositional
import SteppedFlapjack.CrepToLoopSteps.ScalarLoopConsumption
import SteppedFlapjack.CrepToLoopSteps.ScalarClockShift
import SteppedFlapjack.CrepToLoopSteps.BackendReady
/-! Explicit polynomial structural bounds for the optimized Loop program. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
/-- The structural visit bound has explicit linear coefficients in the source limit. -/
theorem scalarOutputVisit_linear (weight limit : Nat) :
    weight*(limit+3*weight*(limit+1)+1) =
      (3*weight*weight+weight)*limit+(3*weight*weight+weight) := by
  ring

/-- A completed scalar program executes as optimized Loop code with a
clock and visit bound calculated solely from that code and a Crep visit limit. -/
theorem scalarProgram_explicit {σ : Type} (p : CrepProgHOL 64) (shape : ScalarProgram p)
    (ctxt : CrepToLoopContextExact) (live : NumSet)
    (source sourceFinal : CrepSemHOLState 64 σ) (result : Option (CrepResultHOLExact 64))
    (target : LoopSemStateFiniteExact 64 σ) (limit : Nat)
    (run : evalCrepSemHOLProgExact source p = (result,sourceFinal))
    (sourceBound : CrepSteps.steps p source ≤ limit) (complete : CompleteCrepResult result)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    let code := compileHOLExact ctxt live p
    let bound := 3*loopVisitWeight (optimiseHOL code)*(limit+1)
    ∃ post,
      evaluate (optimiseHOL code) {target with clock := target.clock+bound} = (resultToLoop result,post) ∧
      LoopSteps.steps (optimiseHOL code) {target with clock := target.clock+bound} ≤
        loopVisitWeight (optimiseHOL code)*(limit+bound+1) ∧
      crepToLoopStateRelExact sourceFinal {post with clock := sourceFinal.clock} ∧
      crepToLoopMemRelHOLExact sourceFinal.memory post.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals post.globals ∧
      crepToLoopCodeRelExact ctxt sourceFinal.code post.code := by
  let code := compileHOLExact ctxt live p
  let bound := 3*loopVisitWeight (optimiseHOL code)*(limit+1)
  obtain ⟨extra,out,oldPost,oldRun,hs,hm,hg,hc,outEq,_,extraBound⟩ :=
    scalarProgram_clock (σ := σ) shape ctxt live source sourceFinal result target run
      (completeCrep_nonerror complete) stateRel memRel globalsRel codeRel localsRel
  subst out
  have controlBound : loopVisitWeight code ≤ loopVisitWeight (optimiseHOL code) :=
    scalarProgram_control_le_optimized_control shape ctxt live
  have padding : extra ≤ bound := by
    dsimp only [bound]
    simp only at extraBound
    exact extraBound.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ controlBound) |>.trans (Nat.mul_le_mul_left _ (by omega)))
  let delta := bound-extra
  have nonTimeout : resultToLoop result ≠ some .timeOut := by
    cases complete <;> simp [resultToLoop]
  have shifted := evaluate_add_clock_eq code _ _ oldPost delta oldRun nonTimeout
  have clockEq : target.clock+extra+delta = target.clock+bound := by dsimp [delta]; omega
  have extended : evaluate code {target with clock := target.clock+bound} =
      (resultToLoop result,{oldPost with clock := oldPost.clock+delta}) := by simpa [clockEq] using shifted
  have loopShape := compile_scalar_program shape ctxt live
  obtain ⟨optRun,_,_⟩ := scalarLoop_optimise_source_steps loopShape _ _ (resultToLoop result) extended (completeCrep_loop complete)
  have optShape := scalarLoop_optimise loopShape
  have visits := scalarLoop_control_consumption_bound optShape _ _ (resultToLoop result) optRun
  have sourceCount := CrepSteps.scalarProgram_clock_consumed shape source sourceFinal result run
  have initial := stateRel.2.2.1
  have final := hs.2.2.1
  have consumed : target.clock+bound-(oldPost.clock+delta)+1 ≤ limit+bound+1 := by omega
  refine ⟨{oldPost with clock := oldPost.clock+delta},optRun,?_,?_,?_,?_,?_⟩
  · exact visits.trans (Nat.mul_le_mul_left _ consumed)
  · simpa [crepToLoopStateRelExact,final] using hs
  · simpa using hm
  · simpa using hg
  · simpa using hc

end SteppedFlapjack.CrepToLoopSteps
