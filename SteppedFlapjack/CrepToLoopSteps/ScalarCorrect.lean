import SteppedFlapjack.CrepToLoopSteps.ConditionShape
import Flapjack.Pancake.Semantics.LoopProps.EvaluateClockExact
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.LoopToWordSteps

/-- A compiled scalar expression preserves its value with an explicit clock
budget computed from the generated Loop prefix. Resetting the resulting clock
recovers the source-to-target state relation. -/
theorem scalar_correct_explicit {width : Nat} [NeZero width] {σ : Type}
    (e : CrepExpHOL width) (shape : CompiledScalar e) (source : CrepSemHOLState width σ)
    (v : HolWordLab width) (target : LoopSemStateFiniteExact width σ)
    (ctxt : CrepToLoopContextExact) (tmp : Nat) (live : NumSet)
    (code : List (HolLoopProg width)) (value : HolLoopExp width) (next : Nat) (outLive : NumSet)
    (compiled : compileExpHOLExact ctxt tmp live e = (code,value,next,outLive))
    (evalSource : evalCrepSemHOLExp source e = some v)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (fresh : ctxt.vmax < tmp) :
    ∃ post,
      evaluate (loopNestedSeqHOL code) {target with clock := target.clock + LoopSteps.structuralWeight (loopNestedSeqHOL code)} = (none,post) ∧
      LoopSemStateFiniteExact.eval post value = some (wlabWlocExact v) ∧
      crepToLoopStateRelExact source {post with clock := source.clock} ∧
      crepToLoopMemRelHOLExact source.memory post.memory source.memaddrs ∧
      crepToLoopGlobalsRelHOLExact source.globals post.globals ∧
      crepToLoopCodeRelExact ctxt source.code post.code ∧
      crepToLoopLocalsRelExact ctxt outLive source.locals post.locals := by
  obtain ⟨code0,value0,next0,live0,hcomp,branch,_⟩ := compiledScalar_prefix shape ctxt tmp live
  rw [compiled] at hcomp
  cases hcomp
  obtain ⟨extra,post,run,he,hs,hm,hg,hc,hl⟩ :=
    crepToLoop_comp_exp_preserves_eval source e v target ctxt tmp live code value next outLive
      ⟨evalSource,stateRel,memRel,globalsRel,codeRel,localsRel,compiled,fresh⟩
  have hshape := nestedSeq_branched code branch
  have consumed := LoopSteps.branchedProgram_clock_consumed hshape
    {target with clock := target.clock+extra} post none run
  have visits := LoopSteps.branchedProgram_structural_bound hshape {target with clock := target.clock+extra}
  have initial := stateRel.2.2.1
  have final := hs.2.2.1
  have bound : extra ≤ LoopSteps.structuralWeight (loopNestedSeqHOL code) := by
    simp only at consumed
    omega
  let delta := LoopSteps.structuralWeight (loopNestedSeqHOL code) - extra
  have shifted := evaluate_add_clock_eq _ _ _ _ delta run (by simp)
  refine ⟨{post with clock := post.clock+delta}, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have eq : target.clock + extra + delta = target.clock + LoopSteps.structuralWeight (loopNestedSeqHOL code) := by dsimp [delta]; omega
    simpa [eq] using shifted
  · simpa only [eval_upd_clock_eq] using he
  · simpa [crepToLoopStateRelExact, final] using hs
  · simpa using hm
  · simpa using hg
  · simpa using hc
  · simpa using hl
end SteppedFlapjack.CrepToLoopSteps
