import SteppedFlapjack.CrepToLoopSteps.ScalarCorrect
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Assembly
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.LoopToWordSteps

/-- A loop-free compiled program runs with a code-derived explicit clock budget. -/
theorem branch_compiler_explicit {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (source sourcePost : CrepSemHOLState width σ)
    (result : Option (CrepResultHOLExact width)) (target : LoopSemStateFiniteExact width σ)
    (ctxt : CrepToLoopContextExact) (live : NumSet)
    (shape : BranchedProgram (compileHOLExact ctxt live p))
    (run : evalCrepSemHOLProgExact source p = (result,sourcePost))
    (nonerror : result ≠ some .error) (nontimeout : resultToLoop result ≠ some .timeOut)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    ∃ post,
      evaluate (compileHOLExact ctxt live p)
        {target with clock := target.clock + LoopSteps.structuralWeight (compileHOLExact ctxt live p)} =
          (resultToLoop result,post) ∧
      crepToLoopStateRelExact sourcePost {post with clock := sourcePost.clock} ∧
      crepToLoopMemRelHOLExact sourcePost.memory post.memory sourcePost.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourcePost.globals post.globals ∧
      crepToLoopCodeRelExact ctxt sourcePost.code post.code ∧
      localsResultRel ctxt live result sourcePost post ∧
      LoopSteps.steps (compileHOLExact ctxt live p)
        {target with clock := target.clock + LoopSteps.structuralWeight (compileHOLExact ctxt live p)} ≤
          LoopSteps.structuralWeight (compileHOLExact ctxt live p) := by
  obtain ⟨extra,res,post,targetRun,postRel,postMem,postGlobal,postCode,resEq,postLocals⟩ :=
    crepToLoop_ncompile_correct p source result sourcePost target ctxt live
      ⟨run,nonerror,stateRel,memRel,globalsRel,codeRel,localsRel⟩
  subst res
  have consumed := LoopSteps.branchedProgram_clock_consumed shape
    {target with clock := target.clock+extra} post (resultToLoop result) targetRun
  have visits := LoopSteps.branchedProgram_structural_bound shape {target with clock := target.clock+extra}
  have sourceClock := evalCrepSemHOLProgExact_clock_le source p
  rw [run] at sourceClock
  have initial := stateRel.2.2.1
  have final := postRel.2.2.1
  have bound : extra ≤ LoopSteps.structuralWeight (compileHOLExact ctxt live p) := by
    simp only at consumed sourceClock
    omega
  let delta := LoopSteps.structuralWeight (compileHOLExact ctxt live p) - extra
  have shifted := evaluate_add_clock_eq _ _ _ _ delta targetRun nontimeout
  refine ⟨{post with clock := post.clock+delta}, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have eq : target.clock + extra + delta = target.clock + LoopSteps.structuralWeight (compileHOLExact ctxt live p) := by dsimp [delta]; omega
    simpa [eq] using shifted
  · simpa [crepToLoopStateRelExact,final] using postRel
  · simpa using postMem
  · simpa using postGlobal
  · simpa using postCode
  · cases result with
    | none => exact postLocals
    | some r => cases r <;> exact postLocals
  · exact LoopSteps.branchedProgram_structural_bound shape _
end SteppedFlapjack.CrepToLoopSteps
