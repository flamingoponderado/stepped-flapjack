import SteppedFlapjack.CrepToLoopSteps.Branch
import SteppedFlapjack.CrepToLoopSteps.ScalarBranch
import SteppedFlapjack.LoopLiveSteps.ClockBound
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Assembly
import SteppedFlapjack.LoopSteps.ClockConsumption

/-! A syntax bound on the extra Loop clock for a compiled Crep branch program. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- Loop-free bodies from the original branch fragment or the full scalar
fragment. Both alternatives compile to a loop-free Loop program. -/
inductive LoopFreeCrep {width : Nat} [NeZero width] : CrepProgHOL width → Prop
  | branch {p} : BranchProgram p → LoopFreeCrep p
  | scalar {p} : ScalarProgram p → scalarNoWhile p = true → LoopFreeCrep p

instance {width : Nat} [NeZero width] {p : CrepProgHOL width} :
    Coe (BranchProgram p) (LoopFreeCrep p) where
  coe := LoopFreeCrep.branch

theorem compile_loopFreeCrep {width : Nat} [NeZero width] {p : CrepProgHOL width}
    (shape : LoopFreeCrep p) (ctxt : CrepToLoopContextExact) (live : NumSet) :
    SteppedFlapjack.LoopToWordSteps.BranchedProgram (compileHOLExact ctxt live p) := by
  cases shape with
  | branch h => exact compile_branchProgram h ctxt live
  | scalar h free => exact SteppedFlapjack.LoopLiveSteps.branch_branched (compile_scalar_branch h free ctxt live)

theorem compile_loopFreeCrep_select {width : Nat} [NeZero width] {p : CrepProgHOL width}
    (shape : LoopFreeCrep p) (ctxt : CrepToLoopContextExact) (live : NumSet) :
    SteppedFlapjack.LoopToWordSteps.LoopSelectProgram (compileHOLExact ctxt live p) := by
  cases shape with
  | branch h => exact compile_branchProgram_select h ctxt live
  | scalar h free => exact SteppedFlapjack.LoopToWordSteps.loopBranch_select (compile_scalar_branch h free ctxt live)

/-- Every clock witness preserving the final state relation is bounded by the
compiled body size, independently of the initial clock. -/
theorem branchProgram_extraClock_bound {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (shape : LoopFreeCrep p)
    (source sourceFinal : CrepSemHOLState width σ) (result : Option (CrepResultHOLExact width))
    (target targetFinal : LoopSemStateFiniteExact width σ) (targetResult : Option (LoopResultExact width))
    (ctxt : CrepToLoopContextExact) (live : NumSet) (extra : Nat)
    (run : evalCrepSemHOLProgExact source p = (result,sourceFinal))
    (stateRel : crepToLoopStateRelExact source target)
    (targetRun : evaluate (compileHOLExact ctxt live p) {target with clock := target.clock + extra} =
      (targetResult,targetFinal))
    (finalRel : crepToLoopStateRelExact sourceFinal targetFinal) :
    extra ≤ sizeOf (compileHOLExact ctxt live p) := by
  have srcClock := evalCrepSemHOLProgExact_clock_le source p
  rw [run] at srcClock
  have consumed := LoopSteps.branchedProgram_clock_consumed (compile_loopFreeCrep shape ctxt live)
    {target with clock := target.clock + extra} targetFinal targetResult targetRun
  have visits := LoopSteps.branchedProgram_static_bound (compile_loopFreeCrep shape ctxt live)
    {target with clock := target.clock + extra}
  have initial := stateRel.2.2.1
  have final := finalRel.2.2.1
  simp only at srcClock consumed
  omega

/-- The compiler correctness witness for a branch program has a bounded extra
clock as well as the existing actual-visit bound. -/
theorem branchProgram_correct_with_bounded_extra {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (shape : LoopFreeCrep p)
    (source sourceFinal : CrepSemHOLState width σ) (result : Option (CrepResultHOLExact width))
    (target : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (live : NumSet)
    (run : evalCrepSemHOLProgExact source p = (result,sourceFinal)) (nonerror : result ≠ some .error)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    ∃ extra targetResult targetFinal,
      evaluate (compileHOLExact ctxt live p) {target with clock := target.clock + extra} = (targetResult,targetFinal) ∧
      crepToLoopStateRelExact sourceFinal targetFinal ∧
      crepToLoopMemRelHOLExact sourceFinal.memory targetFinal.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals targetFinal.globals ∧
      crepToLoopCodeRelExact ctxt sourceFinal.code targetFinal.code ∧
      targetResult = resultToLoop result ∧ localsResultRel ctxt live result sourceFinal targetFinal ∧
      LoopSteps.steps (compileHOLExact ctxt live p) {target with clock := target.clock + extra} ≤
        sizeOf (compileHOLExact ctxt live p) * CrepSteps.steps p source ∧
      extra ≤ sizeOf (compileHOLExact ctxt live p) := by
  obtain ⟨extra,targetResult,targetFinal,he,hs,hm,hg,hc,hr,hl⟩ :=
    crepToLoop_ncompile_correct p source result sourceFinal target ctxt live
      ⟨run,nonerror,stateRel,memRel,globalsRel,codeRel,localsRel⟩
  have static := LoopSteps.branchedProgram_static_bound (compile_loopFreeCrep shape ctxt live)
    {target with clock := target.clock+extra}
  have positive := CrepSteps.steps_pos p source
  have hsteps : LoopSteps.steps (compileHOLExact ctxt live p) {target with clock := target.clock+extra} ≤
      sizeOf (compileHOLExact ctxt live p) * CrepSteps.steps p source := by nlinarith
  exact ⟨extra,targetResult,targetFinal,he,hs,hm,hg,hc,hr,hl,hsteps,
    branchProgram_extraClock_bound p shape source sourceFinal result target targetFinal targetResult
      ctxt live extra run stateRel he hs⟩

end SteppedFlapjack.CrepToLoopSteps
