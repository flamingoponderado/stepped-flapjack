import SteppedFlapjack.Concrete.WitnessLoopCode
import SteppedFlapjack.CrepToLoopSteps.BranchExplicit
import SteppedFlapjack.CrepToLoopSteps.ScalarLoopConsumption
import SteppedFlapjack.CrepToLoopSteps.ScalarExecutable
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Encoders.Asm SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps

/-- The generated comparison body takes two Crep visits and the compiled Loop
body runs with an explicit 23-unit clock and a concrete visit bound. -/
theorem branching_body_loop {σ : Type} (arch : AsmArchitecture) (source : PanSemStateFiniteExact 64 σ) :
    let crep := crepStateFrom source branchingHOL
    let target := loopStateFrom arch source branchingHOL
    let ctxt := witnessLoopContext arch branchingHOL
    let code := compileHOLExact ctxt .ln branchCrepBody
    CrepSteps.steps branchCrepBody crep = 2 ∧
    ∃ post,
      evaluate code {target with clock := target.clock+23} = (some (.result [.word 7]),post) ∧
      LoopSteps.steps code {target with clock := target.clock+23} ≤ 23 ∧
      evaluate (optimiseHOL code) {target with clock := target.clock+23} = (some (.result [.word 7]),post) ∧
      LoopSteps.steps (optimiseHOL code) {target with clock := target.clock+23} ≤ sizeOf (optimiseScalar code) * 47 := by
  let crep := crepStateFrom source branchingHOL
  let target := loopStateFrom arch source branchingHOL
  let ctxt := witnessLoopContext arch branchingHOL
  let code := compileHOLExact ctxt .ln branchCrepBody
  have shape : ScalarProgram branchCrepBody :=
    .ite (.cmp .lower (.direct (.const _)) (.direct (.const _)))
      (.ret (.direct (.const _))) (.ret (.direct (.const _)))
  have free : scalarNoWhile branchCrepBody = true := by rfl
  have rel := loopStateFrom_relations arch source branchingHOL
  have codeLocals := branching_loop_code_locals arch source
  have bounded := branch_compiler_explicit branchCrepBody crep crep.emptyLocals
    (some (.return [.word 7])) target ctxt .ln shape free (branchCrepBody_run crep)
    (by simp) (by simp [resultToLoop]) rel.1 rel.2.1 rel.2.2 codeLocals.1 codeLocals.2
  have cost : LoopSteps.structuralWeight code = 23 := by
    simp [code,ctxt,witnessLoopContext,branchCrepBody,compileHOLExact,compileExpHOLExact,
      compileExpsHOLExact,progIfHOLExact,loopNestedSeqHOL,LoopSteps.structuralWeight,genTemps,mkCtxtExact]
  obtain ⟨post,run,_,_,_,_,_,bound⟩ := bounded
  have run23 : evaluate code {target with clock := target.clock+23} = (some (.result [.word 7]),post) := by
    simpa [code,cost,resultToLoop,wlabWlocExact] using run
  have bound23 : LoopSteps.steps code {target with clock := target.clock+23} ≤ 23 := by
    simpa [code,cost] using bound
  have loopShape := compile_scalar_program shape ctxt .ln
  obtain ⟨optRun,_,optBound⟩ := scalarLoop_optimise_source_steps loopShape _ post _ run23 (.return _)
  refine ⟨branchCrepBody_steps crep,post,run23,bound23,optRun,?_⟩
  change LoopSteps.steps (optimiseHOL code) _ ≤ sizeOf (optimiseHOL code) * (2 * LoopSteps.steps code _ + 1) at optBound
  rw [optimiseScalar_eq loopShape]
  exact optBound.trans (Nat.mul_le_mul_left _ (by omega))

end SteppedFlapjack.Concrete
