import SteppedFlapjack.Concrete.DeclarationEntry
import SteppedFlapjack.Concrete.CountedApplications

/-! The conditional-loop witness through the optimized Loop entry. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.CrepToLoopSteps

def conditionalLoopBody : CrepProgHOL 64 :=
  .ite (.cmp .equal (.var 1) (.const 2))
    (.seq (.assign 1 (.const 1)) .skip) (.seq (.assign 1 (.const 0)) .skip)

theorem conditionalLoop_body_shape : LoopFreeCrep conditionalLoopBody := by
  apply LoopFreeCrep.scalar
    (.ite (.cmp .equal (.direct (.var 1)) (.direct (.const 2)))
      (.seq (.assign 1 (.direct (.const 1))) .skip)
      (.seq (.assign 1 (.direct (.const 0))) .skip))
  rfl

theorem conditionalLoop_scalar : ScalarProgram branchingLoopCrepBody := by
  exact .dec 1 (.direct (.const 2)) (.seq
    (.while (.direct (.var 1)) (.ite (.cmp .equal (.direct (.var 1)) (.direct (.const 2)))
      (.seq (.assign 1 (.direct (.const 1))) .skip) (.seq (.assign 1 (.direct (.const 0))) .skip)))
    (.ret (.direct (.const 7))))

/-- The actual generated optimized entry executes with a source-derived
closed-form bound for the witness that takes both conditional branches. -/
theorem branchingLoop_fixture_entry_loop (arch : AsmArchitecture)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    let source := panSimpSourceState branchingLoop (clockedFixtureSource branchingLoop 23)
    let crep := crepStateFrom source (progToHOL branchingLoop)
    let target := loopStateFrom arch source (progToHOL branchingLoop)
    let ctxt := witnessLoopContext arch (progToHOL branchingLoop)
    let c := ctxtFcExact ctxt.target ctxt.funcs [] []
    let bc := {c with vars := c.vars.updateEq (1,c.vmax+1), vmax := c.vmax+1}
    let bl := sptInsert (c.vmax+1) () .ln
    let tail : CrepProgHOL 64 := .return [.const 7]
    let factor := 1 + (1 + sizeOf (compileHOLExact bc bl (.while (.var 1) conditionalLoopBody))) *
      (sizeOf (compileHOLExact bc bl conditionalLoopBody)+4) + sizeOf (compileHOLExact bc bl tail)
    let budget := (factor+4)*(388+1)
    let code := compileHOLExact c .ln branchingLoopCrepBody
    CrepSteps.steps branchingLoopCrepEntry crep ≤ 388 ∧
    (64,[],branchingLoopEntry) ∈ compileProgHOLExact arch (crepPrograms (progToHOL branchingLoop)) ∧
    ∃ post,
      evaluate branchingLoopEntry {target with clock := target.clock+2*budget} = (some (.result [.word 7]),post) ∧
      LoopSteps.steps branchingLoopEntry {target with clock := target.clock+2*budget} ≤
        sizeOf (optimiseScalar code)*(2*budget+1)+8 := by
  let source := panSimpSourceState branchingLoop (clockedFixtureSource branchingLoop 23)
  let crep := crepStateFrom source (progToHOL branchingLoop)
  let target := loopStateFrom arch source (progToHOL branchingLoop)
  let ctxt := witnessLoopContext arch (progToHOL branchingLoop)
  let name := entryName (progToHOL branchingLoop)
  obtain ⟨final,run,bound⟩ := branching_loop_counted_fixture context primitive handler
  have nonzero : crep.clock ≠ 0 := by
    simp [crep,source,crepStateFrom,PanToCrepSteps.concreteDeclCrepState,panSimpSourceState,
      clockedFixtureSource,loweredStateFrom,PanToCrepSteps.noGlobalsLoweredPreCall]
  have found : crep.code.lookup name = some ([],branchingLoopCrepBody) := by
    have h := generated_callee_lookup (progToHOL branchingLoop) branchingLoopCrepBody branchingLoop_crep_code
    simpa [crep,name,crepState,crepStateFrom,PanToCrepSteps.concreteDeclCrepState] using h
  have label : findLabExact ctxt name = 65 := by
    have fresh := Ne.symm (entryName_fresh (progToHOL branchingLoop))
    have h := twoPrograms_callee_label arch (ofString "main") name branchingLoopCrepBody fresh
    simpa [ctxt,witnessLoopContext,branchingLoop_crep_code,twoPrograms] using h
  have rel := loopStateFrom_relations arch source (progToHOL branchingLoop)
  have codeLocals := branchingLoop_loop_code_locals arch source
  have shape : ScalarProgram (.dec 1 (.const 2) (.seq (.while (.var 1) conditionalLoopBody) (.return [.const 7]))) := conditionalLoop_scalar
  have compiled : (64,[],branchingLoopEntry) ∈ compileProgHOLExact arch (crepPrograms (progToHOL branchingLoop)) := by
    rw [branchingLoop_loop_code]
    exact twoLoopPrograms_entry_code arch _ _ _ (Ne.symm (entryName_fresh (progToHOL branchingLoop)))
  have result := generatedDecl_entry_explicit ctxt name 1 (.const 2) (.var 1) conditionalLoopBody (.return [.const 7])
    (.const 2) (.var 1) conditionalLoop_body_shape (.branch (.expr (.returnOne (.const 7)))) shape crep target [.word 7] 388
    nonzero found ⟨final,run⟩ bound rel.1 rel.2.1 rel.2.2 codeLocals.1 codeLocals.2 label
  obtain ⟨post,entry,steps⟩ := result
  refine ⟨bound,compiled,post,?_,?_⟩
  · simpa [ctxt,name,target,crep,conditionalLoopBody,branchingLoopCrepBody,wlabWlocExact] using entry
  · simpa [ctxt,name,target,crep,conditionalLoopBody,branchingLoopCrepBody] using steps
end SteppedFlapjack.Concrete
