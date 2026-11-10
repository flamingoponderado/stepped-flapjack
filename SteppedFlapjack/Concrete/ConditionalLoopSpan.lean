import SteppedFlapjack.Concrete.WitnessWeights
import SteppedFlapjack.Concrete.CountedApplications

/-! The conditional-loop witness through the optimized Loop entry. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.CrepToLoopSteps

def conditionalLoopBody : CrepProgHOL 64 :=
  .ite (.cmp .equal (.var 1) (.const 2))
    (.seq (.assign 1 (.const 1)) .skip) (.seq (.assign 1 (.const 0)) .skip)

/-- The actual generated optimized entry executes with a source-derived
closed-form bound for the witness that takes both conditional branches. -/
theorem branchingLoop_fixture_entry_loop (arch : AsmArchitecture)
    (memory : BitVec 64 → WordLocW 64)
    (memoryRel : let source := panSimpSourceState branchingLoop (clockedFixtureSource branchingLoop 23)
      crepToLoopMemRelHOLExact (crepStateFrom source (progToHOL branchingLoop)).memory memory (crepStateFrom source (progToHOL branchingLoop)).memaddrs)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    let source := panSimpSourceState branchingLoop (clockedFixtureSource branchingLoop 23)
    let crep := crepStateFrom source (progToHOL branchingLoop)
    let target := {(loopStateFrom arch source (progToHOL branchingLoop)) with memory := memory}
    let ctxt := witnessLoopContext arch (progToHOL branchingLoop)
    let budget := 240*(388+1)
    CrepSteps.steps branchingLoopCrepEntry crep ≤ 388 ∧
    (64,[],branchingLoopEntry) ∈ compileProgHOLExact arch (crepPrograms (progToHOL branchingLoop)) ∧
    ∃ final post,
      evalCrepSemHOLProgExact crep branchingLoopCrepEntry = (some (.return [.word 7]),final) ∧
      evaluate branchingLoopEntry {target with clock := target.clock+budget} = (some (.result [.word 7]),post) ∧
      LoopSteps.steps branchingLoopEntry {target with clock := target.clock+budget} ≤
        80*(388+budget+1)+8 ∧
      crepToLoopStateRelExact final {post with clock := final.clock} ∧
      crepToLoopMemRelHOLExact final.memory post.memory final.memaddrs ∧
      crepToLoopGlobalsRelHOLExact final.globals post.globals ∧
      crepToLoopCodeRelExact ctxt final.code post.code := by
  let source := panSimpSourceState branchingLoop (clockedFixtureSource branchingLoop 23)
  let crep := crepStateFrom source (progToHOL branchingLoop)
  let target := {(loopStateFrom arch source (progToHOL branchingLoop)) with memory := memory}
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
  have originalRel := loopStateFrom_relations arch source (progToHOL branchingLoop)
  have rel : crepToLoopStateRelExact crep target ∧ crepToLoopMemRelHOLExact crep.memory target.memory crep.memaddrs ∧
      crepToLoopGlobalsRelHOLExact crep.globals target.globals := ⟨originalRel.1,memoryRel,originalRel.2.2⟩
  have codeLocals := branchingLoop_loop_code_locals arch source
  have compiled : (64,[],branchingLoopEntry) ∈ compileProgHOLExact arch (crepPrograms (progToHOL branchingLoop)) := by
    rw [branchingLoop_loop_code]
    exact twoLoopPrograms_entry_code arch _ _ _ (Ne.symm (entryName_fresh (progToHOL branchingLoop)))
  have result := generatedScalar_entry_explicit ctxt name branchingLoopCrepBody branchingLoop_scalar crep final target [.word 7] 388
    nonzero found run bound rel.1 rel.2.1 rel.2.2 codeLocals.1 codeLocals.2 label
  obtain ⟨post,entry,steps,finalState,finalMem,finalGlobals,finalCode⟩ := result
  simp only [ctxt,conditional_optimized_weight] at entry steps
  refine ⟨bound,compiled,final,post,run,?_,?_,finalState,finalMem,finalGlobals,finalCode⟩
  · simpa [ctxt,name,target,crep,conditionalLoopBody,branchingLoopCrepBody,wlabWlocExact] using entry
  · simpa [ctxt,name,target,crep,conditionalLoopBody,branchingLoopCrepBody] using steps
end SteppedFlapjack.Concrete
