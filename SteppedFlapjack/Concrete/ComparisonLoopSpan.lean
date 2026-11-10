import SteppedFlapjack.Concrete.WitnessWeights
import SteppedFlapjack.Concrete.CountedApplications

/-! The comparison witness through the optimized Loop entry. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.CrepToLoopSteps

/-- The actual generated optimized entry executes with a source-derived
closed-form bound for the comparison witness. -/
theorem branching_fixture_entry_loop (arch : AsmArchitecture)
    (memory : BitVec 64 → WordLocW 64)
    (memoryRel : let source := panSimpSourceState branching (clockedFixtureSource branching 6)
      crepToLoopMemRelHOLExact (crepStateFrom source branchingHOL).memory memory (crepStateFrom source branchingHOL).memaddrs)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    let source := panSimpSourceState branching (clockedFixtureSource branching 6)
    let crep := crepStateFrom source branchingHOL
    let target := {(loopStateFrom arch source branchingHOL) with memory := memory}
    let ctxt := witnessLoopContext arch branchingHOL
    let budget := 138*(33+1)
    CrepSteps.steps branchCrepEntry crep ≤ 33 ∧
    (64,[],branchingLoopEntry) ∈ compileProgHOLExact arch (crepPrograms branchingHOL) ∧
    ∃ final post,
      evalCrepSemHOLProgExact crep branchCrepEntry = (some (.return [.word 7]),final) ∧
      evaluate branchingLoopEntry {target with clock := target.clock+budget} = (some (.result [.word 7]),post) ∧
      LoopSteps.steps branchingLoopEntry {target with clock := target.clock+budget} ≤
        46*(33+budget+1)+8 ∧
      crepToLoopStateRelExact final {post with clock := final.clock} ∧
      crepToLoopMemRelHOLExact final.memory post.memory final.memaddrs ∧
      crepToLoopGlobalsRelHOLExact final.globals post.globals ∧
      crepToLoopCodeRelExact ctxt final.code post.code := by
  let source := panSimpSourceState branching (clockedFixtureSource branching 6)
  let crep := crepStateFrom source branchingHOL
  let target := {(loopStateFrom arch source branchingHOL) with memory := memory}
  let ctxt := witnessLoopContext arch branchingHOL
  let name := entryName branchingHOL
  obtain ⟨final,run,bound⟩ := branching_counted_fixture context primitive handler
  have nonzero : crep.clock ≠ 0 := by
    simp [crep,source,crepStateFrom,PanToCrepSteps.concreteDeclCrepState,panSimpSourceState,
      clockedFixtureSource,loweredStateFrom,PanToCrepSteps.noGlobalsLoweredPreCall]
  have found : crep.code.lookup name = some ([],branchCrepBody) := by
    have h := generated_callee_lookup branchingHOL branchCrepBody branching_crep_code
    simpa [crep,name,crepState,crepStateFrom,PanToCrepSteps.concreteDeclCrepState] using h
  have label : findLabExact ctxt name = 65 := by
    have fresh := Ne.symm (entryName_fresh branchingHOL)
    have h := twoPrograms_callee_label arch (ofString "main") name branchCrepBody fresh
    simpa [ctxt,name,witnessLoopContext,branching_crep_code,twoPrograms,branchCrepBody] using h
  have originalRel := loopStateFrom_relations arch source branchingHOL
  have rel : crepToLoopStateRelExact crep target ∧ crepToLoopMemRelHOLExact crep.memory target.memory crep.memaddrs ∧
      crepToLoopGlobalsRelHOLExact crep.globals target.globals := ⟨originalRel.1,memoryRel,originalRel.2.2⟩
  have codeLocals := branching_loop_code_locals arch source
  have compiled := branching_loop_entry_code arch
  have result := generatedScalar_entry_explicit ctxt name branchCrepBody branching_scalar crep final target [.word 7] 33
    nonzero found run bound rel.1 rel.2.1 rel.2.2 codeLocals.1 codeLocals.2 label
  obtain ⟨post,entry,steps,finalState,finalMem,finalGlobals,finalCode⟩ := result
  simp only [ctxt,comparison_optimized_weight] at entry steps
  refine ⟨bound,compiled,final,post,run,?_,?_,finalState,finalMem,finalGlobals,finalCode⟩
  · simpa [ctxt,name,target,crep,branchCrepBody,wlabWlocExact] using entry
  · simpa [ctxt,name,target,crep,branchCrepBody] using steps
end SteppedFlapjack.Concrete
