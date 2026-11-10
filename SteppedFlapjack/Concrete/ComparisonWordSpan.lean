import SteppedFlapjack.Concrete.CountdownWordSpan
import SteppedFlapjack.Concrete.ComparisonLoopSpan
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.WordToWord
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps SteppedFlapjack.WordAllocSteps
variable {C : Type}
/-- Phase 2 clock budget and visit bound for the comparison fixture. -/
def comparisonLoopBudget : Nat := 138*(33+1)
def comparisonLoopVisits : Nat := 46*(33+comparisonLoopBudget+1)+8
/-- Actual two-function Crep and Word code for the straight-line branching fixture. -/
def comparisonCrepCode := twoPrograms (ofString "main") (entryName branchingHOL) branchCrepBody
def comparisonWordPrograms := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa comparisonCrepCode)
/-- Explicit optimized Word visit bound for the straight-line branching fixture. -/
def comparisonWordBound : Nat :=
  twoProgramWordBound riscvConfig.isa (ofString "main") (entryName branchingHOL)
    branchCrepBody comparisonLoopVisits phase3WordConfig riscvConfig
/-- The Word start state constructed from the Phase 2 branching state. -/
noncomputable def comparisonWordStarter (template : WordSemStateFiniteExact 64 C Unit) (frame : Nat) :=
  let pan := panSimpSourceState branching (clockedFixtureSource branching 6)
  let crep := crepStateFrom pan (branchingHOL)
  let timed := {crep with clock := crep.clock + comparisonLoopBudget}
  phase3Starter riscvConfig.isa timed comparisonCrepCode template fixtureHeapLength 64 frame
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The straight-line branching fixture returns through the actual optimized Word table
within its explicit code-derived visit bound. -/
theorem branching_wholeWord (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit)
    (template : WordSemStateFiniteExact 64 C Unit) (frame : Nat) :
    let pan := panSimpSourceState branching (clockedFixtureSource branching 6)
    let crep := crepStateFrom pan (branchingHOL)
    let starter := comparisonWordStarter template frame
    let target := WordSemStateFiniteExact.evaluate (.call none (some 64) [0] none)
      {starter with clock := 6*comparisonLoopVisits+1, code := sptFromAList (compile countdownRiscVBackend.wordToWordConf riscvConfig comparisonWordPrograms).2}
    ∃ (final : CrepSemHOLState 64 Unit) (post : LoopSemStateFiniteExact 64 Unit),
      evalCrepSemHOLProgExact crep branchCrepEntry = (some (.return [.word 7]),final) ∧
      crepToLoopStateRelExact final {post with clock := final.clock} ∧
      target.1 = some (.result (.loc 1 0) [.word 7]) ∧ target.2.ffi = post.ffi ∧
      WordSteps.steps (.call none (some 64) [0] none)
        {starter with clock := 6*comparisonLoopVisits+1, code := sptFromAList (compile countdownRiscVBackend.wordToWordConf riscvConfig comparisonWordPrograms).2} ≤ comparisonWordBound := by
  let pan := panSimpSourceState branching (clockedFixtureSource branching 6)
  let crep := crepStateFrom pan (branchingHOL)
  let timed := {crep with clock := crep.clock + comparisonLoopBudget}
  have code : crepPrograms (branchingHOL) = comparisonCrepCode := by
    simpa [comparisonCrepCode,twoPrograms,branchCrepBody] using branching_crep_code
  obtain ⟨_,_,final,post,crepRun,loopRun,loopBound,stateRel,_,_,_⟩ := branching_fixture_entry_loop riscvConfig.isa context primitive handler
  have heap : timed.topAddr = timed.baseAddr + 2*fixtureHeapLength := by
    simpa [timed,crep,pan] using fixture_heap branching 6 (branchingHOL)
  have loopEq : concreteDeclLoopState riscvConfig.isa timed comparisonCrepCode =
      {loopStateFrom riscvConfig.isa pan (branchingHOL) with
        clock := (loopStateFrom riscvConfig.isa pan (branchingHOL)).clock + comparisonLoopBudget} := by
    simp [timed,crep,pan,loopStateFrom,concreteDeclLoopState,code]
  have sourceRun : evaluate branchingLoopEntry (concreteDeclLoopState riscvConfig.isa timed comparisonCrepCode) =
      (some (.result [.word 7]),post) := by
    rw [loopEq]
    simpa [pan,comparisonLoopBudget] using loopRun
  have sourceBound : LoopSteps.steps branchingLoopEntry (concreteDeclLoopState riscvConfig.isa timed comparisonCrepCode) ≤ comparisonLoopVisits := by
    rw [loopEq]
    simpa [pan,comparisonLoopBudget,comparisonLoopVisits] using loopBound
  have span := twoProgram_wholeWord_span riscvConfig.isa (ofString "main") (entryName branchingHOL)
    branchCrepBody (Ne.symm (entryName_fresh (branchingHOL))) branching_scalar
    timed post [.word 7] comparisonLoopVisits template fixtureHeapLength frame
    countdownRiscVBackend.wordToWordConf riscvConfig (phase3Starter riscvConfig.isa timed (comparisonCrepCode) template fixtureHeapLength 64 frame).memory heap sourceRun sourceBound
  obtain ⟨_,wordPost,wordResult,relation,result,ffi,bound⟩ := span
  simp only [LoopToWord.CompileCorrect.resultCase] at relation
  refine ⟨final,post,?_,stateRel,?_,?_,?_⟩
  · simpa [crep,pan] using crepRun
  · simpa [comparisonWordStarter,comparisonCrepCode,comparisonWordPrograms,crep,timed,pan,relation.2.1] using result
  · simpa [comparisonWordStarter,comparisonCrepCode,comparisonWordPrograms,crep,timed,pan] using ffi
  · simpa only [comparisonWordBound,phase3WordConfig_eq,comparisonWordStarter,comparisonCrepCode,comparisonWordPrograms,crep,timed,pan] using bound
end SteppedFlapjack.Concrete
