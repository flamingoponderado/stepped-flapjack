import SteppedFlapjack.Concrete.CountdownWordSpan
import SteppedFlapjack.Concrete.ConditionalLoopSpan
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.WordToWord
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps SteppedFlapjack.WordAllocSteps
variable {C : Type}
/-- Phase 2 clock budget and visit bound for the conditional-loop fixture. -/
def branchLoopBudget : Nat := 240*(388+1)
def branchLoopVisits : Nat := 80*(388+branchLoopBudget+1)+8
/-- Actual two-function Crep and Word code for the branching fixture. -/
def branchCrepCode := twoPrograms (ofString "main") (entryName (progToHOL branchingLoop)) branchingLoopCrepBody
def branchWordPrograms := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa branchCrepCode)
/-- Explicit optimized Word visit bound for the branching fixture. -/
def branchWordBound : Nat :=
  twoProgramWordBound riscvConfig.isa (ofString "main") (entryName (progToHOL branchingLoop))
    branchingLoopCrepBody branchLoopVisits phase3WordConfig riscvConfig
/-- The Word start state constructed from the Phase 2 branching state. -/
noncomputable def branchWordStarter (template : WordSemStateFiniteExact 64 C Unit) (frame : Nat) :=
  let pan := panSimpSourceState branchingLoop (clockedFixtureSource branchingLoop 23)
  let crep := crepStateFrom pan (progToHOL branchingLoop)
  let timed := {crep with clock := crep.clock + branchLoopBudget}
  phase3Starter riscvConfig.isa timed branchCrepCode template fixtureHeapLength 64 frame
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The branching fixture returns through the actual optimized Word table
within its explicit code-derived visit bound. -/
theorem branchingLoop_wholeWord (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit)
    (template : WordSemStateFiniteExact 64 C Unit) (frame : Nat) :
    let pan := panSimpSourceState branchingLoop (clockedFixtureSource branchingLoop 23)
    let crep := crepStateFrom pan (progToHOL branchingLoop)
    let starter := branchWordStarter template frame
    let target := WordSemStateFiniteExact.evaluate (.call none (some 64) [0] none)
      {starter with clock := 6*branchLoopVisits+1, code := sptFromAList (compile countdownRiscVBackend.wordToWordConf riscvConfig branchWordPrograms).2}
    ∃ (final : CrepSemHOLState 64 Unit) (post : LoopSemStateFiniteExact 64 Unit),
      evalCrepSemHOLProgExact crep branchingLoopCrepEntry = (some (.return [.word 7]),final) ∧
      crepToLoopStateRelExact final {post with clock := final.clock} ∧
      target.1 = some (.result (.loc 1 0) [.word 7]) ∧ target.2.ffi = post.ffi ∧
      WordSteps.steps (.call none (some 64) [0] none)
        {starter with clock := 6*branchLoopVisits+1, code := sptFromAList (compile countdownRiscVBackend.wordToWordConf riscvConfig branchWordPrograms).2} ≤ branchWordBound := by
  let pan := panSimpSourceState branchingLoop (clockedFixtureSource branchingLoop 23)
  let crep := crepStateFrom pan (progToHOL branchingLoop)
  let timed := {crep with clock := crep.clock + branchLoopBudget}
  have code : crepPrograms (progToHOL branchingLoop) = branchCrepCode := by
    simpa [branchCrepCode,twoPrograms] using branchingLoop_crep_code
  obtain ⟨_,_,final,post,crepRun,loopRun,loopBound,stateRel,_,_,_⟩ := branchingLoop_fixture_entry_loop riscvConfig.isa context primitive handler
  have heap : timed.topAddr = timed.baseAddr + 2*fixtureHeapLength := by
    simpa [timed,crep,pan] using fixture_heap branchingLoop 23 (progToHOL branchingLoop)
  have loopEq : concreteDeclLoopState riscvConfig.isa timed branchCrepCode =
      {loopStateFrom riscvConfig.isa pan (progToHOL branchingLoop) with
        clock := (loopStateFrom riscvConfig.isa pan (progToHOL branchingLoop)).clock + branchLoopBudget} := by
    simp [timed,crep,pan,loopStateFrom,concreteDeclLoopState,code]
  have sourceRun : evaluate branchingLoopEntry (concreteDeclLoopState riscvConfig.isa timed branchCrepCode) =
      (some (.result [.word 7]),post) := by
    rw [loopEq]
    simpa [pan,branchLoopBudget] using loopRun
  have sourceBound : LoopSteps.steps branchingLoopEntry (concreteDeclLoopState riscvConfig.isa timed branchCrepCode) ≤ branchLoopVisits := by
    rw [loopEq]
    simpa [pan,branchLoopBudget,branchLoopVisits] using loopBound
  have span := twoProgram_wholeWord_span riscvConfig.isa (ofString "main") (entryName (progToHOL branchingLoop))
    branchingLoopCrepBody (Ne.symm (entryName_fresh (progToHOL branchingLoop))) branchingLoop_scalar
    timed post [.word 7] branchLoopVisits template fixtureHeapLength frame
    countdownRiscVBackend.wordToWordConf riscvConfig (phase3Starter riscvConfig.isa timed (branchCrepCode) template fixtureHeapLength 64 frame).memory heap sourceRun sourceBound
  obtain ⟨_,wordPost,wordResult,relation,result,ffi,bound⟩ := span
  simp only [LoopToWord.CompileCorrect.resultCase] at relation
  refine ⟨final,post,?_,stateRel,?_,?_,?_⟩
  · simpa [crep,pan] using crepRun
  · simpa [branchWordStarter,branchCrepCode,branchWordPrograms,crep,timed,pan,relation.2.1] using result
  · simpa [branchWordStarter,branchCrepCode,branchWordPrograms,crep,timed,pan] using ffi
  · simpa only [branchWordBound,phase3WordConfig_eq,branchWordStarter,branchCrepCode,branchWordPrograms,crep,timed,pan] using bound
end SteppedFlapjack.Concrete
