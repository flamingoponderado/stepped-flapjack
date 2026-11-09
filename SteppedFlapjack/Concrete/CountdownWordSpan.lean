import SteppedFlapjack.Concrete.WordSpan
import SteppedFlapjack.Concrete.CountdownLoopSpan
import Flapjack.Compiler.Encoders.RiscV.Target
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.WordToWord
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps SteppedFlapjack.WordAllocSteps
variable {C : Type}
/-- Heap length corresponding to the init-e-shaped source fixture. -/
def fixtureHeapLength : BitVec 64 := 0x39efffef4

/-- The fixed source fixture satisfies the Word heap-length equation. -/
theorem fixture_heap (program : Prog (RiscV.Word 64)) (fuel : Nat) (body : ProgHOL 64) :
    let source := crepStateFrom (panSimpSourceState program (clockedFixtureSource program fuel)) body
    source.topAddr = source.baseAddr + 2 * fixtureHeapLength := by
  change heapTop = heapBase + 2 * fixtureHeapLength
  decide

/-- Phase 2 clock budget and Loop visit bound for the countdown fixture. -/
def countdownLoopBudget (n : Nat) : Nat := 156*(3 + 8*(6*n+18)+1)
def countdownLoopVisits (n : Nat) : Nat := 52*(3 + 8*(6*n+18)+countdownLoopBudget n+1)+8

/-- The exact two-function countdown frontend emitted by Phase 1. -/
def phase3CountdownCrepBody (n : Nat) : CrepProgHOL 64 := naturalCountdownCrepBody (BitVec.ofNat 64 n)
def countdownCrepCode (n : Nat) := twoPrograms (ofString "main") (entryName (naturalCountdownHOL n)) (phase3CountdownCrepBody n)
def countdownWordPrograms (n : Nat) := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (countdownCrepCode n))
/-- The explicit optimized Word bound, computed from the compiled functions. -/
noncomputable def countdownWordBound (n : Nat) : Nat :=
  twoProgramWordBound riscvConfig.isa (ofString "main") (entryName (naturalCountdownHOL n))
    (phase3CountdownCrepBody n) (countdownLoopVisits n) countdownRiscVBackend.wordToWordConf riscvConfig

/-- The Word start state constructed from the Phase 2 countdown state. -/
noncomputable def countdownWordStarter (n : Nat) (template : WordSemStateFiniteExact 64 C Unit) (frame : Nat) :=
  let pan := panSimpSourceState (countdown n) (clockedFixtureSource (countdown n) (6*n+9))
  let crep := crepStateFrom pan (naturalCountdownHOL n)
  let timed := {crep with clock := crep.clock + countdownLoopBudget n}
  phase3Starter riscvConfig.isa timed (countdownCrepCode n) template fixtureHeapLength 64 frame

/-- The countdown Phase 2 run reaches the actual optimized Word start call
with matching return and events and an explicit code-derived visit bound. -/
theorem countdown_wholeWord (n : Nat) (range : n < 2^64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit)
    (template : WordSemStateFiniteExact 64 C Unit) (frame : Nat) :
    let starter := countdownWordStarter n template frame
    let target := WordSemStateFiniteExact.evaluate (.call none (some 64) [0] none)
      {starter with clock := 6*countdownLoopVisits n+1, code := sptFromAList (compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2}
    ∃ post : LoopSemStateFiniteExact 64 Unit,
      target.1 = some (.result (.loc 1 0) [.word 0]) ∧ target.2.ffi = post.ffi ∧
      WordSteps.steps (.call none (some 64) [0] none)
        {starter with clock := 6*countdownLoopVisits n+1, code := sptFromAList (compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2} ≤
        countdownWordBound n := by
  let pan := panSimpSourceState (countdown n) (clockedFixtureSource (countdown n) (6*n+9))
  let crep := crepStateFrom pan (naturalCountdownHOL n)
  let timed := {crep with clock := crep.clock + countdownLoopBudget n}
  have code : crepPrograms (naturalCountdownHOL n) = countdownCrepCode n := by
    simpa [countdownCrepCode,phase3CountdownCrepBody,twoPrograms] using natural_countdown_crep_code n
  obtain ⟨final,post,_,_,loopRun,loopBound,_,_,_,_⟩ := countdown_fixture_entry_loop riscvConfig.isa n range context primitive handler
  have heap : timed.topAddr = timed.baseAddr + 2*fixtureHeapLength := by
    simpa [timed,crep,pan] using fixture_heap (countdown n) (6*n+9) (naturalCountdownHOL n)
  have loopEq : concreteDeclLoopState riscvConfig.isa timed (countdownCrepCode n) =
      {loopStateFrom riscvConfig.isa pan (naturalCountdownHOL n) with
        clock := (loopStateFrom riscvConfig.isa pan (naturalCountdownHOL n)).clock + countdownLoopBudget n} := by
    simp [timed,crep,pan,loopStateFrom,concreteDeclLoopState,code]
  have sourceRun : evaluate branchingLoopEntry (concreteDeclLoopState riscvConfig.isa timed (countdownCrepCode n)) =
      (some (.result [.word 0]),post) := by
    rw [loopEq]
    simpa [pan,countdownLoopBudget] using loopRun
  have sourceBound : LoopSteps.steps branchingLoopEntry (concreteDeclLoopState riscvConfig.isa timed (countdownCrepCode n)) ≤ countdownLoopVisits n := by
    rw [loopEq]
    simpa [pan,countdownLoopBudget,countdownLoopVisits] using loopBound
  have span := twoProgram_wholeWord_span riscvConfig.isa (ofString "main") (entryName (naturalCountdownHOL n))
    (phase3CountdownCrepBody n) (Ne.symm (entryName_fresh (naturalCountdownHOL n))) (naturalCountdown_scalar n)
    timed post [.word 0] (countdownLoopVisits n) template fixtureHeapLength frame
    countdownRiscVBackend.wordToWordConf riscvConfig heap sourceRun sourceBound
  obtain ⟨wordPost,wordResult,relation,result,ffi,bound⟩ := span
  simp only [LoopToWord.CompileCorrect.resultCase] at relation
  refine ⟨post,?_,?_,?_⟩
  · simpa [countdownWordStarter,countdownCrepCode,phase3CountdownCrepBody,countdownWordPrograms,crep,timed,pan,relation.2.1] using result
  · simpa [countdownWordStarter,countdownCrepCode,phase3CountdownCrepBody,countdownWordPrograms,crep,timed,pan] using ffi
  · simpa [countdownWordBound,countdownWordStarter,countdownCrepCode,phase3CountdownCrepBody,countdownWordPrograms,crep,timed,pan] using bound
end SteppedFlapjack.Concrete
