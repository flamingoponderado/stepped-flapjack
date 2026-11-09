import SteppedFlapjack.Concrete.CountdownWordSpan
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.WordToWord
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps SteppedFlapjack.WordAllocSteps
variable {C : Type}
/-- The Phase 2 limit for the unprefixed countdown source. -/
def naturalCountdownLoopBudget (n : Nat) : Nat := 156*(3 + 8*(6*n+16)+1)
def naturalCountdownLoopVisits (n : Nat) : Nat := 52*(3 + 8*(6*n+16)+naturalCountdownLoopBudget n+1)+8
/-- Executable optimized Word visit bound for the unprefixed countdown. -/
def naturalCountdownWordBound (n : Nat) : Nat :=
  twoProgramWordBound riscvConfig.isa (ofString "main") (entryName (naturalCountdownHOL n))
    (phase3CountdownCrepBody n) (naturalCountdownLoopVisits n) phase3WordConfig riscvConfig
/-- The Word start state constructed from the Phase 2 countdown state. -/
noncomputable def naturalCountdownWordStarter (n : Nat) (template : WordSemStateFiniteExact 64 C Unit) (frame : Nat) :=
  let pan := panSimpSourceState (naturalCountdown n) (clockedFixtureSource (naturalCountdown n) (6*n+7))
  let crep := crepStateFrom pan (naturalCountdownHOL n)
  let timed := {crep with clock := crep.clock + naturalCountdownLoopBudget n}
  phase3Starter riscvConfig.isa timed (countdownCrepCode n) template fixtureHeapLength 64 frame

/-- The countdown Phase 2 run reaches the actual optimized Word start call
with matching return and events and an explicit code-derived visit bound. -/
theorem naturalCountdown_wholeWord (n : Nat) (range : n < 2^64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit)
    (template : WordSemStateFiniteExact 64 C Unit) (frame : Nat) :
    let pan := panSimpSourceState (naturalCountdown n) (clockedFixtureSource (naturalCountdown n) (6*n+7))
    let crep := crepStateFrom pan (naturalCountdownHOL n)
    let starter := naturalCountdownWordStarter n template frame
    let target := WordSemStateFiniteExact.evaluate (.call none (some 64) [0] none)
      {starter with clock := 6*naturalCountdownLoopVisits n+1, code := sptFromAList (compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2}
    ∃ (final : CrepSemHOLState 64 Unit) (post : LoopSemStateFiniteExact 64 Unit),
      evalCrepSemHOLProgExact crep (naturalCrepEntry n) = (some (.return [.word 0]),final) ∧
      crepToLoopStateRelExact final {post with clock := final.clock} ∧
      target.1 = some (.result (.loc 1 0) [.word 0]) ∧ target.2.ffi = post.ffi ∧
      WordSteps.steps (.call none (some 64) [0] none)
        {starter with clock := 6*naturalCountdownLoopVisits n+1, code := sptFromAList (compile countdownRiscVBackend.wordToWordConf riscvConfig (countdownWordPrograms n)).2} ≤
        naturalCountdownWordBound n := by
  let pan := panSimpSourceState (naturalCountdown n) (clockedFixtureSource (naturalCountdown n) (6*n+7))
  let crep := crepStateFrom pan (naturalCountdownHOL n)
  let timed := {crep with clock := crep.clock + naturalCountdownLoopBudget n}
  have code : crepPrograms (naturalCountdownHOL n) = countdownCrepCode n := by
    simpa [countdownCrepCode,phase3CountdownCrepBody,twoPrograms] using natural_countdown_crep_code n
  obtain ⟨final,post,crepRun,_,loopRun,loopBound,stateRel,_,_,_⟩ := naturalCountdown_fixture_entry_loop riscvConfig.isa n range context primitive handler
  have heap : timed.topAddr = timed.baseAddr + 2*fixtureHeapLength := by
    simpa [timed,crep,pan] using fixture_heap (naturalCountdown n) (6*n+7) (naturalCountdownHOL n)
  have loopEq : concreteDeclLoopState riscvConfig.isa timed (countdownCrepCode n) =
      {loopStateFrom riscvConfig.isa pan (naturalCountdownHOL n) with
        clock := (loopStateFrom riscvConfig.isa pan (naturalCountdownHOL n)).clock + naturalCountdownLoopBudget n} := by
    simp [timed,crep,pan,loopStateFrom,concreteDeclLoopState,code]
  have sourceRun : evaluate branchingLoopEntry (concreteDeclLoopState riscvConfig.isa timed (countdownCrepCode n)) =
      (some (.result [.word 0]),post) := by
    rw [loopEq]
    simpa [pan,naturalCountdownLoopBudget] using loopRun
  have sourceBound : LoopSteps.steps branchingLoopEntry (concreteDeclLoopState riscvConfig.isa timed (countdownCrepCode n)) ≤ naturalCountdownLoopVisits n := by
    rw [loopEq]
    simpa [pan,naturalCountdownLoopBudget,naturalCountdownLoopVisits] using loopBound
  have span := twoProgram_wholeWord_span riscvConfig.isa (ofString "main") (entryName (naturalCountdownHOL n))
    (phase3CountdownCrepBody n) (Ne.symm (entryName_fresh (naturalCountdownHOL n))) (naturalCountdown_scalar n)
    timed post [.word 0] (naturalCountdownLoopVisits n) template fixtureHeapLength frame
    countdownRiscVBackend.wordToWordConf riscvConfig heap sourceRun sourceBound
  obtain ⟨_,wordPost,wordResult,relation,result,ffi,bound⟩ := span
  simp only [LoopToWord.CompileCorrect.resultCase] at relation
  refine ⟨final,post,?_,stateRel,?_,?_,?_⟩
  · simpa [crep,pan] using crepRun
  · simpa [naturalCountdownWordStarter,countdownCrepCode,phase3CountdownCrepBody,countdownWordPrograms,crep,timed,pan,relation.2.1] using result
  · simpa [naturalCountdownWordStarter,countdownCrepCode,phase3CountdownCrepBody,countdownWordPrograms,crep,timed,pan] using ffi
  · simpa [naturalCountdownWordBound,phase3WordConfig_eq,naturalCountdownWordStarter,countdownCrepCode,phase3CountdownCrepBody,countdownWordPrograms,crep,timed,pan] using bound
end SteppedFlapjack.Concrete
