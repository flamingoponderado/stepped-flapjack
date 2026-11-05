import SteppedFlapjack.LoopToWordSteps.LoopResult
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Loop

/-! Derived setup facts for quantitative Loop-to-Word loop simulation. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.LoopToWord
open Flapjack.LoopToWord.CompileCorrect Flapjack.Compiler.Encoders.Asm

/-- A non-error whole loop cannot execute an erroneous body. -/
theorem loopBody_notError {width : Nat} [NeZero width] {F : Type}
    (live exit : NumSet) (body : HolLoopProg width) (s cut post final : LoopSemStateFiniteExact width F)
    (bodyResult result : Option (LoopResultExact width))
    (cutRun : cutRes live (none,s) = (none,cut))
    (bodyRun : LoopSemStateFiniteExact.evaluate body cut = (bodyResult,post))
    (wholeRun : LoopSemStateFiniteExact.evaluate (.loop live body exit) s = (result,final))
    (notError : result ≠ some .error) : bodyResult ≠ some .error := by
  intro error
  subst bodyResult
  rw [LoopSemStateFiniteExact.evaluate,cutRun] at wholeRun
  simp only at wholeRun
  rw [fix_clock_evaluate,bodyRun] at wholeRun
  simp only [LoopSemStateFiniteExact.exitLoop,Prod.mk.injEq] at wholeRun
  exact notError wholeRun.1.symm

/-- A successful source loop cut constructs the real target cut state and the
relations needed to invoke the body induction hypothesis. -/
theorem loopCut_related {width : Nat} [NeZero width] {C F : Type}
    (live : NumSet) (s sourceCut : LoopSemStateFiniteExact width F)
    (t : WordSemStateFiniteExact width C F) (ctxt : Spt Nat) (retv : WordLocW width)
    (cut : cutRes live (none,s) = (none,sourceCut))
    (state : loopToWordStateRelHOLExact s t) (locals : localsRelHOL ctxt s.locals t.locals)
    (ret : sptLookup 0 t.locals = some retv) :
    ∃ targetCut : WordSemStateFiniteExact width C F,
      WordSemStateFiniteExact.cutState (mkNewCutsetHOL ctxt live,.ln) (WordSemStateFiniteExact.decClock t) = some targetCut ∧
      loopToWordStateRelHOLExact sourceCut targetCut ∧ localsRelHOL ctxt sourceCut.locals targetCut.locals ∧
      sptLookup 0 targetCut.locals = some retv := by
  have state' := state
  obtain ⟨len, hm, hmd, hsmd, hclock, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩ := state'
  have cutFacts : ∃ cs, cutState live s = some cs ∧ s.clock ≠ 0 ∧ sourceCut = decClock cs := by
    unfold cutRes at cut
    simp only at cut
    cases hc : cutState live s with
    | none => rw [hc] at cut; simp at cut
    | some cs =>
      simp only [hc] at cut
      have hcClock : cs.clock = s.clock := cutState_clock hc
      by_cases hz : s.clock = 0
      · simp [hcClock,hz] at cut
      · simp only [hcClock,hz,if_false,Prod.mk.injEq,true_and] at cut
        exact ⟨cs,rfl,hz,cut.symm⟩
  obtain ⟨cs,hcs,hz,rfl⟩ := cutFacts
  have subset : sptSubsetLive live s.locals ∧ cs = {s with locals := sptInter s.locals live} := by
    unfold cutState at hcs
    split at hcs
    · exact ⟨‹_›,(Option.some.inj hcs).symm⟩
    · cases hcs
  obtain ⟨subset,rfl⟩ := subset
  obtain ⟨env,hce,hlr⟩ := wordSemCutEnvMkNewCutsetHOL ctxt live s.locals t.locals retv ⟨locals,subset,ret⟩
  have ret' := (wordSemCutEnvMkNewCutsetIMPHOL ctxt live t.locals env hce).trans ret
  refine ⟨{t with clock := t.clock-1,locals := env},?_,?_,hlr,ret'⟩
  · simp [WordSemStateFiniteExact.cutState,WordSemStateFiniteExact.decClock,hce]
  · exact ⟨len,hm,hmd,hsmd,by simp [decClock,hclock],hbe,hffi,hcur,hlen,htop,hglob,hcode⟩


/-- If a source loop's initial cut does not continue and the whole execution
is non-error, that cut must have timed out at clock zero. -/
theorem loopCut_stopped_clockZero {width : Nat} [NeZero width] {F : Type}
    (live exit : NumSet) (body : HolLoopProg width) (source final cutPost : LoopSemStateFiniteExact width F)
    (cutResult result : Option (LoopResultExact width))
    (cutRun : cutRes live (none,source) = (cutResult,cutPost)) (stopped : cutResult ≠ none)
    (run : LoopSemStateFiniteExact.evaluate (.loop live body exit) source = (result,final))
    (notError : result ≠ some .error) : source.clock = 0 := by
  rw [LoopSemStateFiniteExact.evaluate,cutRun] at run
  cases cutResult with
  | none => exact False.elim (stopped rfl)
  | some r =>
    simp only at run
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj run
    unfold cutRes at cutRun
    cases hc : cutState live source with
    | none => simp [hc] at cutRun; exact False.elim (notError (congrArg some cutRun.1.symm))
    | some cs =>
      have eq := cutState_clock hc
      by_cases zero : source.clock = 0
      · exact zero
      · simp [hc,eq,zero] at cutRun

/-- A zero-clock target loop wrapper stops at its initial tick in two visits. -/
theorem tickLoopTick_zero {width : Nat} [NeZero width] {C F : Type}
    (live exit : Spt Unit) (body : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) (zero : s.clock = 0) :
    WordSteps.steps (.seq .tick (.seq (.loop live body exit) .tick)) s = 2 := by
  rw [WordSteps.steps_seq,WordSemStateFiniteExact.evaluate]
  have one : WordSteps.steps (.tick : WordLangProgHOL (BitVec width)) s = 1 := WordSteps.steps_leaf _ _ rfl
  simp [one,zero]

end SteppedFlapjack.LoopToWordSteps
