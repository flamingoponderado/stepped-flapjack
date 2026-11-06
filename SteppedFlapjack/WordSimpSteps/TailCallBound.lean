import SteppedFlapjack.WordSimpSteps.TailEntry
import SteppedFlapjack.WordSimpSteps.LoopSequenceBound
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.NoInstallEvaluate

/-! Clock and visit bounds for the actual direct Word tail call. -/
namespace SteppedFlapjack.WordSimpSteps
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Backend.WordSimp SteppedFlapjack.WordSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- A direct tail call's visits are bounded by its actual callee's syntax and
available clock, even if argument lookup fails or the call times out. -/
theorem directTail_clock_bound (loc : Nat) (callee : WordLangProgHOL (BitVec width))
    (shape : LoopSequence callee) (s : WordSemStateFiniteExact width C F)
    (lookup : sptLookup loc s.code = some (1,callee)) :
    steps (.call none (some loc) [0] none) s ≤ (1 + sizeOf callee) * (s.clock+1) := by
  cases hvar : getVar 0 s with
  | none =>
    rw [steps.eq_def]
    simp [WordSemStateFiniteExact.getVars,hvar]
    nlinarith
  | some value =>
    have args : getVars [0] s = some [value] := by simp [WordSemStateFiniteExact.getVars,hvar]
    have found : wordSemFindCode (some loc) [value] s.code s.stackSize =
        some ([value],callee,sptLookup loc s.stackSize) := by simp [wordSemFindCode,lookup]
    by_cases clock : s.clock = 0
    · rw [steps.eq_def]
      simp [args,wordSemBadDestArgs,wordSemAddRetLoc,found,clock]
    · rw [steps_call_tail (some loc) [0] s [value] [value] (sptLookup loc s.stackSize) callee
        args (by simp [wordSemBadDestArgs]) found clock]
      have h := loopSequence_clock_bound shape (callEnv [value] (sptLookup loc s.stackSize) (decClock s))
      change steps callee (callEnv [value] (sptLookup loc s.stackSize) (decClock s)) ≤
        sizeOf callee * (s.clock-1+1) at h
      have scale := Nat.mul_le_mul_left (sizeOf callee) (show s.clock-1+1 ≤ s.clock+1 by omega)
      nlinarith

/-- A non-error, non-timeout direct call consumes at most its own visits when
its reached callee belongs to the supported call-free fragment. -/
theorem directTail_consumed (loc : Nat) (callee : WordLangProgHOL (BitVec width))
    (shape : LoopSequence callee) (s post : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) (lookup : sptLookup loc s.code = some (1,callee))
    (run : evaluate (.call none (some loc) [0] none) s = (res,post))
    (notError : res ≠ some .error) (notTimeout : res ≠ some .timeOut) :
    s.clock-post.clock ≤ steps (.call none (some loc) [0] none) s := by
  rw [evaluate] at run
  cases hvar : getVar 0 s with
  | none => simp [WordSemStateFiniteExact.getVars,hvar] at run; exact False.elim (notError run.1.symm)
  | some value =>
    have args : getVars [0] s = some [value] := by simp [WordSemStateFiniteExact.getVars,hvar]
    have found : wordSemFindCode (some loc) [value] s.code s.stackSize =
        some ([value],callee,sptLookup loc s.stackSize) := by simp [wordSemFindCode,lookup]
    simp only [args,wordSemBadDestArgs,wordSemAddRetLoc,found] at run
    by_cases clock : s.clock = 0
    · simp [clock] at run
      exact False.elim (notTimeout run.1.symm)
    · simp only [clock,↓reduceDIte] at run
      rcases he : evaluate callee (callEnv [value] (sptLookup loc s.stackSize) (decClock s)) with ⟨r,t⟩
      rw [he] at run
      by_cases bad : wordSemBadFunReturn r = true
      · simp [bad] at run
        exact False.elim (notError run.1.symm)
      · simp only [bad,Bool.false_eq_true,if_false] at run
        obtain ⟨rfl,rfl⟩ := run
        have consumed := clockProgram_consumption callee
          (callEnv [value] (sptLookup loc s.stackSize) (decClock s)) (loopSequence_clockProgram shape)
        rw [he] at consumed
        rw [steps_call_tail (some loc) [0] s [value] [value] (sptLookup loc s.stackSize) callee
          args (by simp [wordSemBadDestArgs]) found clock]
        change s.clock-1 ≤ post.clock + steps callee
          (callEnv [value] (sptLookup loc s.stackSize) (decClock s)) at consumed
        omega

/-- Call destinations appearing in a tail-entry sequence. -/
inductive TailEntryCalls : WordLangProgHOL (BitVec width) → Nat → Prop
  | call (loc) : TailEntryCalls (.call none (some loc) [0] none) loc
  | left {a b loc} : TailEntryCalls a loc → TailEntryCalls (.seq a b) loc
  | right {a b loc} : TailEntryCalls b loc → TailEntryCalls (.seq a b) loc

/-- Only code entries targeted by this particular entry need supported
callee shape and size; other code entries are unrestricted. -/
def TailEntryCodeBound (p : WordLangProgHOL (BitVec width))
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) (K : Nat) : Prop :=
  ∀ loc, TailEntryCalls p loc → ∃ callee, sptLookup loc code = some (1,callee) ∧
    LoopSequence callee ∧ sizeOf callee ≤ K

/-- The actual Word entry's visits have a syntax-and-clock bound, requiring
callee properties only for its own direct call destinations. -/
theorem tailEntry_clock_bound {p : WordLangProgHOL (BitVec width)}
    (shape : LoopLiveSteps.WordTailEntryShape p) :
    ∀ (s : WordSemStateFiniteExact width C F) (K : Nat),
      noInstallSubprogsHOL p = true → WordProps.noInstallCode s.code → TailEntryCodeBound p s.code K →
      steps p s ≤ (sizeOf p * (K+1)) * (s.clock+1) := by
  induction shape with
  | @branch q h =>
    intro s K _ _ _
    have bound := branch_static h s
    have scale : 1 ≤ (K+1)*(s.clock+1) := by nlinarith
    have mult := Nat.mul_le_mul_left (sizeOf q) scale
    simp only [Nat.mul_one,← Nat.mul_assoc] at mult ⊢
    omega
  | call loc =>
    intro s K _ _ code
    obtain ⟨callee,lookup,body,size⟩ := code loc (.call loc)
    have bound := directTail_clock_bound loc callee body s lookup
    have sz : 1 + sizeOf callee ≤ sizeOf (.call none (some loc) [0] none : WordLangProgHOL (BitVec width)) * (K+1) := by simp_wf; nlinarith
    exact bound.trans (Nat.mul_le_mul_right _ sz)
  | @seq a b ha hb iha ihb =>
    intro s K noInstall noInstallCode code
    simp only [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] at noInstall
    have codeA : TailEntryCodeBound a s.code K := fun loc h => code loc (.left h)
    have codeB : TailEntryCodeBound b s.code K := fun loc h => code loc (.right h)
    have first := iha s K noInstall.1 noInstallCode codeA
    have sizeLower : 1 + sizeOf a + sizeOf b ≤ sizeOf (.seq a b : WordLangProgHOL (BitVec width)) := by simp_wf
    let m := (K+1)*(s.clock+1)
    have factorPositive : 1 ≤ m := by dsimp [m]; nlinarith
    have sizeScaled := Nat.mul_le_mul_right m sizeLower
    have sizeScaled' : m + sizeOf a*m + sizeOf b*m ≤ sizeOf (.seq a b : WordLangProgHOL (BitVec width))*m := by
      simpa only [Nat.add_mul,one_mul] using sizeScaled
    rw [Nat.mul_assoc] at first ⊢
    change steps a s ≤ sizeOf a*m at first
    change steps (.seq a b) s ≤ sizeOf (.seq a b : WordLangProgHOL (BitVec width))*m
    rw [steps_seq]
    rcases run : evaluate a s with ⟨res,middle⟩
    cases res with
    | some r => simp only; omega
    | none =>
      have codeEq := WordSemStateFiniteExact.code_evaluate a s noInstall.1 noInstallCode
      rw [run] at codeEq
      simp only at codeEq
      have second := ihb middle K noInstall.2 (by simpa only [codeEq] using noInstallCode)
        (by simpa only [codeEq] using codeB)
      have clock := (evaluate_clock a s none middle run).1
      simp only
      have scaled := Nat.mul_le_mul_left (sizeOf b * (K+1)) (show middle.clock+1 ≤ s.clock+1 by omega)
      simp only [Nat.mul_assoc] at scaled second
      change sizeOf b * ((K+1) * (middle.clock+1)) ≤ sizeOf b*m at scaled
      omega

/-- A completed entry consumes no more clock than its actual Word visits. -/
theorem tailEntry_consumed {p : WordLangProgHOL (BitVec width)}
    (shape : LoopLiveSteps.WordTailEntryShape p) :
    ∀ (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width)) (K : Nat),
      noInstallSubprogsHOL p = true → WordProps.noInstallCode s.code → TailEntryCodeBound p s.code K →
      evaluate p s = (res,post) → res ≠ some .error → res ≠ some .timeOut →
      s.clock-post.clock ≤ steps p s := by
  induction shape with
  | branch h =>
    intro s post res K _ _ _ run _ _
    have bound := clockProgram_consumed_le_steps _ s (branch_clockProgram h)
    rw [run] at bound
    exact bound
  | call loc =>
    intro s post res K _ _ code run notError notTimeout
    obtain ⟨callee,lookup,body,_⟩ := code loc (.call loc)
    exact directTail_consumed loc callee body s post res lookup run notError notTimeout
  | @seq a b ha hb iha ihb =>
    intro s post res K noInstall noInstallCode code run notError notTimeout
    simp only [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] at noInstall
    have codeA : TailEntryCodeBound a s.code K := fun loc h => code loc (.left h)
    have codeB : TailEntryCodeBound b s.code K := fun loc h => code loc (.right h)
    have preserved := WordSemStateFiniteExact.code_evaluate a s noInstall.1 noInstallCode
    rw [evaluate,fix_clock_evaluate] at run
    rw [steps_seq]
    rcases first : evaluate a s with ⟨out,middle⟩
    rw [first] at run preserved
    simp only at preserved
    have firstClock := (evaluate_clock a s out middle first).1
    cases out with
    | none =>
      have firstBound := iha s middle none K noInstall.1 noInstallCode codeA first (by simp) (by simp)
      have secondBound := ihb middle post res K noInstall.2
        (by simpa only [preserved] using noInstallCode) (by simpa only [preserved] using codeB)
        run notError notTimeout
      have secondClock := (evaluate_clock b middle res post run).1
      simp only
      omega
    | some r =>
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj run
      have firstBound := iha s middle (some r) K noInstall.1 noInstallCode codeA first notError notTimeout
      simp only
      omega


/-- Tail-entry branches and direct calls do not install code. -/
theorem branch_noInstall {p : WordLangProgHOL (BitVec width)} (shape : Branch p) :
    noInstallSubprogsHOL p = true := by
  induction shape <;> simp_all [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp]

theorem tailEntry_noInstall {p : WordLangProgHOL (BitVec width)}
    (shape : LoopLiveSteps.WordTailEntryShape p) : noInstallSubprogsHOL p = true := by
  induction shape with
  | branch h => exact branch_noInstall h
  | call loc => rfl
  | seq _ _ a b =>
    simp only [noInstallSubprogsHOL] at a b
    simpa only [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] using And.intro a b

/-- A completed call entry replays at a clock bounded by its visits. -/
theorem tailEntry_normalized_run {p : WordLangProgHOL (BitVec width)}
    (shape : LoopLiveSteps.WordTailEntryShape p)
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width)) (K limit : Nat)
    (noInstall : noInstallSubprogsHOL p = true) (noInstallCode : WordProps.noInstallCode s.code)
    (code : TailEntryCodeBound p s.code K) (run : evaluate p s = (res,post))
    (notError : res ≠ some .error) (notTimeout : res ≠ some .timeOut) (sourceBound : steps p s ≤ limit) :
    evaluate p {s with clock := limit} = (res,{post with clock := limit-(s.clock-post.clock)}) := by
  have consumed := tailEntry_consumed shape s post res K noInstall noInstallCode code run notError notTimeout
  have le : s.clock-post.clock ≤ limit := consumed.trans sourceBound
  have reduced := evaluate_dec_clock p s res post run
  have extended := evaluate_add_clock (limit - (s.clock-post.clock)) p
    {s with clock := s.clock-post.clock} res {post with clock := 0} ⟨reduced,notTimeout⟩
  have eqn : s.clock-post.clock + (limit-(s.clock-post.clock)) = limit := by omega
  simpa only [eqn,Nat.zero_add] using extended

/-- The actual WordSimp output has a normalized execution and a computable
visit bound, assuming the code facts only for its syntactic call targets. -/
theorem tailEntry_wordSimp_normalized {p : WordLangProgHOL (BitVec width)}
    (shape : LoopLiveSteps.WordTailEntryShape p)
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width)) (K limit : Nat)
    (noInstallCode : WordProps.noInstallCode s.code)
    (code : TailEntryCodeBound p s.code K)
    (codeOpt : TailEntryCodeBound (Compiler.Backend.WordSimp.compileExp p) s.code K)
    (run : evaluate p s = (res,post)) (notError : res ≠ some .error)
    (notTimeout : res ≠ some .timeOut) (sourceBound : steps p s ≤ limit) (gc : gcFunConstOk s.gcFun) :
    evaluate (Compiler.Backend.WordSimp.compileExp p) {s with clock := limit} =
        (res,{post with clock := limit-(s.clock-post.clock)}) ∧
    steps (Compiler.Backend.WordSimp.compileExp p) {s with clock := limit} ≤
      sizeOf (Compiler.Backend.WordSimp.compileExp p) * (K+1) * (limit+1) := by
  have normalized := tailEntry_normalized_run shape s post res K limit (tailEntry_noInstall shape) noInstallCode code
    run notError notTimeout sourceBound
  have good : gcFunConstOk ({s with clock := limit} : WordSemStateFiniteExact width C F).gcFun := gc
  have semantics := (compileExp_tailEntry_correct shape {s with clock := limit} good).2
  exact ⟨semantics.trans normalized,tailEntry_clock_bound (compileExp_tailEntry shape)
    {s with clock := limit} K (tailEntry_noInstall (compileExp_tailEntry shape)) noInstallCode codeOpt⟩

end SteppedFlapjack.WordSimpSteps
