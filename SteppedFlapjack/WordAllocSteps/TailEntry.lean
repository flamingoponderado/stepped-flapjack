import SteppedFlapjack.WordAllocSteps.StackReady
import SteppedFlapjack.WordDeadSteps.SecondTailEntry
import SteppedFlapjack.WordSsaSteps.TailEntry

/-! Register-allocation bounds for a direct single-argument tail entry. -/
namespace SteppedFlapjack.WordAllocSteps
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Backend.WordSimp SteppedFlapjack.WordSteps
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.LoopLiveSteps
open Flapjack.Compiler.Backend.WordAlloc Flapjack.WordAlloc Flapjack.Compiler.Backend.WordToWord
variable {width : Nat} [NeZero width] {C F : Type}

/-- The call carries one argument, which allocation may rename. -/
inductive RegTailShape : WordLangProgHOL (BitVec width) → Prop
  | branch {p} : Branch p → RegTailShape p
  | call (loc reg : Nat) : RegTailShape (.call none (some loc) [reg] none)
  | seq {a b} : RegTailShape a → RegTailShape b → RegTailShape (.seq a b)

/-- A direct tail call's visits are bounded by its actual callee's syntax and
available clock, even if argument lookup fails or the call times out. -/
theorem regDirectTail_control_bound (loc reg : Nat) (callee : WordLangProgHOL (BitVec width))
    (shape : LoopSequence callee) (s : WordSemStateFiniteExact width C F)
    (lookup : sptLookup loc s.code = some (1,callee)) :
    steps (.call none (some loc) [reg] none) s ≤ (1 + wordControlWeight callee) * (s.clock+1) := by
  cases hvar : getVar reg s with
  | none =>
    rw [steps.eq_def]
    simp [WordSemStateFiniteExact.getVars,hvar]
    nlinarith
  | some value =>
    have args : getVars [reg] s = some [value] := by simp [WordSemStateFiniteExact.getVars,hvar]
    have found : wordSemFindCode (some loc) [value] s.code s.stackSize =
        some ([value],callee,sptLookup loc s.stackSize) := by simp [wordSemFindCode,lookup]
    by_cases clock : s.clock = 0
    · rw [steps.eq_def]
      simp [args,wordSemBadDestArgs,wordSemAddRetLoc,found,clock]
    · rw [steps_call_tail (some loc) [reg] s [value] [value] (sptLookup loc s.stackSize) callee
        args (by simp [wordSemBadDestArgs]) found clock]
      have h := wordControl_clock_bound (loopSequence_program shape) (callEnv [value] (sptLookup loc s.stackSize) (decClock s))
      change steps callee (callEnv [value] (sptLookup loc s.stackSize) (decClock s)) ≤
        wordControlWeight callee * (s.clock-1+1) at h
      have scale := Nat.mul_le_mul_left (wordControlWeight callee) (show s.clock-1+1 ≤ s.clock+1 by omega)
      nlinarith

/-- A non-error, non-timeout direct call consumes at most its own visits when
its reached callee belongs to the supported call-free fragment. -/
theorem regDirectTail_consumed (loc reg : Nat) (callee : WordLangProgHOL (BitVec width))
    (shape : LoopSequence callee) (s post : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) (lookup : sptLookup loc s.code = some (1,callee))
    (run : evaluate (.call none (some loc) [reg] none) s = (res,post))
    (notError : res ≠ some .error) (notTimeout : res ≠ some .timeOut) :
    s.clock-post.clock ≤ steps (.call none (some loc) [reg] none) s := by
  rw [evaluate] at run
  cases hvar : getVar reg s with
  | none => simp [WordSemStateFiniteExact.getVars,hvar] at run; exact False.elim (notError run.1.symm)
  | some value =>
    have args : getVars [reg] s = some [value] := by simp [WordSemStateFiniteExact.getVars,hvar]
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
        rw [steps_call_tail (some loc) [reg] s [value] [value] (sptLookup loc s.stackSize) callee
          args (by simp [wordSemBadDestArgs]) found clock]
        change s.clock-1 ≤ post.clock + steps callee
          (callEnv [value] (sptLookup loc s.stackSize) (decClock s)) at consumed
        omega

/-- Call destinations appearing in a tail-entry sequence. -/
inductive RegTailCalls : WordLangProgHOL (BitVec width) → Nat → Prop
  | call (loc reg) : RegTailCalls (.call none (some loc) [reg] none) loc
  | left {a b loc} : RegTailCalls a loc → RegTailCalls (.seq a b) loc
  | right {a b loc} : RegTailCalls b loc → RegTailCalls (.seq a b) loc

/-- Reachable callees have a bounded executable control-node weight. -/
def RegTailControlCodeBound (p : WordLangProgHOL (BitVec width))
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) (K : Nat) : Prop :=
  ∀ loc, RegTailCalls p loc → ∃ callee, sptLookup loc code = some (1,callee) ∧
    LoopSequence callee ∧ wordControlWeight callee ≤ K

/-- Only code entries targeted by this particular entry need supported
callee shape and size; other code entries are unrestricted. -/
def RegTailCodeBound (p : WordLangProgHOL (BitVec width))
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) (K : Nat) : Prop :=
  ∀ loc, RegTailCalls p loc → ∃ callee, sptLookup loc code = some (1,callee) ∧
    LoopSequence callee ∧ sizeOf callee ≤ K

/-- The actual Word entry's visits have a syntax-and-clock bound, requiring
callee properties only for its own direct call destinations. -/
theorem regTail_control_bound {p : WordLangProgHOL (BitVec width)}
    (shape : RegTailShape p) :
    ∀ (s : WordSemStateFiniteExact width C F) (K : Nat),
      noInstallSubprogsHOL p = true → WordProps.noInstallCode s.code → RegTailControlCodeBound p s.code K →
      steps p s ≤ (wordControlWeight p * (K+1)) * (s.clock+1) := by
  induction shape with
  | @branch q h =>
    intro s K _ _ _
    have bound := wordControl_clock_bound (branch_program h) s
    have scale := Nat.mul_le_mul_left (wordControlWeight q * (s.clock+1)) (show 1 ≤ K+1 by omega)
    simp only [Nat.mul_one] at scale
    nlinarith
  | call loc reg =>
    intro s K _ _ code
    obtain ⟨callee,lookup,body,size⟩ := code loc (.call loc reg)
    have bound := regDirectTail_control_bound loc reg callee body s lookup
    have sz : 1 + wordControlWeight callee ≤ wordControlWeight (.call none (some loc) [reg] none : WordLangProgHOL (BitVec width)) * (K+1) := by simp [wordControlWeight]; nlinarith
    exact bound.trans (Nat.mul_le_mul_right _ sz)
  | @seq a b ha hb iha ihb =>
    intro s K noInstall noInstallCode code
    simp only [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] at noInstall
    have codeA : RegTailControlCodeBound a s.code K := fun loc h => code loc (.left h)
    have codeB : RegTailControlCodeBound b s.code K := fun loc h => code loc (.right h)
    have first := iha s K noInstall.1 noInstallCode codeA
    have sizeLower : 1 + wordControlWeight a + wordControlWeight b ≤ wordControlWeight (.seq a b : WordLangProgHOL (BitVec width)) := by simp [wordControlWeight]
    let m := (K+1)*(s.clock+1)
    have factorPositive : 1 ≤ m := by dsimp [m]; nlinarith
    have sizeScaled := Nat.mul_le_mul_right m sizeLower
    have sizeScaled' : m + wordControlWeight a*m + wordControlWeight b*m ≤ wordControlWeight (.seq a b : WordLangProgHOL (BitVec width))*m := by
      simpa only [Nat.add_mul,one_mul] using sizeScaled
    rw [Nat.mul_assoc] at first ⊢
    change steps a s ≤ wordControlWeight a*m at first
    change steps (.seq a b) s ≤ wordControlWeight (.seq a b : WordLangProgHOL (BitVec width))*m
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
      have scaled := Nat.mul_le_mul_left (wordControlWeight b * (K+1)) (show middle.clock+1 ≤ s.clock+1 by omega)
      simp only [Nat.mul_assoc] at scaled second
      change wordControlWeight b * ((K+1) * (middle.clock+1)) ≤ wordControlWeight b*m at scaled
      omega



theorem regTail_control_le_size {p : WordLangProgHOL (BitVec width)} (shape : RegTailShape p) :
    wordControlWeight p ≤ sizeOf p := by
  induction shape with
  | branch h => exact wordControl_le_size (branch_program h)
  | call loc reg => simp [wordControlWeight]
  | seq ha hb iha ihb => simp [wordControlWeight]; omega

theorem regTail_clock_bound {p : WordLangProgHOL (BitVec width)} (shape : RegTailShape p)
    (s : WordSemStateFiniteExact width C F) (K : Nat)
    (noInstall : noInstallSubprogsHOL p = true) (codeOk : WordProps.noInstallCode s.code)
    (code : RegTailCodeBound p s.code K) :
    steps p s ≤ (sizeOf p * (K+1)) * (s.clock+1) := by
  have control : RegTailControlCodeBound p s.code K := by
    intro loc calls
    obtain ⟨callee,lookup,shape,size⟩ := code loc calls
    exact ⟨callee,lookup,shape,(wordControl_le_size (loopSequence_program shape)).trans size⟩
  have bound := regTail_control_bound shape s K noInstall codeOk control
  have size := Nat.mul_le_mul_right ((K+1)*(s.clock+1)) (regTail_control_le_size shape)
  nlinarith

/-- A single-argument tail entry whose destinations satisfy a predicate. -/
inductive RegAllowedTail (allowed : Nat → Prop) : WordLangProgHOL (BitVec width) → Prop
  | branch {p} : Branch p → RegAllowedTail allowed p
  | call (loc reg : Nat) : allowed loc → RegAllowedTail allowed (.call none (some loc) [reg] none)
  | seq {a b} : RegAllowedTail allowed a → RegAllowedTail allowed b → RegAllowedTail allowed (.seq a b)

omit [NeZero width] in
theorem allowed_regTail {allowed : Nat → Prop} {p : WordLangProgHOL (BitVec width)}
    (shape : AllowedTailEntry allowed p) : RegAllowedTail allowed p := by
  induction shape with
  | branch h => exact .branch h
  | call loc good => exact .call loc 0 good
  | seq _ _ a b => exact .seq a b

omit [NeZero width] in
theorem regAllowed_shape {allowed : Nat → Prop} {p : WordLangProgHOL (BitVec width)}
    (shape : RegAllowedTail allowed p) : RegTailShape p := by
  induction shape with
  | branch h => exact .branch h
  | call loc reg _ => exact .call loc reg
  | seq _ _ a b => exact .seq a b

omit [NeZero width] in
theorem regAllowed_calls {allowed : Nat → Prop} {p : WordLangProgHOL (BitVec width)}
    (shape : RegAllowedTail allowed p) : ∀ loc, RegTailCalls p loc → allowed loc := by
  induction shape with
  | branch h => intro loc call; induction h <;> cases call <;> simp_all
  | call loc reg good => intro dest call; cases call; exact good
  | seq _ _ a b =>
    intro loc call
    cases call with
    | left h => exact a loc h
    | right h => exact b loc h

/-- Colouring changes the argument register but not the direct destination. -/
theorem colour_regAllowed (f : Nat → Nat) {allowed : Nat → Prop} {p : WordLangProgHOL (BitVec width)}
    (shape : RegAllowedTail allowed p) : RegAllowedTail allowed (Flapjack.WordAlloc.applyColour f p) := by
  induction shape with
  | branch h => exact .branch (colour_branch f h)
  | call loc reg good => simpa only [Flapjack.WordAlloc.applyColour,List.map_cons,List.map_nil] using RegAllowedTail.call loc (f reg) good
  | seq _ _ a b => exact .seq a b

/-- Every branch of the actual allocator retains the allowed destinations. -/
theorem wordAlloc_regAllowed (fc : Nat) (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width) (alg k : Nat)
    (col : Option (Spt Nat)) {allowed : Nat → Prop} {p : WordLangProgHOL (BitVec width)}
    (shape : RegAllowedTail allowed p) : RegAllowedTail allowed (Flapjack.WordAlloc.wordAlloc fc ac alg k p col) := by
  simp only [Flapjack.WordAlloc.wordAlloc]
  cases ho : Flapjack.WordAlloc.oracleColourOk k col (Flapjack.WordAlloc.getClashTree p []) p (Flapjack.WordAlloc.getForced ac p []) with
  | none =>
    simp only
    cases hh : Flapjack.WordAlloc.getHeuristics alg fc p with
    | mk moves costs =>
      simp only
      cases hs : Flapjack.WordAlloc.selectRegAlloc alg costs k moves (Flapjack.WordAlloc.getClashTree p [])
          (Flapjack.WordAlloc.getForced ac p []) (Flapjack.WordAlloc.getStackOnly p) with
      | success colour => exact colour_regAllowed _ shape
      | failure failure => exact shape
  | some coloured =>
    simp only
    cases col with
    | none => simp [Flapjack.WordAlloc.oracleColourOk] at ho
    | some c =>
      simp only [Flapjack.WordAlloc.oracleColourOk] at ho
      split at ho
      · split at ho
        · simp only [Option.some.injEq] at ho
          subst coloured
          exact colour_regAllowed _ shape
        · cases ho
      · cases ho

/-- Register-renamed tail entries are no-install programs. -/
theorem regTail_noInstall {p : WordLangProgHOL (BitVec width)} (shape : RegTailShape p) :
    noInstallSubprogsHOL p = true := by
  induction shape with
  | branch h => exact branch_noInstall h
  | call loc reg => rfl
  | seq _ _ a b =>
    simp only [noInstallSubprogsHOL] at a b
    simpa only [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] using And.intro a b

/-- Register allocation preserves a completed direct-entry execution and
bounds its visits by the allocated syntax, clock, and reached callee size. -/
theorem wordAlloc_tailEntry_correct_with_steps (fc : Nat) (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width)
    (alg k : Nat) {p : WordLangProgHOL (BitVec width)} (col : Option (Spt Nat)) (shape : WordTailEntryShape p)
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width)) (K : Nat)
    (noInstallCode : WordProps.noInstallCode s.code) (code : TailEntryCodeBound p s.code K)
    (run : evaluate p s = (res,post)) (nonerror : res ≠ some .error)
    (even : Flapjack.Compiler.Backend.WordAlloc.Proofs.evenStartingLocals s.locals)
    (cutsets : wfCutsets p) :
    ∃ targetPost,
      evaluate (Flapjack.WordAlloc.wordAlloc fc ac alg k p col) s = (res,targetPost) ∧
      Flapjack.WordAlloc.wordStateEqRel post targetPost ∧
      (match res with | none | some (.break _) | some (.continue _) => True | some _ => post.locals = targetPost.locals) ∧
      RegTailShape (Flapjack.WordAlloc.wordAlloc fc ac alg k p col) ∧
      RegTailCodeBound (Flapjack.WordAlloc.wordAlloc fc ac alg k p col) s.code K ∧
      steps (Flapjack.WordAlloc.wordAlloc fc ac alg k p col) s ≤
        sizeOf (Flapjack.WordAlloc.wordAlloc fc ac alg k p col) * (K+1) * (s.clock+1) := by
  obtain ⟨perm,correct⟩ := Flapjack.WordAlloc.wordAllocCorrect fc ac alg p k col s ⟨even,cutsets⟩
  have permRun := SteppedFlapjack.WordSsaSteps.tailEntry_withPermute shape s perm K noInstallCode code
  rw [run] at permRun
  simp only at permRun
  have permNonerror : (evaluate p {s with permute := perm}).1 ≠ some .error := by rw [permRun]; exact nonerror
  dsimp only at correct
  rw [if_neg permNonerror,permRun] at correct
  rcases targetRun : evaluate (Flapjack.WordAlloc.wordAlloc fc ac alg k p col) s with ⟨targetResult,targetPost⟩
  simp only [targetRun] at correct
  have inputAllowed := allowed_regTail (tailEntry_allowed_of_code shape s.code K code)
  have outputAllowed := wordAlloc_regAllowed fc ac alg k col inputAllowed
  have outShape := regAllowed_shape outputAllowed
  have outCode : RegTailCodeBound (Flapjack.WordAlloc.wordAlloc fc ac alg k p col) s.code K := regAllowed_calls outputAllowed
  have bound := regTail_clock_bound outShape s K (regTail_noInstall outShape) noInstallCode outCode
  refine ⟨targetPost,?_,?_,?_,outShape,outCode,bound⟩
  · exact congrArg (fun r => (r,targetPost)) correct.1.symm
  · simpa only [Flapjack.WordAlloc.wordStateEqRel] using correct.2.1
  · cases res with
    | none => trivial
    | some r => cases r <;> exact correct.2.2

/-- Register-renamed flat entries fit the existing Word-to-Stack call fragment. -/
theorem flat_regTail_callSequence {p : WordLangProgHOL (BitVec width)} (shape : RegTailShape p)
    (flat : flatExpConventions p = true) : SteppedFlapjack.WordToStackSteps.CallSequence p := by
  induction shape with
  | branch h => exact .block (flat_branch_block h flat)
  | call loc reg => exact .tail (some loc) [reg]
  | seq _ _ a b =>
    simp only [flatExpConventions,Bool.and_eq_true] at flat
    exact .seq (a flat.1) (b flat.2)

/-- Register-renamed tail entries contain no must-terminate markers. -/
theorem removeMustTerminate_regTail {p : WordLangProgHOL (BitVec width)} (shape : RegTailShape p) :
    Flapjack.Compiler.Backend.WordRemove.removeMustTerminate p = p := by
  induction shape with
  | branch h => exact removeMustTerminate_branch h
  | call loc reg => rfl
  | seq _ _ a b => simp only [Flapjack.Compiler.Backend.WordRemove.removeMustTerminate,a,b]

/-- The actual Word compiler prefix through register allocation preserves a
completed tail-entry run and admits a source-relative visit bound. -/
theorem compilerPrefix_tailEntry_alloc_correct
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width) (flag : Bool) (count fc alg k : Nat)
    (col : Option (Spt Nat)) {p : WordLangProgHOL (BitVec width)} (shape : WordTailEntryShape p)
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (K limit : Nat) (locals : Spt (WordLocW width))
    (noInstallCode : WordProps.noInstallCode s.code) (code : TailEntryCodeBound p s.code K)
    (run : evaluate p s = (res,post)) (nonerror : res ≠ some .error) (notTimeout : res ≠ some .timeOut)
    (sourceBound : steps p s ≤ limit) (gc : gcFunConstOk s.gcFun)
    (localRel : wordLocalsRel (maxVarHOL (Flapjack.Compiler.Backend.WordSimp.compileExp p)+1) s.locals locals)
    (domain : sptDomain locals = (fun key => key ∈ evenList count)) :
    let allocated := Flapjack.WordAlloc.wordAlloc fc ac alg k (preAlloc ac flag count p) col
    ∃ selectedLocals targetPost,
      evaluate allocated {s with locals := locals,clock := limit} = (res,targetPost) ∧
      Flapjack.WordAlloc.wordStateEqRel {post with locals := selectedLocals,clock := limit-(s.clock-post.clock)} targetPost ∧
      RegTailShape allocated ∧ RegTailCodeBound allocated s.code K ∧
      steps allocated {s with locals := locals,clock := limit} ≤ sizeOf allocated * (K+1) * (limit+1) := by
  have vars : everyVarHOL (fun x => decide (x < maxVarHOL (Flapjack.Compiler.Backend.WordSimp.compileExp p)+1))
      (Flapjack.Compiler.Backend.WordSimp.compileExp p) = true :=
    everyVarMono _ _ _ ⟨fun x hx => by simp only [decide_eq_true_eq] at hx ⊢; omega,
      Flapjack.Compiler.Backend.WordAlloc.maxVarMax _⟩
  obtain ⟨selectedLocals,ssaPost,finalLocals,finalRun,ssaRel,_,preShape,preCode,_⟩ :=
    SteppedFlapjack.WordDeadSteps.compilerPrefix_tailEntry_secondDead_correct ac flag _ count shape s post res K limit locals
      noInstallCode code run nonerror notTimeout sourceBound gc vars localRel domain
  obtain ⟨targetPost,targetRun,targetRel,_,outShape,outCode,targetBound⟩ :=
    wordAlloc_tailEntry_correct_with_steps fc ac alg k col preShape
      {s with locals := locals,clock := limit} {ssaPost with locals := finalLocals} res K
      noInstallCode preCode finalRun nonerror (evenStartingLocals_of_domain locals count domain)
      (preAlloc_cutsets ac flag count p)
  refine ⟨selectedLocals,targetPost,targetRun,?_,outShape,outCode,targetBound⟩
  exact wordStateEqRel_trans ssaRel
    (wordStateEqRel_trans (wordStateEqRel_locals ssaPost finalLocals) targetRel)

/-- The proved allocated entry is exactly the compiler's full single-function
output, and meets the existing Word-to-Stack call-sequence conventions. -/
theorem fullCompileSingle_tailEntry_correct
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width) (flag : Bool) (count fc alg k : Nat)
    (col : Option (Spt Nat)) {p : WordLangProgHOL (BitVec width)} (shape : WordTailEntryShape p)
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (K limit : Nat) (locals : Spt (WordLocW width))
    (noInstallCode : WordProps.noInstallCode s.code) (code : TailEntryCodeBound p s.code K)
    (run : evaluate p s = (res,post)) (nonerror : res ≠ some .error) (notTimeout : res ≠ some .timeOut)
    (sourceBound : steps p s ≤ limit) (gc : gcFunConstOk s.gcFun)
    (localRel : wordLocalsRel (maxVarHOL (Flapjack.Compiler.Backend.WordSimp.compileExp p)+1) s.locals locals)
    (domain : sptDomain locals = (fun key => key ∈ evenList count)) :
    let out := (Flapjack.Compiler.Backend.WordToWord.fullCompileSingle flag k alg ac ((fc,count,p),col)).2.2
    RegTailShape out ∧ SteppedFlapjack.WordToStackSteps.CallSequence out ∧ noInstallSubprogsHOL out = true ∧
    flatExpConventions out = true ∧ postAllocConventionsHOL k out = true ∧
    ∃ selectedLocals targetPost,
      evaluate out {s with locals := locals,clock := limit} = (res,targetPost) ∧
      Flapjack.WordAlloc.wordStateEqRel {post with locals := selectedLocals,clock := limit-(s.clock-post.clock)} targetPost ∧
      RegTailCodeBound out s.code K ∧ steps out {s with locals := locals,clock := limit} ≤ sizeOf out * (K+1) * (limit+1) := by
  obtain ⟨selectedLocals,targetPost,targetRun,targetRel,outShape,outCode,bound⟩ :=
    compilerPrefix_tailEntry_alloc_correct ac flag count fc alg k col shape s post res K limit locals
      noInstallCode code run nonerror notTimeout sourceBound gc localRel domain
  have eq : (Flapjack.Compiler.Backend.WordToWord.fullCompileSingle flag k alg ac ((fc,count,p),col)).2.2 =
      Flapjack.WordAlloc.wordAlloc fc ac alg k (preAlloc ac flag count p) col := by
    change Flapjack.Compiler.Backend.WordRemove.removeMustTerminate
      (Flapjack.WordAlloc.wordAlloc fc ac alg k (preAlloc ac flag count p) col) = _
    exact removeMustTerminate_regTail outShape
  have conventions := fullCompileSingle_stackConventions ac flag count fc alg k p col
  rw [eq] at conventions
  rw [eq]
  exact ⟨outShape,flat_regTail_callSequence outShape conventions.1,regTail_noInstall outShape,
    conventions.1,conventions.2,selectedLocals,targetPost,targetRun,targetRel,outCode,bound⟩

end SteppedFlapjack.WordAllocSteps
