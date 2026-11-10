import SteppedFlapjack.WordToStackSteps.TailCallZeroClock
import SteppedFlapjack.StackAllocSteps.LoopClockLinear
import SteppedFlapjack.StackRemoveSteps.OraclePrefix

namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.StackSteps SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps
open SteppedFlapjack.StackRemoveSteps.CompCorrect
variable {width : Nat} [NeZero width]

/-- The target prep for resolving a call destination has no recursive control. -/
theorem callDest_straight (dest : Option Nat) (args : List Nat) (kf : Nat × Nat × Nat) :
    straightLine (callDestNative (width := width) dest args kf).1 = true := by
  cases dest with
  | some _ => rfl
  | none =>
    simp only [callDestNative]
    split
    · rfl
    · apply straightLine_stackLoad; rfl

/-- A call-free code tree's maximum structural cost is computable. -/
def loopCodeCost (clock : Nat) (code : Spt (HolProg width)) : Nat :=
  maxListNat ((sptToAList code).map fun entry => linearLoopCost clock entry.2)

theorem loopCodeCost_bound (clock : Nat) (code : Spt (HolProg width))
    (label : Nat) (p : HolProg width) (lookup : sptLookup label code = some p) :
    linearLoopCost clock p ≤ loopCodeCost clock code := by
  have hlist : sptAListLookup label (sptToAList code) = some p := by
    have h := sptLookup_sptFromAList_sptToAList label code
    rw [lookup] at h
    simpa only [sptLookup_sptFromAList] using h
  have hmem := Flapjack.sptAListLookup_mem label (sptToAList code) p hlist
  apply le_maxListNat_of_mem
  exact List.mem_map.mpr ⟨(label, p), hmem, rfl⟩

/-- Resolve any direct or indirect successful target call into its code entry. -/
theorem findCode_entry {C F : Type} (dest : Sum Nat Nat)
    (s : StackSemStateFiniteExact width C F) (p : HolProg width)
    (found : findCode dest s.regs s.code = some p) :
    ∃ label, sptLookup label s.code = some p := by
  cases dest with
  | inl label => exact ⟨label, found⟩
  | inr reg =>
    simp only [findCode] at found
    split at found <;> try contradiction
    rename_i label _
    exact ⟨label, found⟩

/-- A target tail call into a loop-only code tree has a bound computed from
that tree and the current clock. -/
theorem targetTailCall_bound {C F : Type} (dest : Sum Nat Nat)
    (s : StackSemStateFiniteExact width C F)
    (shape : ∀ label p, sptLookup label s.code = some p → loopOnly p = true) :
    steps (.call none dest none, s) ≤ 1 + loopCodeCost s.clock s.code := by
  rw [steps_call_none]
  cases found : findCode dest s.regs s.code with
  | none => simp
  | some p =>
    by_cases zero : s.clock = 0
    · simp [zero]
    · have ⟨label, lookup⟩ := findCode_entry dest s p found
      have cost := linearLoopCostBound s.clock p (shape label p lookup) (decClock s) (by simp [decClock])
      have maxBound := loopCodeCost_bound s.clock s.code label p lookup
      simp only [zero, if_false]
      omega


/-- A uniform-clock version, useful after a call prep has executed. -/
theorem targetTailCall_bound_at {C F : Type} (dest : Sum Nat Nat) (k : Nat)
    (s : StackSemStateFiniteExact width C F) (clockBound : s.clock ≤ k)
    (shape : ∀ label p, sptLookup label s.code = some p → loopOnly p = true) :
    steps (.call none dest none, s) ≤ 1 + loopCodeCost k s.code := by
  rw [steps_call_none]
  cases found : findCode dest s.regs s.code with
  | none => simp
  | some p =>
    by_cases zero : s.clock = 0
    · simp [zero]
    · have ⟨label, lookup⟩ := findCode_entry dest s p found
      have cost := linearLoopCostBound k p (shape label p lookup) (decClock s) (by simp [decClock]; omega)
      have maxBound := loopCodeCost_bound k s.code label p lookup
      simp only [zero, if_false]
      omega

/-- Freeing the caller frame adds at most two structural steps before the call. -/
theorem freeTail_bound {C F : Type} (dest : Sum Nat Nat) (free k : Nat)
    (s : StackSemStateFiniteExact width C F) (clockBound : s.clock ≤ k)
    (shape : ∀ label p, sptLookup label s.code = some p → loopOnly p = true) :
    steps (seqStackFreeNative free (.call none dest none), s) ≤ 3 + loopCodeCost k s.code := by
  unfold seqStackFreeNative
  split
  · have h := targetTailCall_bound_at dest k s clockBound shape
    omega
  · rw [steps_seq]
    have hl : steps (.stackFree free, s) = 1 := steps_leaf _ s rfl
    rw [hl, StackSemEvaluateClock.fixClockEvaluate]
    rw [StackSemEvaluate.evaluate_stackFree]
    by_cases hu : (!s.useStack) = true
    · simp [hu]; omega
    · by_cases hs : s.stack.length < s.stackSpace + free
      · simp [hu, hs]; omega
      · simp only [hu, hs, if_false, Bool.false_eq_true]
        have h := targetTailCall_bound_at dest k {s with stackSpace := s.stackSpace + free} clockBound shape
        simp only at h ⊢
        omega


/-- The whole compiled tail call is bounded by its destination prep plus
frame overhead and the maximum cost of the actual target code entries. -/
theorem compiledTail_bound {C F : Type} (ac : AsmConfigExact width)
    (dest : Option Nat) (args : List Nat) (bs : AppList (BitVec width) × Nat)
    (kf : Nat × Nat × Nat) (s : StackSemStateFiniteExact width C F)
    (shape : ∀ label p, sptLookup label s.code = some p → loopOnly p = true) :
    steps ((compNative ac false (.call none dest args none) bs kf).1, s) ≤
      4 + loopOnlyCost 0 (callDestNative (width := width) dest args kf).1 + loopCodeCost s.clock s.code := by
  have hshape := callDest_straight (width := width) dest args kf
  rcases hcd : callDestNative (width := width) dest args kf with ⟨prep, targetDest⟩
  simp only [hcd] at hshape
  simp only [compNative, hcd]
  rw [steps_seq, StackSemEvaluateClock.fixClockEvaluate]
  have hp := straightLineSteps prep hshape s
  rcases he : StackSemEvaluate.evaluate (prep, s) with ⟨res, post⟩
  cases res with
  | some r => simp only; omega
  | none =>
    have preserved := Flapjack.WordToStackProofs.CallDest.callDest_preserves dest args kf prep targetDest s post hcd he
    have hc := StackSemEvaluateClock.evaluateClock prep s none post he
    have hs : ∀ label p, sptLookup label post.code = some p → loopOnly p = true := by
      simpa only [preserved.2] using shape
    have bound := freeTail_bound targetDest (Compiler.Backend.WordToStack.stackFree targetDest args.length kf.1 kf.2.1 kf.2.2) s.clock post hc hs
    simp only [preserved.2] at bound
    simp only
    omega


/-- Compiling a loop-block function adds only a stack-allocation node. -/
theorem loopOnly_compileProg (ac : AsmConfigExact width) (p : WordLangProgHOL (BitVec width))
    (block : LoopBlock p) (arity k : Nat) (bs : AppList (BitVec width) × Nat) :
    loopOnly (compileProgNative ac false p arity k bs).1 = true := by
  simp only [compileProgNative]
  rcases h : compNative ac false p bs
      (k, if max (maxVarHOL p / 2 + 1 - k) (arity - k) = 0 then 0 else
        max (maxVarHOL p / 2 + 1 - k) (arity - k) + 1,
        max (maxVarHOL p / 2 + 1 - k) (arity - k)) with ⟨body, next⟩
  simp only [loopOnly, Bool.true_and]
  simpa only [h] using loopWord_compiled ac p (loopBlock_loop block) bs
    (k, if max (maxVarHOL p / 2 + 1 - k) (arity - k) = 0 then 0 else
      max (maxVarHOL p / 2 + 1 - k) (arity - k) + 1,
      max (maxVarHOL p / 2 + 1 - k) (arity - k))

/-- Actual related target code is loop-only when all source functions are
loop blocks. The two compiler-generated stubs are checked directly. -/
theorem relatedLoopCode {C F : Type} (ac : AsmConfigExact width) (k f frame : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) (target : StackSemStateFiniteExact width C F)
    (lens : List Nat) (related : Flapjack.WordToStackProofs.stateRel ac k f frame source target lens 0)
    (code : ∀ label arity prog, sptLookup label source.code = some (arity, prog) → LoopBlock prog) :
    ∀ label p, sptLookup label target.code = some p → loopOnly p = true := by
  intro label p lookup
  have rel := related
  unfold Flapjack.WordToStackProofs.stateRel at rel
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, domain, functions, stub1, stub2, _⟩ := rel
  have member : sptDomain target.code label := by simp [sptDomain, lookup]
  rw [domain] at member
  rcases member with h | h | h
  · subst label
    rw [lookup] at stub1
    have eq : p = raiseStubNative false k := Option.some.inj stub1
    subst p
    simp [raiseStubNative, loopOnly]
  · subst label
    rw [lookup] at stub2
    have eq : p = storeConstsStubNative k := Option.some.inj stub2
    subst p
    simp [storeConstsStubNative, loopOnly]
  · cases hlookup : sptLookup label source.code with
    | none => simp [sptDomain, hlookup] at h
    | some entry =>
      rcases entry with ⟨arity, prog⟩
      obtain ⟨_, _, bs, j, bs2, j2, frame2, targetProg, compiled, _, _, _, targetLookup, _⟩ := functions label prog arity hlookup
      have eq : p = targetProg := by rw [lookup] at targetLookup; exact Option.some.inj targetLookup
      subst p
      have shape := loopOnly_compileProg ac prog (code label arity prog hlookup) arity k (bs, j)
      rw [compiled] at shape
      exact shape


/-- A non-error, non-timeout tail call consumes no more clock than its
WordSem step count when its actual callee is a loop block. -/
theorem tailCall_consumed {C F : Type} (dest : Option Nat) (args : List Nat)
    (s post : WordSemStateFiniteExact width (Nat × C) F) (res : Option (WordSemResult width))
    (code : ∀ loc arity prog, sptLookup loc s.code = some (arity, prog) → LoopBlock prog)
    (run : WordSemStateFiniteExact.evaluate (.call none dest args none) s = (res, post))
    (notError : res ≠ some .error) (notTimeout : res ≠ some .timeOut) :
    s.clock - post.clock ≤ WordSteps.steps (.call none dest args none) s := by
  rw [WordSemStateFiniteExact.evaluate] at run
  cases hargs : WordSemStateFiniteExact.getVars args s with
  | none => simp [hargs] at run; exact False.elim (notError run.1.symm)
  | some xs =>
    simp only [hargs] at run
    cases hbad : wordSemBadDestArgs dest args with
    | true => simp [hbad] at run; exact False.elim (notError run.1.symm)
    | false =>
      simp only [hbad, Bool.false_eq_true, if_false, wordSemAddRetLoc] at run
      cases hfind : wordSemFindCode dest xs s.code s.stackSize with
      | none => simp [hfind] at run; exact False.elim (notError run.1.symm)
      | some found =>
        rcases found with ⟨values, callee, ss⟩
        simp only [hfind] at run
        by_cases hz : s.clock = 0
        · simp [hz] at run
          exact False.elim (notTimeout run.1.symm)
        · simp only [hz, ↓reduceDIte] at run
          rcases he : WordSemStateFiniteExact.evaluate callee
              (WordSemStateFiniteExact.callEnv values ss (WordSemStateFiniteExact.decClock s)) with ⟨r, t⟩
          rw [he] at run
          by_cases hb : wordSemBadFunReturn r = true
          · simp [hb] at run
            exact False.elim (notError run.1.symm)
          · simp only [hb, Bool.false_eq_true, if_false, Prod.mk.injEq] at run
            obtain ⟨rfl, rfl⟩ := run
            obtain ⟨loc, lookup, _, _, _⟩ := Flapjack.WordToStackProofs.CompCorrect.CallTail.findCode_facts
              dest xs s.code s.stackSize values callee ss hfind
            have hc := WordSteps.loopWord_consumption callee
              (WordSemStateFiniteExact.callEnv values ss (WordSemStateFiniteExact.decClock s))
              (loopBlock_loop (code loc values.length callee lookup))
            rw [he] at hc
            rw [WordSteps.steps_call_tail dest args s xs values ss callee hargs hbad hfind hz]
            change s.clock - 1 ≤ t.clock + WordSteps.steps callee
              (WordSemStateFiniteExact.callEnv values ss (WordSemStateFiniteExact.decClock s)) at hc
            omega


/-- A non-timeout tail call into loop-block code preserves the compiler result
relation and has a finite target-step bound computed from the source-step
limit, emitted call prefix, and actual related target code tree. -/
theorem tailCall_normalized_bound {C F : Type} (ac : AsmConfigExact width)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (k f frame : Nat) (bs bsPost : AppList (BitVec width)) (n nPost limit : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (code : ∀ loc arity prog, sptLookup loc source.code = some (arity, prog) → LoopBlock prog)
    (notTimeout : result ≠ some .timeOut) (stepsBound : WordSteps.steps (.call none dest args none) source ≤ limit)
    (premises : WordSemStateFiniteExact.evaluate (.call none dest args none) source = (result, sourcePost) ∧
      result ≠ some .error ∧ Flapjack.WordToStackProofs.stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k (.call none dest args none : WordLangProgHOL (BitVec width)) = true ∧ flatExpConventions (.call none dest args none : WordLangProgHOL (BitVec width)) = true ∧
      compNative ac false (.call none dest args none) (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧ n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL (.call none dest args none : WordLangProgHOL (BitVec width)) < 2 * frame + 2 * k) :
    ∃ (targetPost : StackSemStateFiniteExact width C F) (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := limit}) = (targetResult, targetPost) ∧
      Flapjack.WordToStackProofs.CompCorrect.compCorrectResult ac k f frame {source with clock := limit}
        {sourcePost with clock := limit - (source.clock - sourcePost.clock)} targetPost result targetResult lens ∧
      steps (compiled, {target with clock := limit}) ≤
        4 + loopOnlyCost 0 (callDestNative (width := width) dest args (k, f, frame)).1 + loopCodeCost limit target.code := by
  have used := tailCall_consumed dest args source sourcePost result code premises.1 premises.2.1 notTimeout
  have le : source.clock - sourcePost.clock ≤ limit := used.trans stepsBound
  have reduced := WordSemStateFiniteExact.evaluate_dec_clock (.call none dest args none) source result sourcePost premises.1
  have extended := WordSemStateFiniteExact.evaluate_add_clock (limit - (source.clock - sourcePost.clock))
    (.call none dest args none) {source with clock := source.clock - sourcePost.clock} result
      {sourcePost with clock := 0} ⟨reduced, notTimeout⟩
  have eqn : source.clock - sourcePost.clock + (limit - (source.clock - sourcePost.clock)) = limit := by omega
  have normalized : WordSemStateFiniteExact.evaluate (.call none dest args none) {source with clock := limit} =
      (result, {sourcePost with clock := limit - (source.clock - sourcePost.clock)}) := by
    simpa only [eqn, Nat.zero_add] using extended
  have related := stateRel_setClocks ac k f frame source target lens 0 limit premises.2.2.1
  have normalizedCode : ∀ loc arity prog, sptLookup loc ({source with clock := limit}).code = some (arity, prog) → LoopBlock prog := code
  have sim := tailCall_zero_of_code ac dest args {source with clock := limit} normalizedCode
  obtain ⟨post, out, run, relation⟩ := sim k f frame
    {sourcePost with clock := limit - (source.clock - sourcePost.clock)} {target with clock := limit}
    result bs bsPost n nPost compiled lens ⟨normalized, premises.2.1, related, premises.2.2.2⟩
  have shape := relatedLoopCode ac k f frame source target lens premises.2.2.1 code
  have bound := compiledTail_bound ac dest args (bs, n) (k, f, frame) {target with clock := limit} shape
  rw [premises.2.2.2.2.2.1] at bound
  exact ⟨post, out, run, relation, bound⟩

end SteppedFlapjack.WordToStackSteps
