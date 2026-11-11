import SteppedFlapjack.WordToStackSteps.ClockSlack
import SteppedFlapjack.WordToStackSteps.LoopZeroClock
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-- A compiler simulation with a concrete extra clock budget and a preserved
reserve for subsequent execution. -/
def BudgetSimulation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (program : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) (cost : Nat) : Prop :=
  ∀ (k f frame : Nat)
    (sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat),
    (WordSemStateFiniteExact.evaluate program source = (result, sourcePost) ∧
      result ≠ some .error ∧ result ≠ some .timeOut ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k program = true ∧ flatExpConventions program = true ∧
      compNative ac false program (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL program < 2 * frame + 2 * k) →
    ∀ reserve : Nat, ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + cost + reserve}) =
        (targetResult, targetPost) ∧
      reserve ≤ targetPost.clock ∧
      (targetResult = some (.halt (.word 2)) ∨
        (sourcePost.clock + reserve ≤ targetPost.clock ∧ targetPost.clock ≤ sourcePost.clock + cost + reserve)) ∧
      compCorrectResult ac k f frame source sourcePost {targetPost with clock := sourcePost.clock} result targetResult lens

theorem zeroBudget {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (p : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (h : ZeroSimulation ac p source) : BudgetSimulation ac p source 0 := by
  intro k f frame post target res bs bsPost n nPost compiled lens premises reserve
  obtain ⟨run, ne, nt, rest⟩ := premises
  obtain ⟨targetPost, out, targetRun, enough, accounting, conclusion⟩ :=
    zeroSimulation_addSlack ac p source h k f frame post target res bs bsPost n nPost compiled lens reserve nt ⟨run,ne,rest⟩
  refine ⟨targetPost,out,by simpa using targetRun,enough,?_,?_⟩
  · rcases accounting with limit | clock
    · exact Or.inl limit
    · right; constructor <;> omega
  · simpa using compCorrectResult_setClocks ac k f frame source post
      {targetPost with clock := targetPost.clock-reserve} res out lens post.clock conclusion

theorem raiseBudget {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (name : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) : BudgetSimulation ac (.raise name) source 1 := by
  intro k f frame post target res bs bsPost n nPost compiled lens premises reserve
  obtain ⟨run, ne, nt, rest⟩ := premises
  obtain ⟨targetPost, out, targetRun, enough, accounting, conclusion⟩ :=
    raise_oneClock_addSlack ac name source k f frame post target res bs bsPost n nPost compiled lens ⟨run,ne,rest⟩ reserve
  refine ⟨targetPost,out,targetRun,enough,?_,?_⟩
  · rcases accounting with limit | clock
    · exact Or.inl limit
    · right; constructor <;> omega
  · simpa using compCorrectResult_setClocks ac k f frame source post
      {targetPost with clock := targetPost.clock-reserve} res out lens post.clock conclusion




private theorem budgetSeqFirstNonNone {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (first second : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) (firstCost secondCost : Nat)
    (ih : (∀ result middle,
      (result, middle) = WordSemStateFiniteExact.evaluate first source ∧ result = none →
        BudgetSimulation ac second middle secondCost) ∧ BudgetSimulation ac first source firstCost)
    (firstNonNone : (WordSemStateFiniteExact.evaluate first source).1 ≠ none) :
    BudgetSimulation ac (.seq first second) source (firstCost + secondCost) := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises reserve
  rcases premises with ⟨execution, notError, notTimeout, related, conventions, flat,
    compilation, lengthBound, bitmapBound, bitmapPrefix, labels, maxBound⟩
  rcases firstCompile : compNative ac false first (bs, n) (k, f, frame) with
    ⟨firstCode, middleBitmaps⟩
  rcases secondCompile : compNative ac false second middleBitmaps (k, f, frame) with
    ⟨secondCode, finalBitmaps⟩
  simp only [compNative, firstCompile, secondCompile] at compilation
  obtain ⟨compiledEq, bitmapEq⟩ := Prod.mk.inj compilation
  subst compiled
  have firstPrefix := compImpIsPrefix ac false second middleBitmaps (k, f, frame)
    secondCode finalBitmaps secondCompile
  rw [bitmapEq] at firstPrefix
  have firstLabels : ∀ loc, StackSem.getLabelsExact firstCode loc →
      StackSem.locCheckExact target.code loc := by
    intro loc member
    apply labels loc
    rw [StackSem.getLabelsExact]
    exact Or.inl member
  have firstConventions : postAllocConventionsHOL k first = true := by
    simp only [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL,
      callArgConventionHOL, Bool.and_eq_true] at conventions ⊢
    exact ⟨conventions.1.1, conventions.2.1.1, conventions.2.2.1⟩
  have firstFlat : flatExpConventions first = true := by
    simp only [flatExpConventions, Bool.and_eq_true] at flat
    exact flat.1
  have firstMax : maxVarHOL first < 2 * frame + 2 * k := by
    simp only [maxVarHOL] at maxBound
    omega
  rw [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.fix_clock_evaluate] at execution
  rcases firstRun : WordSemStateFiniteExact.evaluate first source with ⟨firstResult, middle⟩
  rw [firstRun] at firstNonNone execution
  cases firstResult with
  | none => exact False.elim (firstNonNone rfl)
  | some value =>
    obtain ⟨resultEq, sourceEq⟩ := Prod.mk.inj execution
    subst result
    subst sourcePost
    obtain ⟨targetPost, targetResult, targetRun, reserveBound, clockAccounting, conclusion⟩ :=
      ih.2 k f frame middle target (some value) bs middleBitmaps.1 n middleBitmaps.2
        firstCode lens ⟨firstRun, notError, notTimeout, related, firstConventions, firstFlat,
          firstCompile, lengthBound, bitmapBound, firstPrefix.trans bitmapPrefix,
          firstLabels, firstMax⟩ (secondCost + reserve)
    have targetNonNone : targetResult ≠ none := by
      intro eq
      subst targetResult
      simp [compCorrectResult] at conclusion
    refine ⟨targetPost, targetResult, ?_, by omega, ?_, conclusion⟩
    · rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
      simp only [Nat.add_assoc] at targetRun ⊢
      rw [targetRun]
      cases targetResult with
      | none => exact False.elim (targetNonNone rfl)
      | some output => rfl
    · rcases clockAccounting with limit | enough
      · exact Or.inl limit
      · right; omega



private theorem budgetSeqFirstNone {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (first second : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) (firstCost secondCost : Nat)
    (ih : (∀ result middle,
      (result, middle) = WordSemStateFiniteExact.evaluate first source ∧ result = none →
        BudgetSimulation ac second middle secondCost) ∧ BudgetSimulation ac first source firstCost)
    (firstNone : (WordSemStateFiniteExact.evaluate first source).1 = none) :
    BudgetSimulation ac (.seq first second) source (firstCost + secondCost) := by
  classical
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises reserve
  rcases premises with ⟨execution, notError, notTimeout, related, conventions, flat,
    compilation, lengthBound, bitmapBound, bitmapPrefix, labels, maxBound⟩
  rcases firstCompile : compNative ac false first (bs, n) (k, f, frame) with
    ⟨firstCode, middleBitmaps⟩
  rcases secondCompile : compNative ac false second middleBitmaps (k, f, frame) with
    ⟨secondCode, finalBitmaps⟩
  simp only [compNative, firstCompile, secondCompile] at compilation
  obtain ⟨compiledEq, bitmapEq⟩ := Prod.mk.inj compilation
  subst compiled
  have firstPrefix := compImpIsPrefix ac false second middleBitmaps (k, f, frame)
    secondCode finalBitmaps secondCompile
  rw [bitmapEq] at firstPrefix
  have firstLabels : ∀ loc, StackSem.getLabelsExact firstCode loc →
      StackSem.locCheckExact target.code loc := by
    intro loc member
    apply labels loc
    rw [StackSem.getLabelsExact]
    exact Or.inl member
  have firstConventions : postAllocConventionsHOL k first = true := by
    simp only [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL,
      callArgConventionHOL, Bool.and_eq_true] at conventions ⊢
    exact ⟨conventions.1.1, conventions.2.1.1, conventions.2.2.1⟩
  have firstFlat : flatExpConventions first = true := by
    simp only [flatExpConventions, Bool.and_eq_true] at flat
    exact flat.1
  have firstMax : maxVarHOL first < 2 * frame + 2 * k := by
    simp only [maxVarHOL] at maxBound
    omega
  have secondConventions : postAllocConventionsHOL k second = true := by
    simp only [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL,
      callArgConventionHOL, Bool.and_eq_true] at conventions ⊢
    exact ⟨conventions.1.2, conventions.2.1.2, conventions.2.2.2⟩
  have secondFlat : flatExpConventions second = true := by
    simp only [flatExpConventions, Bool.and_eq_true] at flat
    exact flat.2
  have secondMax : maxVarHOL second < 2 * frame + 2 * k := by
    simp only [maxVarHOL] at maxBound
    omega
  rw [WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.fix_clock_evaluate] at execution
  rcases firstRun : WordSemStateFiniteExact.evaluate first source with ⟨firstResult, middle⟩
  rw [firstRun] at firstNone execution
  cases firstResult with
  | some value => cases firstNone
  | none =>
    obtain ⟨targetMiddle, firstTargetResult, targetRun, firstReserve, firstAccounting, firstConclusion⟩ :=
      ih.2 k f frame middle target none bs middleBitmaps.1 n middleBitmaps.2
        firstCode lens ⟨firstRun, by simp, by simp, related, firstConventions, firstFlat,
          firstCompile, lengthBound, bitmapBound, firstPrefix.trans bitmapPrefix,
          firstLabels, firstMax⟩ (secondCost + reserve)
    cases firstTargetResult with
    | some value =>
      simp [compCorrectResult] at firstConclusion
      rcases firstConclusion with ⟨valueEq, events, resource⟩
      subst value
      have finalEvents := WordSemStateFiniteExact.evaluate_io_events_mono
        second middle result sourcePost execution
      have resourceThe : miscThe (middle.stackLimit + 1) middle.stackMax > middle.stackLimit := by
        cases h : middle.stackMax <;> simp_all [miscThe]
      have finalResourceThe := WordSemStateFiniteExact.evaluate_stack_limit_stack_max
        second middle result sourcePost ⟨execution, resourceThe⟩
      have finalResource : sourcePost.stackMax.getD (sourcePost.stackLimit + 1) >
          sourcePost.stackLimit := by
        cases h : sourcePost.stackMax <;> simp_all [miscThe]
      have dimension : goodDimindex width := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have mismatch : result.map compileResult ≠ some (.halt (.word 2)) := by
        cases result with
        | none => simp
        | some value =>
          simp only [Option.map_some, ne_eq, Option.some.injEq]
          exact Ne.symm ((haltEqCompileResult value).2 dimension)
      refine ⟨targetMiddle, some (.halt (.word 2)), ?_, by omega, Or.inl rfl, ?_⟩
      · rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
        simp only [Nat.add_assoc] at targetRun ⊢
        rw [targetRun]
        rfl
      · unfold compCorrectResult
        split
        · exact ⟨rfl, events.trans finalEvents, finalResource⟩
        · rename_i equal
          exact False.elim (mismatch (by simpa using equal))
    | none =>
      simp only [compCorrectResult, Option.map_none, ne_eq, not_true_eq_false,
        ↓reduceIte] at firstConclusion
      have accounting := compImpLength ac false first (bs, n) (k, f, frame)
        firstCode middleBitmaps ⟨firstCompile, lengthBound⟩
      have mono := Flapjack.Compiler.Backend.StackProps.EvaluateMono.evaluateMono
        firstCode {target with clock := target.clock + firstCost + (secondCost + reserve)} targetMiddle none targetRun
      have gap := accounting.2
      have secondBitmapBound : middleBitmaps.2 - (appListAppend middleBitmaps.1).length ≤
          targetMiddle.bitmaps.length := by
        rw [← gap]
        exact bitmapBound.trans mono.1.length_le
      have secondPrefix : (appListAppend finalBitmaps.1).IsPrefix
          (targetMiddle.bitmaps.drop
            (middleBitmaps.2 - (appListAppend middleBitmaps.1).length)) := by
        rw [← gap, bitmapEq]
        exact bitmapPrefix.trans (mono.1.drop _)
      have secondLabels : ∀ loc, StackSem.getLabelsExact secondCode loc →
          StackSem.locCheckExact targetMiddle.code loc := by
        intro loc member
        apply LocationLabels.locCheckSubset target.code targetMiddle.code mono.2 loc
        apply labels loc
        rw [StackSem.getLabelsExact]
        exact Or.inr member
      have enough : middle.clock + (secondCost + reserve) ≤ targetMiddle.clock := by
        rcases firstAccounting with impossible | enough
        · simp at impossible
        · exact enough.1
      let remaining := targetMiddle.clock - middle.clock - secondCost
      have remainingBound : reserve ≤ remaining := by dsimp [remaining]; omega
      have remainingEq : middle.clock + secondCost + remaining = targetMiddle.clock := by dsimp [remaining]; omega
      obtain ⟨targetPost, targetResult, secondRun, secondReserve, secondAccounting, conclusion⟩ :=
        ih.1 none middle ⟨firstRun.symm, rfl⟩ k f frame sourcePost {targetMiddle with clock := middle.clock}
          result middleBitmaps.1 finalBitmaps.1 middleBitmaps.2 finalBitmaps.2
          secondCode lens ⟨execution, notError, notTimeout, firstConclusion, secondConventions,
            secondFlat, secondCompile, accounting.1, secondBitmapBound, secondPrefix,
            secondLabels, secondMax⟩ remaining
      have handlerEq : middle.handler = source.handler := by
        have preserved := WordSemStackEq.evaluateStackSwap first source
        unfold WordSemStackEq.stackSwapPost at preserved
        rw [firstRun] at preserved
        exact preserved.2.1
      have finalConclusion : compCorrectResult ac k f frame source sourcePost
          {targetPost with clock := sourcePost.clock} result targetResult lens := by
        unfold compCorrectResult at conclusion ⊢
        rw [handlerEq] at conclusion
        exact conclusion
      refine ⟨targetPost, targetResult, ?_, by omega, ?_, finalConclusion⟩
      · rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
        simp only [Nat.add_assoc] at targetRun ⊢
        rw [targetRun]
        simpa only [remainingEq] using secondRun
      · rcases secondAccounting with limit | enough
        · exact Or.inl limit
        · rcases enough with ⟨lower, upper⟩
          rcases firstAccounting with limit | firstBounds
          · simp at limit
          · right; constructor <;> omega


/-- A larger concrete budget preserves a bounded simulation. -/
theorem budgetMono {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (p : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) (old new : Nat)
    (h : BudgetSimulation ac p source old) (le : old ≤ new) : BudgetSimulation ac p source new := by
  intro k f frame post target res bs bsPost n nPost compiled lens premises reserve
  obtain ⟨targetPost, out, run, enough, accounting, relation⟩ :=
    h k f frame post target res bs bsPost n nPost compiled lens premises (new - old + reserve)
  have eq : target.clock + old + (new - old + reserve) = target.clock + new + reserve := by omega
  refine ⟨targetPost, out, by simpa only [eq] using run, by omega, ?_, relation⟩
  rcases accounting with limit | enough
  · exact Or.inl limit
  · right; omega


/-- Explicit budgets compose through sequences, preserving unused allowance
when an earlier instruction exits. -/
theorem budgetSeq {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (a b : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) (firstCost secondCost : Nat)
    (first : BudgetSimulation ac a source firstCost)
    (second : ∀ result middle,
      (result, middle) = WordSemStateFiniteExact.evaluate a source ∧ result = none →
        BudgetSimulation ac b middle secondCost) :
    BudgetSimulation ac (.seq a b) source (firstCost + secondCost) := by
  by_cases h : (WordSemStateFiniteExact.evaluate a source).1 = none
  · exact budgetSeqFirstNone ac a b source firstCost secondCost ⟨second, first⟩ h
  · exact budgetSeqFirstNonNone ac a b source firstCost secondCost ⟨second, first⟩ h

/-- Count the raises in a sequence, giving a computable extra-clock budget. -/
def sequenceRaiseBudget {width : Nat} [NeZero width] : WordLangProgHOL (BitVec width) → Nat
  | .seq a b => sequenceRaiseBudget a + sequenceRaiseBudget b
  | .raise _ => 1
  | _ => 0

/-- Sequences of zero-clock loop blocks and raises. -/
inductive RaiseSequence {width : Nat} [NeZero width] : WordLangProgHOL (BitVec width) → Prop
  | loopBlock {p} : LoopBlock p → RaiseSequence p
  | raise (name) : RaiseSequence (.raise name)
  | seq {a b} : RaiseSequence a → RaiseSequence b → RaiseSequence (.seq a b)

private theorem loopBlock_raiseBudget {width : Nat} [NeZero width]
    {p : WordLangProgHOL (BitVec width)} (h : LoopBlock p) : sequenceRaiseBudget p = 0 := by
  induction h <;> simp_all [sequenceRaiseBudget]

/-- Every raise sequence has a source-derived, explicit target clock budget. -/
theorem raiseSequence_budget {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (p : WordLangProgHOL (BitVec width))
    (h : RaiseSequence p) (source : WordSemStateFiniteExact width (Nat × C) F) :
    BudgetSimulation ac p source (sequenceRaiseBudget p) := by
  induction h generalizing source with
  | loopBlock h =>
    rw [loopBlock_raiseBudget h]
    exact zeroBudget ac _ source (loopBlock_zero ac _ source h)
  | raise name => exact raiseBudget ac name source
  | seq ha hb iha ihb =>
    exact budgetSeq ac _ _ source _ _ (iha source) (fun _ middle _ => ihb middle)

/-- Maximum sequence raise budget in an actual Word code table. -/
def sequenceRaiseCodeBudget {width : Nat} [NeZero width]
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) : Nat :=
  (sptToAList code).foldr (fun row limit => max (sequenceRaiseBudget row.2.2) limit) 0

/-- A looked-up function is bounded by its table's computed raise budget. -/
theorem sequenceRaiseCodeBudget_lookup {width : Nat} [NeZero width]
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) (loc arity : Nat)
    (body : WordLangProgHOL (BitVec width)) (found : sptLookup loc code = some (arity,body)) :
    sequenceRaiseBudget body ≤ sequenceRaiseCodeBudget code := by
  have member : (loc,(arity,body)) ∈ sptToAList code :=
    (sptToAList_mem_iff_lookup code loc (arity,body)).mpr found
  have aux (rows : List (Nat × (Nat × WordLangProgHOL (BitVec width)))) : ∀ row ∈ rows,
      sequenceRaiseBudget row.2.2 ≤ rows.foldr (fun row limit => max (sequenceRaiseBudget row.2.2) limit) 0 := by
    induction rows with
    | nil => simp
    | cons row rest ih =>
      intro entry member
      simp only [List.mem_cons] at member
      cases member with
      | inl same => subst entry; simp
      | inr restMem => exact (ih entry restMem).trans (Nat.le_max_right _ _)
  exact aux _ _ member

end SteppedFlapjack.WordToStackSteps
