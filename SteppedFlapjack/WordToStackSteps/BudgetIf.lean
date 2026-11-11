import SteppedFlapjack.WordToStackSteps.BudgetSimulation
import SteppedFlapjack.WordToStackSteps.IfZeroClock
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.If
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordToStackRegFormat
/-- Reached conditional branches admit bounded simulations. -/
def BudgetIfHypotheses {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (comparison : Cmp) (register : Nat)
    (operand : WordRegImm (BitVec width))
    (first second : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) (cost : Nat) : Prop :=
  (∀ v3 v4 x y value,
    (WordSemStateFiniteExact.getVar register source,
      WordSemStateFiniteExact.getVarImm operand source) = (v3, v4) ∧
    v3 = some x ∧ v4 = some y ∧ wordSemWordCmp comparison x y = some value ∧
    value = true → BudgetSimulation ac first source cost) ∧
  (∀ v3 v4 x y value,
    (WordSemStateFiniteExact.getVar register source,
      WordSemStateFiniteExact.getVarImm operand source) = (v3, v4) ∧
    v3 = some x ∧ v4 = some y ∧ wordSemWordCmp comparison x y = some value ∧
    ¬ value = true → BudgetSimulation ac second source cost)

/-- Flapjack infrastructure deriving the selected recursive simulation from
actual source execution and its original non-error premise. No branch success
or operand value is assumed independently, and both literal IH guards remain. -/
private theorem budgetSelectedSourceBranch {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (comparison : Cmp) (register : Nat)
    (operand : WordRegImm (BitVec width))
    (first second : WordLangProgHOL (BitVec width))
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width)) (cost : Nat)
    (ih : BudgetIfHypotheses ac comparison register operand first second source cost)
    (execution : WordSemStateFiniteExact.evaluate (.ite comparison register operand first second)
      source = (result, sourcePost))
    (nonerror : result ≠ some .error) :
    ∃ x y value,
      WordSemStateFiniteExact.getVar register source = some x ∧
      WordSemStateFiniteExact.getVarImm operand source = some y ∧
      wordSemWordCmp comparison x y = some value ∧
      WordSemStateFiniteExact.evaluate (if value then first else second) source =
        (result, sourcePost) ∧
      BudgetSimulation ac (if value then first else second) source cost := by
  cases left : WordSemStateFiniteExact.getVar register source with
  | none => simp [WordSemStateFiniteExact.evaluate, left] at execution; cases nonerror execution.1.symm
  | some x =>
    cases right : WordSemStateFiniteExact.getVarImm operand source with
    | none => simp [WordSemStateFiniteExact.evaluate, left, right] at execution; cases nonerror execution.1.symm
    | some y =>
      cases compared : wordSemWordCmp comparison x y with
      | none => simp [WordSemStateFiniteExact.evaluate, left, right, compared] at execution; cases nonerror execution.1.symm
      | some value =>
        refine ⟨x, y, value, rfl, rfl, compared, ?_, ?_⟩
        · cases value <;> simpa [WordSemStateFiniteExact.evaluate, left, right, compared] using execution
        · cases value
          · exact ih.2 _ _ x y false ⟨by simp [left, right], rfl, rfl, compared, by decide⟩
          · exact ih.1 _ _ x y true ⟨by simp [left, right], rfl, rfl, compared, rfl⟩

private theorem physicalOperandEven {width : Nat} [NeZero width]
    (operand : WordRegImm (BitVec width))
    (physical : everyVarImmHOL isPhyVar operand = true) :
    OperandEven operand := by
  cases operand with
  | reg other => simpa [everyVarImmHOL,isPhyVar,OperandEven] using physical
  | imm word => trivial


/-- Conditional compilation preserves a common explicit branch budget. -/
theorem budgetIf {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (comparison : Cmp) (register : Nat)
    (operand : WordRegImm (BitVec width))
    (first second : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (cost : Nat) (ih : BudgetIfHypotheses ac comparison register operand first second source cost) :
    BudgetSimulation ac (.ite comparison register operand first second) source cost := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises reserve
  rcases premises with ⟨execution, notError, notTimeout, related, conventions, flat,
    compilation, lengthBound, bitmapBound, bitmapPrefix, labels, maxBound⟩
  obtain ⟨x,y,value,left,right,compared,selectedRun,selectedIH⟩ :=
    budgetSelectedSourceBranch ac comparison register operand first second source sourcePost result cost ih execution notError
  have conventionParts := conventions
  simp only [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
    callArgConventionHOL,Bool.and_eq_true] at conventionParts
  rcases conventionParts with ⟨⟨⟨⟨leftPhy,rightPhy⟩,firstVar⟩,secondVar⟩,
    ⟨⟨firstStack,secondStack⟩,⟨firstCall,secondCall⟩⟩⟩
  have leftEven : register % 2 = 0 := by simpa [isPhyVar] using leftPhy
  have rightEven := physicalOperandEven operand rightPhy
  obtain ⟨loaded,loadedRel,sameClock,bitmapMono,codeMono,routing⟩ :=
    prepareCondition ac comparison register operand k f frame source target lens x y value
      related leftEven rightEven left right compared
  rcases firstCompile : compNative ac false first (bs,n) (k,f,frame) with ⟨q1,middle⟩
  rcases secondCompile : compNative ac false second middle (k,f,frame) with ⟨q2,after⟩
  have compiledFactor := compileCondition ac comparison register operand (k,f,frame)
    first second (bs,n) middle after q1 q2 firstCompile secondCompile
  obtain ⟨compiledEq,bitmapEq⟩ := Prod.mk.inj (compiledFactor.symm.trans compilation)
  subst compiled
  have firstAccounting := compImpLength ac false first (bs,n) (k,f,frame) q1 middle
    ⟨firstCompile,lengthBound⟩
  have selectedConventions : postAllocConventionsHOL k (if value then first else second) = true := by
    cases value <;> simp [postAllocConventionsHOL,firstVar,secondVar,firstStack,secondStack,firstCall,secondCall]
  have selectedFlat : flatExpConventions (if value then first else second) = true := by
    simp only [flatExpConventions,Bool.and_eq_true] at flat
    cases value <;> simp [flat.1,flat.2]
  have selectedMax : maxVarHOL (if value then first else second) < 2*frame+2*k := by
    unfold maxVarHOL at maxBound
    have max3Eq (a b c : Nat) : max3HOL a b c = max a (max b c) := by
      unfold max3HOL
      split_ifs <;> omega
    rw [max3Eq] at maxBound
    cases value <;> simp only [Bool.false_eq_true,if_false,if_true] <;> omega
  have selectedCompile :
      compNative ac false (if value then first else second)
        (if value then (bs,n) else middle) (k,f,frame) =
      (if value then q1 else q2, if value then middle else after) := by
    cases value <;> simp [firstCompile,secondCompile]
  have selectedLength : (appListAppend (if value then (bs,n) else middle).1).length ≤
      (if value then (bs,n) else middle).2 := by
    cases value <;> simp [lengthBound,firstAccounting.1]
  have selectedGap : (if value then (bs,n) else middle).2 -
      (appListAppend (if value then (bs,n) else middle).1).length = n-(appListAppend bs).length := by
    cases value <;> simp [firstAccounting.2]
  have selectedBitmapBound : (if value then (bs,n) else middle).2 -
      (appListAppend (if value then (bs,n) else middle).1).length ≤ loaded.bitmaps.length := by
    rw [selectedGap]
    exact bitmapBound.trans bitmapMono.length_le
  have selectedPrefix : (appListAppend (if value then middle else after).1).IsPrefix
      (loaded.bitmaps.drop ((if value then (bs,n) else middle).2 -
        (appListAppend (if value then (bs,n) else middle).1).length)) := by
    rw [selectedGap]
    have finalPrefix : (appListAppend after.1).IsPrefix
        (loaded.bitmaps.drop (n-(appListAppend bs).length)) := by
      rw [bitmapEq]
      exact bitmapPrefix.trans (bitmapMono.drop _)
    cases value
    · exact finalPrefix
    · exact (compImpIsPrefix ac false second middle (k,f,frame) q2 after secondCompile).trans finalPrefix
  have selectedLabels : ∀ loc, StackSem.getLabelsExact (if value then q1 else q2) loc →
      StackSem.locCheckExact loaded.code loc := by
    intro loc member
    apply LocationLabels.locCheckSubset target.code loaded.code codeMono loc
    apply labels loc
    apply (conditionLabels ac comparison register operand (k,f,frame) q1 q2 loc).2
    cases value
    · exact Or.inr member
    · exact Or.inl member
  obtain ⟨post,targetResult,targetRun,enough,accounting,conclusion⟩ :=
    selectedIH k f frame sourcePost loaded result
      (if value then (bs,n) else middle).1 (if value then middle else after).1
      (if value then (bs,n) else middle).2 (if value then middle else after).2
      (if value then q1 else q2) lens
      ⟨selectedRun,notError,notTimeout,loadedRel,selectedConventions,selectedFlat,selectedCompile,
        selectedLength,selectedBitmapBound,selectedPrefix,selectedLabels,selectedMax⟩ reserve
  refine ⟨post,targetResult,?_,enough,accounting,conclusion⟩
  rw [routing q1 q2 (target.clock + cost + reserve),sameClock]
  exact targetRun



end SteppedFlapjack.WordToStackSteps
