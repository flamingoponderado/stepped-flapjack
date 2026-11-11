import SteppedFlapjack.WordToStackSteps.BudgetHandler
import SteppedFlapjack.WordToStackSteps.BudgetTailCall
import SteppedFlapjack.WordToStackSteps.BudgetIf
import SteppedFlapjack.WordSimpSteps.LoopSequenceClock
import SteppedFlapjack.StackSteps.TableBound
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps SteppedFlapjack.WordSimpSteps
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-- Word programs built from loop blocks, raises, branches, and calls. -/
inductive CallBudgetBlock {width : Nat} [NeZero width] : WordLangProgHOL (BitVec width) → Prop
  | base {p} : LoopBlock p → CallBudgetBlock p
  | raise (name) : CallBudgetBlock (.raise name)
  | seq {a b} : CallBudgetBlock a → CallBudgetBlock b → CallBudgetBlock (.seq a b)
  | ite (cmp r ri) {a b} : CallBudgetBlock a → CallBudgetBlock b → CallBudgetBlock (.ite cmp r ri a b)
  | tail (dest args) : CallBudgetBlock (.call none dest args none)
  | call (values names l1 l2 dest args) {body} : CallBudgetBlock body →
      CallBudgetBlock (.call (some (values,names,body,l1,l2)) dest args none)
  | handler (values names l1 l2 dest args hvar h1 h2) {body catchCode} :
      CallBudgetBlock body → CallBudgetBlock catchCode →
      CallBudgetBlock (.call (some (values,names,body,l1,l2)) dest args (some (hvar,catchCode,h1,h2)))

/-- An explicit compiler clock allowance from the actual code-table weight
and the initial Word clock. -/
def callTableBudget {width : Nat} [NeZero width] {C F : Type}
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) : Nat :=
  wordControlWeight p * (wordCodeWeight s.code + 1) ^ (s.clock + 1)

private theorem wordControlWeight_pos {width : Nat} [NeZero width] (p : WordLangProgHOL (BitVec width)) :
    1 ≤ wordControlWeight p := by
  cases p <;> (try simp only [wordControlWeight]) <;> (try omega)
  case call ret dest args handler =>
    cases ret <;> cases handler <;> simp [wordControlWeight]
    all_goals omega

/-- Whole-table compiler simulation for nested calls and continuations, with
an explicit budget computed from the function table and source clock. -/
theorem callBudgetBlock_simulation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (p : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width (Nat × C) F)
    (shape : CallBudgetBlock p) (noMt : noMtSubprogsHOL p = true)
    (noInstall : noInstallSubprogsHOL p = true) (safe : safeWordCode s)
    (table : ∀ loc arity body, sptLookup loc s.code = some (arity,body) → CallBudgetBlock body) :
    BudgetSimulation ac p s (callTableBudget p s) := by
  cases shape with
  | base block =>
    exact budgetMono ac p s 0 _ (zeroBudget ac p s (loopBlock_zero ac p s block)) (by omega)
  | raise name =>
    apply budgetMono ac _ s 1 _ (raiseBudget ac name s)
    have hp : 0 < (wordCodeWeight s.code + 1) ^ (s.clock + 1) := Nat.pow_pos (by omega)
    simp only [callTableBudget,wordControlWeight,Nat.one_mul]
    omega
  | @seq a b ha hb =>
    simp only [noMtSubprogsHOL, noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] at noMt noInstall
    have first := callBudgetBlock_simulation ac a s ha noMt.1 noInstall.1 safe table
    rcases run : evaluate a s with ⟨res,middle⟩
    cases res with
    | none =>
      have code := code_evaluate a s noInstall.1 safe.2
      rw [run] at code
      have codeEq : middle.code = s.code := code
      have middleSafe : safeWordCode middle := by simpa [safeWordCode,codeEq] using safe
      have middleTable : ∀ loc arity body, sptLookup loc middle.code = some (arity,body) → CallBudgetBlock body := by rw [codeEq]; exact table
      have clk := (evaluate_clock a s none middle run).1
      have second := callBudgetBlock_simulation ac b middle hb noMt.2 noInstall.2 middleSafe middleTable
      have powLe : (wordCodeWeight s.code + 1) ^ (middle.clock + 1) ≤
          (wordCodeWeight s.code + 1) ^ (s.clock + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      apply budgetMono ac _ s (callTableBudget a s + callTableBudget b middle) _
        (budgetSeq ac a b s _ _ first ?_) ?_
      · intro result middle' guard
        rw [run] at guard
        cases guard.1
        exact second
      · simp only [callTableBudget,wordControlWeight,codeEq]
        have bb := Nat.mul_le_mul_left (wordControlWeight b) powLe
        simp only [Nat.add_mul,Nat.one_mul]
        omega
    | some v =>
      apply budgetMono ac _ s (callTableBudget a s + 0) _
        (budgetSeq ac a b s _ _ first ?_) ?_
      · intro result middle' guard
        rw [run] at guard
        have impossible := congrArg Prod.fst guard.1
        rw [guard.2] at impossible
        cases impossible
      · simp only [callTableBudget,wordControlWeight]
        have hp : 0 < (wordCodeWeight s.code + 1) ^ (s.clock + 1) := Nat.pow_pos (by omega)
        nlinarith
  | @ite cmp r ri a b ha hb =>
    simp only [noMtSubprogsHOL,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] at noMt noInstall
    apply budgetIf ac cmp r ri a b s (callTableBudget (.ite cmp r ri a b) s)
    constructor
    · intro v3 v4 x y value guard
      have child := callBudgetBlock_simulation ac a s ha noMt.1 noInstall.1 safe table
      apply budgetMono ac a s _ _ child
      simp only [callTableBudget,wordControlWeight]
      apply Nat.mul_le_mul_right
      omega
    · intro v3 v4 x y value guard
      have child := callBudgetBlock_simulation ac b s hb noMt.2 noInstall.2 safe table
      apply budgetMono ac b s _ _ child
      simp only [callTableBudget,wordControlWeight]
      apply Nat.mul_le_mul_right
      omega
  | tail dest args =>
    apply budgetCallTail ac dest args none s (callTableBudget (.call none dest args none) s)
    intro xs args1 prog ss guard
    obtain ⟨hargs,hbad,hfind,_,hclock⟩ := guard
    obtain ⟨loc,found,_,_,_⟩ := Flapjack.WordToStackProofs.CompCorrect.CallTail.findCode_facts dest _ s.code s.stackSize args1 prog ss hfind
    let child := callEnv args1 ss (decClock s)
    have childCode : child.code = s.code := rfl
    have childClock : child.clock < s.clock := by simp only [child,WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.decClock]; omega
    have childSafe : safeWordCode child := by simpa [safeWordCode,childCode] using safe
    have childTable : ∀ loc arity body, sptLookup loc child.code = some (arity,body) → CallBudgetBlock body := by rw [childCode]; exact table
    have childShape := table loc args1.length prog found
    have childNoMt := safe.1 loc args1.length prog found
    have childNoInstall := safe.2 loc args1.length prog found
    have sim := callBudgetBlock_simulation ac prog child childShape childNoMt childNoInstall childSafe childTable
    apply budgetMono ac prog child _ _ sim
    have weight := wordCodeWeight_lookup s.code loc args1.length prog found
    have powLe : (wordCodeWeight s.code+1)^(child.clock+1) ≤ (wordCodeWeight s.code+1)^s.clock :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have bound := Nat.mul_le_mul weight powLe
    simp only [callTableBudget,childCode,wordControlWeight,Nat.add_zero,Nat.one_mul]
    rw [Nat.pow_succ (wordCodeWeight s.code+1) s.clock]
    apply bound.trans
    rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm ((wordCodeWeight s.code+1)^s.clock) (wordCodeWeight s.code)]
    omega
  | @call values names l1 l2 dest args body hb =>
    simp only [noMtSubprogsHOL,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] at noMt noInstall
    let power := (wordCodeWeight s.code + 1) ^ s.clock
    let bodyCost := wordCodeWeight s.code * power
    let contCost := wordControlWeight body * power
    have retSim : ∀ t : WordSemStateFiniteExact width (Nat × C) F,
        t.clock < s.clock → (safeWordCode s → safeWordCode t ∧ t.code = s.code) →
        BudgetSimulation ac body t contCost := by
      intro t smaller transfer
      obtain ⟨safeT,codeEq⟩ := transfer safe
      have shapeT : ∀ loc arity prog, sptLookup loc t.code = some (arity,prog) → CallBudgetBlock prog := by rw [codeEq]; exact table
      have child := callBudgetBlock_simulation ac body t hb noMt.1.2 noInstall.1.2 safeT shapeT
      apply budgetMono ac body t _ _ child
      have powLe : (wordCodeWeight s.code+1)^(t.clock+1) ≤ power :=
        Nat.pow_le_pow_right (by omega) (by omega)
      simpa [callTableBudget,codeEq,contCost] using Nat.mul_le_mul_left (wordControlWeight body) powLe
    have codeSim : ∀ loc arity prog, sptLookup loc s.code = some (arity,prog) →
        ∀ t : WordSemStateFiniteExact width (Nat × C) F,
          t.clock < s.clock → (safeWordCode s → safeWordCode t ∧ t.code = s.code) →
          BudgetSimulation ac prog t bodyCost := by
      intro loc arity prog found t smaller transfer
      obtain ⟨safeT,codeEq⟩ := transfer safe
      have shapeT : ∀ loc arity prog, sptLookup loc t.code = some (arity,prog) → CallBudgetBlock prog := by rw [codeEq]; exact table
      have child := callBudgetBlock_simulation ac prog t (table loc arity prog found) (safe.1 loc arity prog found)
        (safe.2 loc arity prog found) safeT shapeT
      apply budgetMono ac prog t _ _ child
      have weight := wordCodeWeight_lookup s.code loc arity prog found
      have powLe : (wordCodeWeight s.code+1)^(t.clock+1) ≤ power :=
        Nat.pow_le_pow_right (by omega) (by omega)
      simpa [callTableBudget,codeEq,bodyCost] using Nat.mul_le_mul weight powLe
    apply budgetMono ac _ s (bodyCost+contCost) _
      (budgetReturningNone ac values names body l1 l2 dest args s bodyCost contCost retSim codeSim)
    have wpos := wordControlWeight_pos body
    have baseLe : wordCodeWeight s.code + wordControlWeight body ≤
        (1 + wordControlWeight body) * (wordCodeWeight s.code + 1) := by nlinarith
    have bound := Nat.mul_le_mul_right power baseLe
    simp only [callTableBudget,wordControlWeight,Nat.add_zero,Nat.pow_succ]
    change wordCodeWeight s.code * power + wordControlWeight body * power ≤
      (1 + wordControlWeight body) * (power * (wordCodeWeight s.code + 1))
    calc
      _ = (wordCodeWeight s.code + wordControlWeight body) * power := by rw [Nat.add_mul]
      _ ≤ ((1 + wordControlWeight body) * (wordCodeWeight s.code + 1)) * power := bound
      _ = _ := by ac_rfl
  | @handler values names l1 l2 dest args hvar h1 h2 body catchCode hb hc =>
    simp only [noMtSubprogsHOL,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] at noMt noInstall
    let power := (wordCodeWeight s.code + 1) ^ s.clock
    let bodyCost := wordCodeWeight s.code * power
    let contCost := max (wordControlWeight body) (wordControlWeight catchCode) * power
    have retSim : ∀ t : WordSemStateFiniteExact width (Nat × C) F,
        t.clock < s.clock → (safeWordCode s → safeWordCode t ∧ t.code = s.code) →
        BudgetSimulation ac body t contCost := by
      intro t smaller transfer
      obtain ⟨safeT,codeEq⟩ := transfer safe
      have shapeT : ∀ loc arity prog, sptLookup loc t.code = some (arity,prog) → CallBudgetBlock prog := by rw [codeEq]; exact table
      have child := callBudgetBlock_simulation ac body t hb noMt.1.2 noInstall.1.2 safeT shapeT
      apply budgetMono ac body t _ _ child
      have powLe : (wordCodeWeight s.code+1)^(t.clock+1) ≤ power :=
        Nat.pow_le_pow_right (by omega) (by omega)
      simpa [callTableBudget,codeEq,contCost] using Nat.mul_le_mul (Nat.le_max_left (wordControlWeight body) (wordControlWeight catchCode)) powLe
    have handlerSim : ∀ t : WordSemStateFiniteExact width (Nat × C) F,
        t.clock < s.clock → (safeWordCode s → safeWordCode t ∧ t.code = s.code) →
        BudgetSimulation ac catchCode t contCost := by
      intro t smaller transfer
      obtain ⟨safeT,codeEq⟩ := transfer safe
      have shapeT : ∀ loc arity prog, sptLookup loc t.code = some (arity,prog) → CallBudgetBlock prog := by rw [codeEq]; exact table
      have child := callBudgetBlock_simulation ac catchCode t hc noMt.2.2 noInstall.2.2 safeT shapeT
      apply budgetMono ac catchCode t _ _ child
      have powLe : (wordCodeWeight s.code+1)^(t.clock+1) ≤ power :=
        Nat.pow_le_pow_right (by omega) (by omega)
      simpa [callTableBudget,codeEq,contCost] using Nat.mul_le_mul (Nat.le_max_right (wordControlWeight body) (wordControlWeight catchCode)) powLe
    have codeSim : ∀ loc arity prog, sptLookup loc s.code = some (arity,prog) →
        ∀ t : WordSemStateFiniteExact width (Nat × C) F,
          t.clock < s.clock → (safeWordCode s → safeWordCode t ∧ t.code = s.code) →
          BudgetSimulation ac prog t bodyCost := by
      intro loc arity prog found t smaller transfer
      obtain ⟨safeT,codeEq⟩ := transfer safe
      have shapeT : ∀ loc arity prog, sptLookup loc t.code = some (arity,prog) → CallBudgetBlock prog := by rw [codeEq]; exact table
      have child := callBudgetBlock_simulation ac prog t (table loc arity prog found) (safe.1 loc arity prog found)
        (safe.2 loc arity prog found) safeT shapeT
      apply budgetMono ac prog t _ _ child
      have weight := wordCodeWeight_lookup s.code loc arity prog found
      have powLe : (wordCodeWeight s.code+1)^(t.clock+1) ≤ power :=
        Nat.pow_le_pow_right (by omega) (by omega)
      simpa [callTableBudget,codeEq,bodyCost] using Nat.mul_le_mul weight powLe
    apply budgetMono ac _ s (bodyCost+contCost) _
      (budgetReturningHandlerCase ac values names body l1 l2 dest args hvar h1 h2 catchCode s bodyCost contCost retSim handlerSim codeSim)
    have wpos := wordControlWeight_pos body
    have maxLe : max (wordControlWeight body) (wordControlWeight catchCode) ≤
        wordControlWeight body + wordControlWeight catchCode := max_le (by omega) (by omega)
    have baseLe : wordCodeWeight s.code + max (wordControlWeight body) (wordControlWeight catchCode) ≤
        (1 + wordControlWeight body + wordControlWeight catchCode) * (wordCodeWeight s.code + 1) := by nlinarith
    have bound := Nat.mul_le_mul_right power baseLe
    simp only [callTableBudget,wordControlWeight,Nat.pow_succ]
    change wordCodeWeight s.code * power + max (wordControlWeight body) (wordControlWeight catchCode) * power ≤
      (1 + wordControlWeight body + wordControlWeight catchCode) * (power * (wordCodeWeight s.code + 1))
    calc
      _ = (wordCodeWeight s.code + max (wordControlWeight body) (wordControlWeight catchCode)) * power := by rw [Nat.add_mul]
      _ ≤ ((1 + wordControlWeight body + wordControlWeight catchCode) * (wordCodeWeight s.code + 1)) * power := bound
      _ = _ := by ac_rfl
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals try subst p
  all_goals simp_wf
  all_goals simp_all only [WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.decClock]
  all_goals omega

/-- The concrete compiled Stack run has an explicit table-derived visit bound. -/
theorem callBudgetBlock_stackVisits {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (p : WordLangProgHOL (BitVec width))
    (source post : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (k f frame : Nat) (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (shape : CallBudgetBlock p) (noMt : noMtSubprogsHOL p = true)
    (noInstall : noInstallSubprogsHOL p = true) (safe : safeWordCode source)
    (table : ∀ loc arity prog, sptLookup loc source.code = some (arity,prog) → CallBudgetBlock prog)
    (empty : StackSteps.emptyCodeOracle target)
    (premises : WordSemStateFiniteExact.evaluate p source = (result, post) ∧
      result ≠ some .error ∧ result ≠ some .timeOut ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k p = true ∧ flatExpConventions p = true ∧
      compNative ac false p (bs, n) (k,f,frame) = (compiled,(bsPost,nPost)) ∧
      (appListAppend bs).length ≤ n ∧ n-(appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n-(appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL p < 2*frame+2*k) :
    let allowance := callTableBudget p source
    ∃ targetPost targetResult,
      StackSemEvaluate.evaluate (compiled,{target with clock := target.clock + allowance}) =
        (targetResult,targetPost) ∧
      compCorrectResult ac k f frame source post {targetPost with clock := post.clock} result targetResult lens ∧
      StackSteps.steps (compiled,{target with clock := target.clock + allowance}) ≤
        StackSteps.stackControlWeight compiled +
          max (StackSteps.stackControlWeight compiled) (StackSteps.stackCodeWeight target.code) *
            (target.clock + allowance) := by
  dsimp only
  obtain ⟨targetPost,out,run,_,_,related⟩ :=
    callBudgetBlock_simulation ac p source shape noMt noInstall safe table
      k f frame post target result bs bsPost n nPost compiled lens premises 0
  refine ⟨targetPost,out,by simpa using run,related,?_⟩
  have bound := StackSteps.stackTable_clock_bound compiled
    {target with clock := target.clock + callTableBudget p source} empty
  exact bound

end SteppedFlapjack.WordToStackSteps
