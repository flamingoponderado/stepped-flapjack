import SteppedFlapjack.WordToStackSteps.BudgetHandler
import SteppedFlapjack.WordToStackSteps.BudgetTailCall
import SteppedFlapjack.WordToStackSteps.BudgetIf
import SteppedFlapjack.WordToStackSteps.BudgetLoop
import SteppedFlapjack.WordToStackSteps.BudgetSharedMemory
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
  | shareInst (op v exp) : CallBudgetBlock (.shareInst op v exp)
  | seq {a b} : CallBudgetBlock a → CallBudgetBlock b → CallBudgetBlock (.seq a b)
  | ite (cmp r ri) {a b} : CallBudgetBlock a → CallBudgetBlock b → CallBudgetBlock (.ite cmp r ri a b)
  | loop (names exitNames) {body} : CallBudgetBlock body → CallBudgetBlock (.loop names body exitNames)
  | tail (dest args) : CallBudgetBlock (.call none dest args none)
  | call (values names l1 l2 dest args) {body} : CallBudgetBlock body →
      CallBudgetBlock (.call (some (values,names,body,l1,l2)) dest args none)
  | handler (values names l1 l2 dest args hvar h1 h2) {body catchCode} :
      CallBudgetBlock body → CallBudgetBlock catchCode →
      CallBudgetBlock (.call (some (values,names,body,l1,l2)) dest args (some (hvar,catchCode,h1,h2)))

/-- The cost of a program at a fixed code-and-program control weight. -/
def fixedTableBudget {width : Nat} [NeZero width] {C F : Type} (K : Nat)
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) : Nat :=
  wordControlWeight p * (K + 1) ^ (s.clock + 1)

/-- The allowance computed from a concrete program, code table, and clock. -/
def callTableBudget {width : Nat} [NeZero width] {C F : Type}
    (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) : Nat :=
  fixedTableBudget (max (wordControlWeight p) (wordCodeWeight s.code)) p s

private theorem wordControlWeight_pos {width : Nat} [NeZero width] (p : WordLangProgHOL (BitVec width)) :
    1 ≤ wordControlWeight p := by
  cases p <;> (try simp only [wordControlWeight]) <;> (try omega)
  case call ret dest args handler =>
    cases ret <;> cases handler <;> simp [wordControlWeight]
    all_goals omega

/-- Whole-table compiler simulation for nested calls and continuations, with
an explicit budget computed from the function table and source clock. -/
private theorem callBudgetBlock_simulation_core {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (K : Nat) (p : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width (Nat × C) F)
    (shape : CallBudgetBlock p) (noMt : noMtSubprogsHOL p = true)
    (noInstall : noInstallSubprogsHOL p = true) (safe : safeWordCode s)
    (table : ∀ loc arity body, sptLookup loc s.code = some (arity,body) → CallBudgetBlock body)
    (codeBound : wordCodeWeight s.code ≤ K) (progBound : wordControlWeight p ≤ K) :
    BudgetSimulation ac p s (fixedTableBudget K p s) := by
  cases shape with
  | base block =>
    exact budgetMono ac p s 0 _ (zeroBudget ac p s (loopBlock_zero ac p s block)) (by omega)
  | raise name =>
    apply budgetMono ac _ s 1 _ (raiseBudget ac name s)
    have hp : 0 < (K + 1) ^ (s.clock + 1) := Nat.pow_pos (by omega)
    simp only [fixedTableBudget,wordControlWeight,Nat.one_mul]
    omega
  | shareInst op v exp =>
    apply budgetMono ac _ s 1 _ (shareInst_budget ac op v exp s)
    have hp : 0 < (K + 1) ^ (s.clock + 1) := Nat.pow_pos (by omega)
    simp only [fixedTableBudget,wordControlWeight,Nat.one_mul]
    omega
  | @seq a b ha hb =>
    simp only [noMtSubprogsHOL, noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] at noMt noInstall
    have first := callBudgetBlock_simulation_core ac K a s ha noMt.1 noInstall.1 safe table codeBound (by simp [wordControlWeight] at progBound; omega)
    rcases run : evaluate a s with ⟨res,middle⟩
    cases res with
    | none =>
      have code := code_evaluate a s noInstall.1 safe.2
      rw [run] at code
      have codeEq : middle.code = s.code := code
      have middleSafe : safeWordCode middle := by simpa [safeWordCode,codeEq] using safe
      have middleTable : ∀ loc arity body, sptLookup loc middle.code = some (arity,body) → CallBudgetBlock body := by rw [codeEq]; exact table
      have clk := (evaluate_clock a s none middle run).1
      have second := callBudgetBlock_simulation_core ac K b middle hb noMt.2 noInstall.2 middleSafe middleTable (by simpa [codeEq] using codeBound) (by simp [wordControlWeight] at progBound; omega)
      have powLe : (K + 1) ^ (middle.clock + 1) ≤
          (K + 1) ^ (s.clock + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      apply budgetMono ac _ s (fixedTableBudget K a s + fixedTableBudget K b middle) _
        (budgetSeq ac a b s _ _ first ?_) ?_
      · intro result middle' guard
        rw [run] at guard
        cases guard.1
        exact second
      · simp only [fixedTableBudget,wordControlWeight]
        have bb := Nat.mul_le_mul_left (wordControlWeight b) powLe
        simp only [Nat.add_mul,Nat.one_mul]
        omega
    | some v =>
      apply budgetMono ac _ s (fixedTableBudget K a s + 0) _
        (budgetSeq ac a b s _ _ first ?_) ?_
      · intro result middle' guard
        rw [run] at guard
        have impossible := congrArg Prod.fst guard.1
        rw [guard.2] at impossible
        cases impossible
      · simp only [fixedTableBudget,wordControlWeight]
        have hp : 0 < (K + 1) ^ (s.clock + 1) := Nat.pow_pos (by omega)
        nlinarith
  | @ite cmp r ri a b ha hb =>
    simp only [noMtSubprogsHOL,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] at noMt noInstall
    apply budgetIf ac cmp r ri a b s (fixedTableBudget K (.ite cmp r ri a b) s)
    constructor
    · intro v3 v4 x y value guard
      have child := callBudgetBlock_simulation_core ac K a s ha noMt.1 noInstall.1 safe table codeBound (by simp [wordControlWeight] at progBound; omega)
      apply budgetMono ac a s _ _ child
      simp only [fixedTableBudget,wordControlWeight]
      apply Nat.mul_le_mul_right
      omega
    · intro v3 v4 x y value guard
      have child := callBudgetBlock_simulation_core ac K b s hb noMt.2 noInstall.2 safe table codeBound (by simp [wordControlWeight] at progBound; omega)
      apply budgetMono ac b s _ _ child
      simp only [fixedTableBudget,wordControlWeight]
      apply Nat.mul_le_mul_right
      omega
  | @loop names exitNames body hb =>
    have loopMt := noMt
    have loopInstall := noInstall
    simp only [noMtSubprogsHOL,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp] at noMt noInstall
    have weightBody : wordControlWeight body ≤ K := by simp [wordControlWeight] at progBound; omega
    let power := (K+1)^s.clock
    let bodyCost := wordControlWeight body * (K+1)^(s.clock+1)
    let recCost := wordControlWeight (.loop names body exitNames : WordLangProgHOL (BitVec width)) * power
    have cutCode : ∀ cutSource, cutState (names,.ln) s = some cutSource → cutSource.code = s.code := by
      intro cutSource cut
      unfold cutState at cut
      cases env : wordSemCutEnv (names,.ln) s.locals <;> simp [env] at cut
      next locals => subst cutSource; rfl
    have bodySim : ∀ cutSource, cutState (names,.ln) s = some cutSource →
        BudgetSimulation ac body cutSource bodyCost := by
      intro cutSource cut
      have codeEq := cutCode cutSource cut
      have clocks := cutState_clock_termdep _ _ _ cut
      have safeCut : safeWordCode cutSource := by simpa [safeWordCode,codeEq] using safe
      have tableCut : ∀ loc arity prog, sptLookup loc cutSource.code = some (arity,prog) → CallBudgetBlock prog := by rw [codeEq]; exact table
      have child := callBudgetBlock_simulation_core ac K body cutSource hb noMt noInstall safeCut tableCut (by simpa [codeEq] using codeBound) weightBody
      simpa [fixedTableBudget,bodyCost,show cutSource.clock = s.clock by omega] using child
    have recSim : ∀ cutSource bodyResult bodyPost,
        cutState (names,.ln) s = some cutSource ∧
        (bodyResult,bodyPost) = evaluate body cutSource ∧
        wordSemContLoop bodyResult = true ∧ bodyPost.clock ≠ 0 →
        BudgetSimulation ac (wordSemSTOP (.loop names body exitNames)) (decClock bodyPost) recCost := by
      intro cutSource bodyResult bodyPost guard
      obtain ⟨cut,run,continues,nonzero⟩ := guard
      have codeEq := cutCode cutSource cut
      have clocks := cutState_clock_termdep _ _ _ cut
      have bodyClock := (evaluate_clock body cutSource bodyResult bodyPost run.symm).1
      have safeCut : safeWordCode cutSource := by simpa [safeWordCode,codeEq] using safe
      have postCode := code_evaluate body cutSource noInstall safeCut.2
      rw [←run] at postCode
      have childCode : (decClock bodyPost).code = s.code := by simpa [WordSemStateFiniteExact.decClock,codeEq] using postCode
      have childClock : (decClock bodyPost).clock < s.clock := by simp only [WordSemStateFiniteExact.decClock]; omega
      have safeChild : safeWordCode (decClock bodyPost) := by simpa [safeWordCode,childCode] using safe
      have tableChild : ∀ loc arity prog, sptLookup loc (decClock bodyPost).code = some (arity,prog) → CallBudgetBlock prog := by rw [childCode]; exact table
      have child := callBudgetBlock_simulation_core ac K (.loop names body exitNames) (decClock bodyPost)
        (.loop names exitNames hb) loopMt loopInstall safeChild tableChild (by simpa [childCode] using codeBound) progBound
      apply budgetMono ac _ _ _ recCost
      · simpa [wordSemSTOP] using child
      · have powLe : (K+1)^((decClock bodyPost).clock+1) ≤ power :=
          Nat.pow_le_pow_right (by omega) (by omega)
        simpa [fixedTableBudget,wordSemSTOP,recCost] using Nat.mul_le_mul_left
          (wordControlWeight (.loop names body exitNames : WordLangProgHOL (BitVec width))) powLe
    apply budgetMono ac _ s (bodyCost+recCost) _
      (budgetLoop ac names exitNames body s bodyCost recCost ⟨recSim,bodySim⟩)
    have factorLe : 1 + wordControlWeight body ≤ K + 1 := by simp [wordControlWeight] at progBound; omega
    have recBound := Nat.mul_le_mul_right power factorLe
    simp only [fixedTableBudget,wordControlWeight,Nat.pow_succ]
    change wordControlWeight body * ((K+1)^(s.clock+1)) + (1+wordControlWeight body)*power ≤
      (1+wordControlWeight body) * (power * (K+1))
    rw [Nat.pow_succ (K+1) s.clock]
    calc
      _ ≤ wordControlWeight body * (power * (K+1)) + (K+1)*power := Nat.add_le_add_left recBound _
      _ = _ := by ring
  | tail dest args =>
    apply budgetCallTail ac dest args none s (fixedTableBudget K (.call none dest args none) s)
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
    have sim := callBudgetBlock_simulation_core ac K prog child childShape childNoMt childNoInstall childSafe childTable (by simpa [childCode] using codeBound) ((wordCodeWeight_lookup s.code loc args1.length prog found).trans codeBound)
    apply budgetMono ac prog child _ _ sim
    have weight := (wordCodeWeight_lookup s.code loc args1.length prog found).trans codeBound
    have powLe : (K+1)^(child.clock+1) ≤ (K+1)^s.clock :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have bound := Nat.mul_le_mul weight powLe
    simp only [fixedTableBudget,wordControlWeight,Nat.add_zero,Nat.one_mul]
    rw [Nat.pow_succ (K+1) s.clock]
    apply bound.trans
    rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm ((K+1)^s.clock) (K)]
    omega
  | @call values names l1 l2 dest args body hb =>
    simp only [noMtSubprogsHOL,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] at noMt noInstall
    let power := (K + 1) ^ s.clock
    let bodyCost := K * power
    let contCost := wordControlWeight body * power
    have retSim : ∀ t : WordSemStateFiniteExact width (Nat × C) F,
        t.clock < s.clock → (safeWordCode s → safeWordCode t ∧ t.code = s.code) →
        BudgetSimulation ac body t contCost := by
      intro t smaller transfer
      obtain ⟨safeT,codeEq⟩ := transfer safe
      have shapeT : ∀ loc arity prog, sptLookup loc t.code = some (arity,prog) → CallBudgetBlock prog := by rw [codeEq]; exact table
      have child := callBudgetBlock_simulation_core ac K body t hb noMt.1.2 noInstall.1.2 safeT shapeT (by simpa [codeEq] using codeBound) (by simp [wordControlWeight] at progBound; omega)
      apply budgetMono ac body t _ _ child
      have powLe : (K+1)^(t.clock+1) ≤ power :=
        Nat.pow_le_pow_right (by omega) (by omega)
      simpa [fixedTableBudget,codeEq,contCost] using Nat.mul_le_mul_left (wordControlWeight body) powLe
    have codeSim : ∀ loc arity prog, sptLookup loc s.code = some (arity,prog) →
        ∀ t : WordSemStateFiniteExact width (Nat × C) F,
          t.clock < s.clock → (safeWordCode s → safeWordCode t ∧ t.code = s.code) →
          BudgetSimulation ac prog t bodyCost := by
      intro loc arity prog found t smaller transfer
      obtain ⟨safeT,codeEq⟩ := transfer safe
      have shapeT : ∀ loc arity prog, sptLookup loc t.code = some (arity,prog) → CallBudgetBlock prog := by rw [codeEq]; exact table
      have child := callBudgetBlock_simulation_core ac K prog t (table loc arity prog found) (safe.1 loc arity prog found)
        (safe.2 loc arity prog found) safeT shapeT (by simpa [codeEq] using codeBound)
        ((wordCodeWeight_lookup s.code loc arity prog found).trans codeBound)
      apply budgetMono ac prog t _ _ child
      have weight := (wordCodeWeight_lookup s.code loc arity prog found).trans codeBound
      have powLe : (K+1)^(t.clock+1) ≤ power :=
        Nat.pow_le_pow_right (by omega) (by omega)
      simpa [fixedTableBudget,codeEq,bodyCost] using Nat.mul_le_mul weight powLe
    apply budgetMono ac _ s (bodyCost+contCost) _
      (budgetReturningNone ac values names body l1 l2 dest args s bodyCost contCost retSim codeSim)
    have wpos := wordControlWeight_pos body
    have baseLe : K + wordControlWeight body ≤
        (1 + wordControlWeight body) * (K + 1) := by nlinarith
    have bound := Nat.mul_le_mul_right power baseLe
    simp only [fixedTableBudget,wordControlWeight,Nat.add_zero,Nat.pow_succ]
    change K * power + wordControlWeight body * power ≤
      (1 + wordControlWeight body) * (power * (K + 1))
    calc
      _ = (K + wordControlWeight body) * power := by rw [Nat.add_mul]
      _ ≤ ((1 + wordControlWeight body) * (K + 1)) * power := bound
      _ = _ := by ac_rfl
  | @handler values names l1 l2 dest args hvar h1 h2 body catchCode hb hc =>
    simp only [noMtSubprogsHOL,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] at noMt noInstall
    let power := (K + 1) ^ s.clock
    let bodyCost := K * power
    let contCost := max (wordControlWeight body) (wordControlWeight catchCode) * power
    have retSim : ∀ t : WordSemStateFiniteExact width (Nat × C) F,
        t.clock < s.clock → (safeWordCode s → safeWordCode t ∧ t.code = s.code) →
        BudgetSimulation ac body t contCost := by
      intro t smaller transfer
      obtain ⟨safeT,codeEq⟩ := transfer safe
      have shapeT : ∀ loc arity prog, sptLookup loc t.code = some (arity,prog) → CallBudgetBlock prog := by rw [codeEq]; exact table
      have child := callBudgetBlock_simulation_core ac K body t hb noMt.1.2 noInstall.1.2 safeT shapeT (by simpa [codeEq] using codeBound) (by simp [wordControlWeight] at progBound; omega)
      apply budgetMono ac body t _ _ child
      have powLe : (K+1)^(t.clock+1) ≤ power :=
        Nat.pow_le_pow_right (by omega) (by omega)
      simpa [fixedTableBudget,codeEq,contCost] using Nat.mul_le_mul (Nat.le_max_left (wordControlWeight body) (wordControlWeight catchCode)) powLe
    have handlerSim : ∀ t : WordSemStateFiniteExact width (Nat × C) F,
        t.clock < s.clock → (safeWordCode s → safeWordCode t ∧ t.code = s.code) →
        BudgetSimulation ac catchCode t contCost := by
      intro t smaller transfer
      obtain ⟨safeT,codeEq⟩ := transfer safe
      have shapeT : ∀ loc arity prog, sptLookup loc t.code = some (arity,prog) → CallBudgetBlock prog := by rw [codeEq]; exact table
      have child := callBudgetBlock_simulation_core ac K catchCode t hc noMt.2.2 noInstall.2.2 safeT shapeT (by simpa [codeEq] using codeBound) (by simp [wordControlWeight] at progBound; omega)
      apply budgetMono ac catchCode t _ _ child
      have powLe : (K+1)^(t.clock+1) ≤ power :=
        Nat.pow_le_pow_right (by omega) (by omega)
      simpa [fixedTableBudget,codeEq,contCost] using Nat.mul_le_mul (Nat.le_max_right (wordControlWeight body) (wordControlWeight catchCode)) powLe
    have codeSim : ∀ loc arity prog, sptLookup loc s.code = some (arity,prog) →
        ∀ t : WordSemStateFiniteExact width (Nat × C) F,
          t.clock < s.clock → (safeWordCode s → safeWordCode t ∧ t.code = s.code) →
          BudgetSimulation ac prog t bodyCost := by
      intro loc arity prog found t smaller transfer
      obtain ⟨safeT,codeEq⟩ := transfer safe
      have shapeT : ∀ loc arity prog, sptLookup loc t.code = some (arity,prog) → CallBudgetBlock prog := by rw [codeEq]; exact table
      have child := callBudgetBlock_simulation_core ac K prog t (table loc arity prog found) (safe.1 loc arity prog found)
        (safe.2 loc arity prog found) safeT shapeT (by simpa [codeEq] using codeBound)
        ((wordCodeWeight_lookup s.code loc arity prog found).trans codeBound)
      apply budgetMono ac prog t _ _ child
      have weight := (wordCodeWeight_lookup s.code loc arity prog found).trans codeBound
      have powLe : (K+1)^(t.clock+1) ≤ power :=
        Nat.pow_le_pow_right (by omega) (by omega)
      simpa [fixedTableBudget,codeEq,bodyCost] using Nat.mul_le_mul weight powLe
    apply budgetMono ac _ s (bodyCost+contCost) _
      (budgetReturningHandlerCase ac values names body l1 l2 dest args hvar h1 h2 catchCode s bodyCost contCost retSim handlerSim codeSim)
    have wpos := wordControlWeight_pos body
    have maxLe : max (wordControlWeight body) (wordControlWeight catchCode) ≤
        wordControlWeight body + wordControlWeight catchCode := max_le (by omega) (by omega)
    have baseLe : K + max (wordControlWeight body) (wordControlWeight catchCode) ≤
        (1 + wordControlWeight body + wordControlWeight catchCode) * (K + 1) := by nlinarith
    have bound := Nat.mul_le_mul_right power baseLe
    simp only [fixedTableBudget,wordControlWeight,Nat.pow_succ]
    change K * power + max (wordControlWeight body) (wordControlWeight catchCode) * power ≤
      (1 + wordControlWeight body + wordControlWeight catchCode) * (power * (K + 1))
    calc
      _ = (K + max (wordControlWeight body) (wordControlWeight catchCode)) * power := by rw [Nat.add_mul]
      _ ≤ ((1 + wordControlWeight body + wordControlWeight catchCode) * (K + 1)) * power := bound
      _ = _ := by ac_rfl
termination_by (s.clock, sizeOf p)
decreasing_by
  all_goals try subst p
  all_goals simp_wf
  all_goals simp_all only [WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.decClock]
  all_goals omega


/-- Whole-table simulation for nested calls and loops with a concrete budget. -/
theorem callBudgetBlock_simulation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (p : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width (Nat × C) F)
    (shape : CallBudgetBlock p) (noMt : noMtSubprogsHOL p = true)
    (noInstall : noInstallSubprogsHOL p = true) (safe : safeWordCode s)
    (table : ∀ loc arity body, sptLookup loc s.code = some (arity,body) → CallBudgetBlock body) :
    BudgetSimulation ac p s (callTableBudget p s) := by
  exact callBudgetBlock_simulation_core ac _ p s shape noMt noInstall safe table
    (Nat.le_max_right _ _) (Nat.le_max_left _ _)

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
