import SteppedFlapjack.WordToStackSteps.BudgetTailCall
import SteppedFlapjack.WordToStackSteps.BudgetIf
import SteppedFlapjack.WordSteps.ClockConsumption
import SteppedFlapjack.WordSimpSteps.LoopSequenceClock
import SteppedFlapjack.StackSteps.TableBound
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
open Flapjack.WordToStackProofs.CompCorrect.CallTail
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-- Word programs with loop blocks, raises, sequencing, conditionals, and tail calls. -/
inductive RaiseTail {width : Nat} [NeZero width] : WordLangProgHOL (BitVec width) → Prop
  | loopBlock {p} : LoopBlock p → RaiseTail p
  | raise (name) : RaiseTail (.raise name)
  | seq {a b} : RaiseTail a → RaiseTail b → RaiseTail (.seq a b)
  | tail (dest args) : RaiseTail (.call none dest args none)
  | ite (cmp r ri) {a b} : RaiseTail a → RaiseTail b → RaiseTail (.ite cmp r ri a b)

/-- Nested tail calls preserve the compiler relation with at most one extra
Stack clock per actual Word evaluator visit. -/
theorem raiseTail_visitBudget {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (p : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width (Nat × C) F) :
    RaiseTail p → noInstallSubprogsHOL p = true → WordProps.noInstallCode s.code →
    (∀ loc arity prog, sptLookup loc s.code = some (arity,prog) → RaiseTail prog) →
    BudgetSimulation ac p s (steps p s) := by
  generalize hh : steps p s = n
  induction n using Nat.strong_induction_on generalizing p s with
  | h n ih =>
    intro shape noInstall safe table
    cases shape with
    | loopBlock block =>
      exact budgetMono ac p s 0 _ (zeroBudget ac p s (loopBlock_zero ac p s block)) (by omega)
    | raise name =>
      exact budgetMono ac _ s 1 _ (raiseBudget ac name s) (by have := steps_pos (.raise name) s; omega)
    | @seq a b ha hb =>
      simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] at noInstall
      obtain ⟨na,nb⟩ := noInstall
      rcases run : evaluate a s with ⟨res,middle⟩
      have count := steps_seq a b s
      rw [run] at count
      cases res with
      | none =>
        simp only at count
        have ca : steps a s < n := by omega
        have cb : steps b middle < n := by omega
        have codeEq := code_evaluate a s na safe
        rw [run] at codeEq
        simp only at codeEq
        have safeMiddle : WordProps.noInstallCode middle.code := by rw [codeEq]; exact safe
        have tableMiddle : ∀ loc arity prog, sptLookup loc middle.code = some (arity,prog) → RaiseTail prog := by
          rw [codeEq]; exact table
        have first := ih (steps a s) ca a s rfl ha na safe table
        have second := ih (steps b middle) cb b middle rfl hb nb safeMiddle tableMiddle
        apply budgetMono ac _ s (steps a s + steps b middle) _
          (budgetSeq ac a b s _ _ first ?_) (by omega)
        intro result middle' guard
        rw [run] at guard
        cases guard.1
        exact second
      | some v =>
        simp only at count
        have ca : steps a s < n := by omega
        have first := ih (steps a s) ca a s rfl ha na safe table
        apply budgetMono ac _ s (steps a s + 0) _
          (budgetSeq ac a b s _ _ first ?_) (by omega)
        intro result middle' guard
        rw [run] at guard
        have impossible := congrArg Prod.fst guard.1
        rw [guard.2] at impossible
        cases impossible
    | @ite cmp r ri a b ha hb =>
      simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] at noInstall
      obtain ⟨na,nb⟩ := noInstall
      apply budgetIf ac cmp r ri a b s n
      constructor
      · intro v3 v4 x y value guard
        obtain ⟨vars, v3eq, v4eq, compared, selected⟩ := guard
        rw [v3eq,v4eq] at vars
        have left := congrArg Prod.fst vars
        have right := congrArg Prod.snd vars
        have count := steps_ite cmp r ri a b s
        simp only at left right
        simp only [left,right] at count
        rw [compared] at count
        rw [selected] at count
        have smaller : steps a s < n := by simp only at count; omega
        have branch := ih _ smaller a s rfl ha na safe table
        exact budgetMono ac a s _ _ branch (by omega)
      · intro v3 v4 x y value guard
        obtain ⟨vars, v3eq, v4eq, compared, selected⟩ := guard
        rw [v3eq,v4eq] at vars
        have left := congrArg Prod.fst vars
        have right := congrArg Prod.snd vars
        have count := steps_ite cmp r ri a b s
        simp only at left right
        simp only [left,right] at count
        rw [compared] at count
        have vfalse : value = false := by cases value <;> simp_all
        rw [vfalse] at count
        have smaller : steps b s < n := by simp only at count; omega
        have branch := ih _ smaller b s rfl hb nb safe table
        exact budgetMono ac b s _ _ branch (by omega)
    | tail dest args =>
      rw [← hh]
      apply budgetCallTail ac dest args none s (steps (.call none dest args none) s)
      intro xs args1 prog ss guard
      obtain ⟨hargs,hbad,hfind,_,hclock⟩ := guard
      have find' : wordSemFindCode dest xs s.code s.stackSize = some (args1,prog,ss) := by simpa [wordSemAddRetLoc] using hfind
      obtain ⟨loc, found, _, _, _⟩ := findCode_facts dest xs s.code s.stackSize args1 prog ss find'
      have hbad' : wordSemBadDestArgs dest args = false := by cases h : wordSemBadDestArgs dest args <;> simp_all
      have count := steps_call_tail dest args s xs args1 ss prog hargs hbad' find' hclock
      have smaller : steps prog (callEnv args1 ss (decClock s)) < n := by omega
      have progNi := safe loc args1.length prog found
      have progShape := table loc args1.length prog found
      have child := ih _ smaller prog (callEnv args1 ss (decClock s)) rfl progShape progNi safe table
      exact budgetMono ac prog _ _ _ child (by omega)
/-- A concrete program, code table and initial clock give a closed target
clock allowance for arbitrarily nested calls in the tail fragment. -/
theorem raiseTail_staticBudget {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (p : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width (Nat × C) F)
    (shape : RaiseTail p) (noMt : noMtSubprogsHOL p = true)
    (noInstall : noInstallSubprogsHOL p = true) (tableNoMt : WordProps.noMtCode s.code)
    (tableNoInstall : WordProps.noInstallCode s.code)
    (table : ∀ loc arity prog, sptLookup loc s.code = some (arity,prog) → RaiseTail prog) :
    BudgetSimulation ac p s
      (WordSimpSteps.wordControlWeight p +
        max (WordSimpSteps.wordControlWeight p) (WordSimpSteps.wordCodeWeight s.code) * s.clock) := by
  exact budgetMono ac p s _ _ (raiseTail_visitBudget ac p s shape noInstall tableNoInstall table)
    (WordSimpSteps.wordTable_clock_bound p s noMt noInstall tableNoMt tableNoInstall)

/-- A concrete recursive-tail Word simulation and its actual Stack run have
an explicit visit bound computed from the two programs and code tables. -/
theorem raiseTail_stackVisitBudget {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (p : WordLangProgHOL (BitVec width))
    (source post : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
    (k f frame : Nat) (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (shape : RaiseTail p) (noMt : noMtSubprogsHOL p = true)
    (noInstall : noInstallSubprogsHOL p = true) (tableNoMt : WordProps.noMtCode source.code)
    (tableNoInstall : WordProps.noInstallCode source.code)
    (table : ∀ loc arity prog, sptLookup loc source.code = some (arity,prog) → RaiseTail prog)
    (empty : StackSteps.emptyCodeOracle target)
    (premises : WordSemStateFiniteExact.evaluate p source = (result, post) ∧
      result ≠ some .error ∧ result ≠ some .timeOut ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k p = true ∧ flatExpConventions p = true ∧
      compNative ac false p (bs, n) (k,f,frame) = (compiled,(bsPost,nPost)) ∧
      (appListAppend bs).length ≤ n ∧ n-(appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n-(appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL p < 2*frame+2*k) :
    let allowance := WordSimpSteps.wordControlWeight p +
      max (WordSimpSteps.wordControlWeight p) (WordSimpSteps.wordCodeWeight source.code) * source.clock
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
    raiseTail_staticBudget ac p source shape noMt noInstall tableNoMt tableNoInstall table
      k f frame post target result bs bsPost n nPost compiled lens premises 0
  refine ⟨targetPost,out,by simpa using run,related,?_⟩
  have bound := StackSteps.stackTable_clock_bound compiled
    {target with clock := target.clock + (WordSimpSteps.wordControlWeight p +
      max (WordSimpSteps.wordControlWeight p) (WordSimpSteps.wordCodeWeight source.code) * source.clock)} empty
  exact bound

end SteppedFlapjack.WordToStackSteps
