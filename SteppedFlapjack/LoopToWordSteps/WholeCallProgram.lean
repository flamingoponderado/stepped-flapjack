import SteppedFlapjack.LoopToWordSteps.TailCall
import SteppedFlapjack.LoopLiveSteps.TailEntryGlobalBound
import SteppedFlapjack.CrepToLoopSteps.CallFrontendShape
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.LoopToWord
open Flapjack.LoopToWord.CompileCorrect Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.LoopLiveSteps SteppedFlapjack.LoopSteps

private theorem tail_dispatch {width : Nat} [NeZero width] {C F : Type}
    (loc : Nat) (args : List Nat) (s : LoopSemStateFiniteExact width F)
    (bodyProp : ∀ vals env body, getVars args s = some vals →
      findCode (some loc) vals s.code = some (env,body) → s.clock ≠ 0 →
      SixBoundPropertyAt C body {decClock s with locals := env}) :
    SixBoundPropertyAt C (.call none (some loc) args none) s := by
  cases get : getVars args s with
  | none =>
    intro res final target ctxt retv labels premises
    have run := premises.1
    rw [evaluate] at run
    simp only [get,Prod.mk.injEq] at run
    exact False.elim (premises.2.1 run.1.symm)
  | some vals =>
    cases found : findCode (some loc) vals s.code with
    | none =>
      intro res final target ctxt retv labels premises
      have run := premises.1
      rw [evaluate] at run
      simp only [get,found,Prod.mk.injEq] at run
      exact False.elim (premises.2.1 run.1.symm)
    | some pair =>
      obtain ⟨env,body⟩ := pair
      exact sixBoundedDirectTail loc args vals env body s (bodyProp vals env body get found) get found

private theorem returning_dispatch {width : Nat} [NeZero width] {C F : Type}
    (loc : Nat) (args names : List Nat) (live liveOut : NumSet) (exc : Nat)
    (markHandler markNormal : Bool) (s : LoopSemStateFiniteExact width F)
    (bodyProp : ∀ vals env body cut, getVars args s = some vals →
      findCode (some loc) vals s.code = some (env,body) →
      cutRes live (none,s) = (none,cut) → SixBoundPropertyAt C body {cut with locals := env}) :
    SixBoundPropertyAt C (.call (some (names,live)) (some loc) args
      (some (exc,if markHandler then .mark (.raise exc) else .raise exc,
        if markNormal then .mark .skip else .skip,liveOut))) s := by
  cases get : getVars args s with
  | none =>
    intro res final target ctxt retv labels premises
    have run := premises.1
    rw [evaluate] at run
    simp only [get,Prod.mk.injEq] at run
    exact False.elim (premises.2.1 run.1.symm)
  | some vals =>
    cases found : findCode (some loc) vals s.code with
    | none =>
      intro res final target ctxt retv labels premises
      have run := premises.1
      rw [evaluate] at run
      simp only [get,found,Prod.mk.injEq] at run
      exact False.elim (premises.2.1 run.1.symm)
    | some pair =>
      obtain ⟨env,body⟩ := pair
      by_cases distinct : names.Nodup
      · exact sixBoundedDirectReturning loc args names live liveOut exc markHandler markNormal s vals env body
          get found distinct (fun cut h => bodyProp vals env body cut get found h)
      · intro res final target ctxt retv labels premises
        have run := premises.1
        rw [evaluate] at run
        simp only [get,found,distinct,not_false_eq_true,if_true,Prod.mk.injEq] at run
        exact False.elim (premises.2.1 run.1.symm)
set_option maxHeartbeats 5000000 in
/-- Every supported Loop program has the sixfold Loop-to-Word simulation when
all bodies in its actual code table have the same recursive call-aware shape. -/
theorem loopTable_correct_with_steps {width : Nat} [NeZero width] {C F : Type}
    (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F)
    (shape : SimpleLoopSequenceSource p) (table : LoopTableSupported s.code) :
    SixBoundPropertyAt C p s := by
  have key : ∀ (x : Nat × Nat) (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F),
      (s.clock,sizeOf p) = x → SimpleLoopSequenceSource p → LoopTableSupported s.code →
      SixBoundPropertyAt C p s := by
    intro x
    induction x using (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.induction with
    | h x ih0 =>
      intro p s hx shape table
      have ih : ∀ (q : HolLoopProg width) (t : LoopSemStateFiniteExact width F),
          Prod.Lex (· < ·) (· < ·) (t.clock,sizeOf q) (s.clock,sizeOf p) →
          SimpleLoopSequenceSource q → t.code = s.code → SixBoundPropertyAt C q t := by
        intro q t smaller qshape same
        have table' : LoopTableSupported t.code := by rw [same]; exact table
        exact ih0 _ (hx ▸ smaller) q t rfl qshape table'
      clear ih0 hx
      cases shape with
      | branch h => exact loopProgram_correct_with_steps (loopBranch_program h) s
      | @loop live exits body h =>
        apply sixBoundedLoopAt live exits body s
        intro t same smaller
        exact ih body t (Prod.Lex.left _ _ smaller) h same
      | @seq a b ha hb =>
        apply sixBoundedSeq a b s
        refine ⟨?_,ih a s (lexLt (Nat.le_refl _) (by simp_wf; omega)) ha rfl⟩
        intro res middle h
        obtain ⟨run,rfl⟩ := h
        have clock := evaluate_clock a s none middle run.symm
        have same := SteppedFlapjack.LoopLiveSteps.evaluate_code a s middle none run.symm
        exact ih b middle (lexLt clock (by simp_wf)) hb same
      | @conditional cmp r ri live a b ha hb =>
        apply sixBoundedIf cmp r ri a b live s
        intro v2 v3 v5 x v13 y branch h1 h2 h3 h4 h5 h6
        cases branch <;> simp only [Bool.false_eq_true,↓reduceIte]
        · exact ih b s (lexLt (Nat.le_refl _) (by simp_wf; omega)) hb rfl
        · exact ih a s (lexLt (Nat.le_refl _) (by simp_wf; omega)) ha rfl
      | @mark q h => exact sixBoundedMark q s (ih q s (lexLt (Nat.le_refl _) (by simp_wf)) h rfl)
      | tail loc args =>
        apply tail_dispatch loc args s
        intro vals env body get found nonzero
        obtain ⟨params,lookup⟩ := findCode_direct_body s.code loc vals env body found
        have small : (decClock s).clock < s.clock := by simp [decClock]; omega
        exact ih body {decClock s with locals := env} (Prod.Lex.left _ _ small) (table loc params body lookup) rfl
      | returning names live loc exc args liveOut =>
        apply returning_dispatch loc args names live liveOut exc false false s
        intro vals env body cut get found cutRun
        obtain ⟨params,lookup⟩ := findCode_direct_body s.code loc vals env body found
        have small := cutRes_none_clock cutRun
        have same : cut.code = s.code := by have h := cutRes_code live none s; rw [cutRun] at h; exact h
        exact ih body {cut with locals := env} (Prod.Lex.left _ _ small) (table loc params body lookup) same
      | returningMarked names live loc exc args liveOut =>
        apply returning_dispatch loc args names live liveOut exc true true s
        intro vals env body cut get found cutRun
        obtain ⟨params,lookup⟩ := findCode_direct_body s.code loc vals env body found
        have small := cutRes_none_clock cutRun
        have same : cut.code = s.code := by have h := cutRes_code live none s; rw [cutRun] at h; exact h
        exact ih body {cut with locals := env} (Prod.Lex.left _ _ small) (table loc params body lookup) same
  exact key _ p s rfl shape table

/-- A reached entry in a supported table has the complete sixfold compiler
simulation, including calls to other entries. -/
theorem loopTable_entry_correct_with_steps {width : Nat} [NeZero width] {C F : Type}
    (code : Spt (List Nat × HolLoopProg width)) (loc : Nat) (params : List Nat) (body : HolLoopProg width)
    (s : LoopSemStateFiniteExact width F) (codeEq : s.code = code)
    (supported : LoopTableSupported code) (found : sptLookup loc code = some (params,body)) :
    SixBoundPropertyAt C body s := by
  apply loopTable_correct_with_steps body s (supported loc params body found)
  simpa only [codeEq] using supported

/-- The actual compiler table built from call-aware declarations discharges the
Loop-to-Word table premise when the declarations select no inlining. -/
theorem declaration_loopTable_entry_correct_with_steps {width : Nat} [NeZero width] {C F : Type}
    (arch : AsmArchitecture) (declarations : List (Pancake.PanLang.DeclHOL width))
    (noInline : (Pancake.PanLang.functionsHOL (declarations.filter Pancake.PanLang.inlinableHOL)).map Prod.fst = [])
    (shapes : ∀ entry ∈ Pancake.PanLang.functionsHOL declarations,
      PanToCrepSteps.CallFrontend (mkCtxtExactHOL (panToCrepMakeVmapHOLExact entry.2.1)
        (makeFuncsExactHOL (Pancake.PanLang.functionsHOL declarations))
        (Pancake.PanLang.sizeOfShapeHOL (.comb (entry.2.1.map Prod.snd)) - 1)
        (getEidsFromDeclsHOL declarations)) entry.2.2.1)
    (loc : Nat) (params : List Nat) (body : HolLoopProg width) (s : LoopSemStateFiniteExact width F)
    (codeEq : s.code = sptFromAList (compileProgHOLExact arch (compileProgDeclsHOLW declarations)))
    (found : sptLookup loc s.code = some (params,body)) : SixBoundPropertyAt C body s := by
  have table : LoopTableSupported s.code := by
    rw [codeEq]
    exact CrepToLoopSteps.callFrontend_declaration_loopTableSupported arch declarations noInline shapes
  exact loopTable_correct_with_steps body s (table loc params body found) table

end SteppedFlapjack.LoopToWordSteps
