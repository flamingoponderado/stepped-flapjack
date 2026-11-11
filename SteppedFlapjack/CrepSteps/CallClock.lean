import SteppedFlapjack.CrepSteps.ScalarClock
import Flapjack.Pancake.Semantics.CrepProps
namespace SteppedFlapjack.CrepSteps
open Flapjack SteppedFlapjack.CrepToLoopSteps

/-- Recursive scalar programs with ordinary and tail calls. -/
inductive CallScalarProgram {width : Nat} [NeZero width] : CrepProgHOL width → Prop
  | base {p} : ScalarProgram p → CallScalarProgram p
  | dec (n) {e p} : CompiledScalar e → CallScalarProgram p → CallScalarProgram (.dec n e p)
  | seq {p q} : CallScalarProgram p → CallScalarProgram q → CallScalarProgram (.seq p q)
  | ite {e p q} : CompiledScalar e → CallScalarProgram p → CallScalarProgram q → CallScalarProgram (.ite e p q)
  | loop {e p} : CompiledScalar e → CallScalarProgram p → CallScalarProgram (.while e p)
  | call (ret : Option (List Nat)) (name : Basis.Pure.MlString.MlString) (args : List (CrepExpHOL width)) :
      CallScalarProgram (.call (ret.map (fun ns => (ns,none))) name args)

def CallScalarTable {width : Nat} [NeZero width]
    (code : HolFiniteMapExact Basis.Pure.MlString.MlString (List Nat × CrepProgHOL width)) : Prop :=
  ∀ name params body, code.lookup name = some (params,body) → CallScalarProgram body

set_option maxHeartbeats 5000000 in
theorem callScalarProgram_clock_consumed {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (s : CrepSemHOLState width σ) (shape : CallScalarProgram p)
    (table : CallScalarTable s.code) :
    s.clock - (evalCrepSemHOLProgExact s p).2.clock ≤ steps p s := by
  have key : ∀ (x : Nat × Nat) (p : CrepProgHOL width) (s : CrepSemHOLState width σ),
      (s.clock,sizeOf p) = x → CallScalarProgram p → CallScalarTable s.code →
      s.clock - (evalCrepSemHOLProgExact s p).2.clock ≤ steps p s := by
    intro x
    induction x using (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.induction with
    | h x ih0 =>
      intro p s hx shape table
      have ih : ∀ (q : CrepProgHOL width) (t : CrepSemHOLState width σ),
          Prod.Lex (· < ·) (· < ·) (t.clock,sizeOf q) (s.clock,sizeOf p) →
          CallScalarProgram q → t.code = s.code →
          t.clock - (evalCrepSemHOLProgExact t q).2.clock ≤ steps q t := by
        intro q t smaller qshape same
        have tables : CallScalarTable t.code := by rw [same]; exact table
        exact ih0 _ (hx ▸ smaller) q t rfl qshape tables
      clear ih0 hx
      cases shape with
      | base h =>
        rcases run : evalCrepSemHOLProgExact s p with ⟨out,post⟩
        exact scalarProgram_clock_consumed h s post out run
      | @dec name value body hv hb =>
        rw [steps_dec,evalCrepSemHOLProgExact_dec_holShape]
        rcases evalValue : evalCrepSemHOLExp s value with _ | v
        · simp
        · simp only
          rcases bodyRun : evalCrepSemHOLProgExact (CrepSemHOLState.setVar name v s) body with ⟨out,post⟩
          have smaller : Prod.Lex (· < ·) (· < ·)
              ((CrepSemHOLState.setVar name v s).clock,sizeOf body)
              (s.clock,sizeOf (.dec name value body : CrepProgHOL width)) := by
            apply Prod.Lex.right
            simp_wf
          have bound := ih body (CrepSemHOLState.setVar name v s) smaller hb rfl
          rw [bodyRun] at bound
          simp only [CrepSemHOLState.setVar] at bodyRun bound ⊢
          rw [bodyRun]
          simp only
          omega
      | @seq a b ha hb =>
        rw [steps_seq,evalCrepSemHOLProgExact_seq_holShape]
        rcases first : evalCrepSemHOLProgExact s a with ⟨out,middle⟩
        have aBound := ih a s (Prod.Lex.right _ (by simp_wf; omega)) ha rfl
        rw [first] at aBound
        have aClock := evalCrepSemHOLProgExact_clock_le s a
        rw [first] at aClock
        have aCode := evaluateCodeInvariantHOL a s out middle first
        cases out with
        | none =>
          simp only [if_true]
          have small : Prod.Lex (· < ·) (· < ·) (middle.clock,sizeOf b) (s.clock,sizeOf (.seq a b : CrepProgHOL width)) := by
            rcases Nat.lt_or_eq_of_le aClock with h | h
            · apply Prod.Lex.left; exact h
            · have eq : middle.clock = s.clock := by simpa using h
              rw [eq]
              apply Prod.Lex.right
              simp_wf
          have bBound := ih b middle small hb aCode
          have bClock := evalCrepSemHOLProgExact_clock_le middle b
          simp only at *
          omega
        | some r => simp only [if_false,Option.some_ne_none]; simp only at *; omega
      | @ite cond a b hcond ha hb =>
        rw [steps_ite,evalCrepSemHOLProgExact_ite_holShape]
        rcases hv : evalCrepSemHOLExp s cond with _ | ⟨v⟩
        · simp
        · simp only
          by_cases nz : v.1 ≠ 0
          · simp only [if_pos nz]
            have h := ih a s (Prod.Lex.right _ (by simp_wf; omega)) ha rfl
            omega
          · simp only [if_neg nz]
            have h := ih b s (Prod.Lex.right _ (by simp_wf)) hb rfl
            omega
      | @loop condition body hcondition hbody =>
        rcases run : evalCrepSemHOLProgExact s (.while condition body) with ⟨result,final⟩
        have execution := run
        rw [evalCrepSemHOLProgExact_while_holShape] at execution
        rw [steps_while]
        rcases hv : evalCrepSemHOLExp s condition with _ | ⟨w⟩
        · simp only [hv,Prod.mk.injEq] at execution
          obtain ⟨_,rfl⟩ := execution
          simp only
          omega
        · simp only [hv] at execution ⊢
          by_cases nz : w.1 ≠ 0
          · simp only [if_pos nz] at execution
            by_cases zero : s.clock = 0
            · simp only [zero,if_true,Prod.mk.injEq] at execution
              obtain ⟨_,rfl⟩ := execution
              simp [zero,CrepSemHOLState.emptyLocals]
            · simp only [if_neg zero] at execution
              simp only [if_pos (show w.1 ≠ 0 ∧ s.clock ≠ 0 from ⟨nz,zero⟩)]
              rcases bodyRun : evalCrepSemHOLProgExact (decClockCrepSemHOL s) body with ⟨bodyResult,post⟩
              have small : (decClockCrepSemHOL s).clock < s.clock := by simp [decClockCrepSemHOL]; omega
              have bodyBound := ih body (decClockCrepSemHOL s) (Prod.Lex.left _ _ small) hbody rfl
              rw [bodyRun] at bodyBound
              have bodyClock := evalCrepSemHOLProgExact_clock_le (decClockCrepSemHOL s) body
              rw [bodyRun] at bodyClock
              have bodyCode := evaluateCodeInvariantHOL body (decClockCrepSemHOL s) bodyResult post bodyRun
              have smaller : post.clock < s.clock := by simp only [decClockCrepSemHOL] at bodyClock; omega
              have same : post.code = s.code := by simpa [decClockCrepSemHOL] using bodyCode
              simp only [bodyRun] at execution
              change s.clock - 1 - post.clock ≤ steps body (decClockCrepSemHOL s) at bodyBound
              cases bodyResult with
              | none =>
                have rest := ih (.while condition body) post (Prod.Lex.left _ _ smaller) (.loop hcondition hbody) same
                simp only at execution
                rw [execution] at rest
                simp only at *
                omega
              | some r =>
                cases r <;> try (simp_all [exitLoopCrepResult]; omega)
                case «break» label =>
                  cases label <;> simp_all [exitLoopCrepResult] <;> omega
                case «continue» label =>
                  cases label with
                  | zero =>
                    have rest := ih (.while condition body) post (Prod.Lex.left _ _ smaller) (.loop hcondition hbody) same
                    simp only at execution
                    rw [execution] at rest
                    simp only at *
                    omega
                  | succ n => simp_all [exitLoopCrepResult]; omega
          · simp only [if_neg nz,Prod.mk.injEq] at execution
            obtain ⟨_,rfl⟩ := execution
            simp only [nz,false_and,if_false]
            omega
      | call ret name args =>
        cases ret with
        | none =>
          cases hargs : args.mapM (evalCrepSemHOLExp s) with
          | none =>
            rw [steps.eq_def,evalCrepSemHOLProgExact_call_holShape]
            simp [hargs]
          | some values =>
            cases found : s.code.lookup name with
            | none =>
              rw [steps.eq_def,evalCrepSemHOLProgExact_call_holShape]
              simp [hargs,found,lookupCodeFiniteHOL]
            | some pair =>
              obtain ⟨params,body⟩ := pair
              by_cases valid : params.length = values.length ∧ params.Nodup
              · by_cases zero : s.clock = 0
                · rw [steps.eq_def,evalCrepSemHOLProgExact_call_holShape]
                  simp [hargs,found,lookupCodeFiniteHOL,valid.1,valid.2,zero,CrepSemHOLState.emptyLocals]
                · rcases run : evalCrepSemHOLProgExact (decClockCrepSemHOL
                    {s with locals := HolFiniteMapExact.empty.updateList (params.zip values)}) body with ⟨out,post⟩
                  have small : (decClockCrepSemHOL {s with locals := HolFiniteMapExact.empty.updateList (params.zip values)}).clock < s.clock := by
                    simp [decClockCrepSemHOL]; omega
                  have hb := ih body (decClockCrepSemHOL {s with locals := HolFiniteMapExact.empty.updateList (params.zip values)})
                    (Prod.Lex.left _ _ small) (table name params body found) rfl
                  rw [run] at hb
                  have h := call_clock_consumed_from_body none name args s post values params body out
                    hargs found valid.1 valid.2 (by simp) zero run (by simpa [decClockCrepSemHOL] using hb)
                  exact h
              · rw [steps.eq_def,evalCrepSemHOLProgExact_call_holShape]
                simp [hargs,found,lookupCodeFiniteHOL,valid]
        | some names =>
          by_cases nd : names.Nodup
          ·
            cases hargs : args.mapM (evalCrepSemHOLExp s) with
            | none =>
              rw [steps.eq_def,evalCrepSemHOLProgExact_call_holShape]
              simp [hargs]
            | some values =>
              cases found : s.code.lookup name with
              | none =>
                rw [steps.eq_def,evalCrepSemHOLProgExact_call_holShape]
                simp [hargs,found,lookupCodeFiniteHOL]
              | some pair =>
                obtain ⟨params,body⟩ := pair
                by_cases valid : params.length = values.length ∧ params.Nodup
                · by_cases zero : s.clock = 0
                  · rw [steps.eq_def,evalCrepSemHOLProgExact_call_holShape]
                    simp [hargs,found,lookupCodeFiniteHOL,valid.1,valid.2,zero,CrepSemHOLState.emptyLocals,crepReturnInfoNodupError,nd]
                  · rcases run : evalCrepSemHOLProgExact (decClockCrepSemHOL
                      {s with locals := HolFiniteMapExact.empty.updateList (params.zip values)}) body with ⟨out,post⟩
                    have small : (decClockCrepSemHOL {s with locals := HolFiniteMapExact.empty.updateList (params.zip values)}).clock < s.clock := by
                      simp [decClockCrepSemHOL]; omega
                    have hb := ih body (decClockCrepSemHOL {s with locals := HolFiniteMapExact.empty.updateList (params.zip values)})
                      (Prod.Lex.left _ _ small) (table name params body found) rfl
                    rw [run] at hb
                    have h := call_clock_consumed_from_body (some names) name args s post values params body out
                      hargs found valid.1 valid.2 (by intro ns h; cases h; exact nd) zero run (by simpa [decClockCrepSemHOL] using hb)
                    exact h
                · rw [steps.eq_def,evalCrepSemHOLProgExact_call_holShape]
                  simp [hargs,found,lookupCodeFiniteHOL,valid,nd]
          · rw [steps.eq_def,evalCrepSemHOLProgExact_call_holShape]
            cases hargs : args.mapM (evalCrepSemHOLExp s) with
            | none => simp [hargs]
            | some values =>
              cases found : s.code.lookup name with
              | none => simp [hargs,found,lookupCodeFiniteHOL]
              | some pair =>
                obtain ⟨params,body⟩ := pair
                by_cases valid : params.length = values.length ∧ params.Nodup <;>
                  simp [hargs,found,lookupCodeFiniteHOL,crepReturnInfoNodupError,nd,valid]

  exact key _ p s rfl shape table
end SteppedFlapjack.CrepSteps
