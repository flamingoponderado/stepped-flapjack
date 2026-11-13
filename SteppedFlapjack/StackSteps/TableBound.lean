import SteppedFlapjack.StackRemoveSteps.CodeOriginEvaluate
import Flapjack.Compiler.Backend.Semantics.WordSem.EnvListSupport
/-! Concrete whole-table StackSem visit bounds, including nested calls. -/
namespace SteppedFlapjack.StackSteps
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.StackSemEvaluate
open Flapjack.StackSemMeasure Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.StackRemoveSteps.CompCorrect
variable {width : Nat} [NeZero width] {C F : Type}

/-- Control nodes in a Stack program, including call continuations. -/
def stackControlWeight : HolProg width → Nat
  | .seq a b | .ite _ _ _ a b => 1 + stackControlWeight a + stackControlWeight b
  | .loop body => 1 + stackControlWeight body
  | .call ret _ handler => 1 + (match ret with
      | none => 0
      | some (body,_,_,_) => stackControlWeight body) + (match handler with
      | none => 0
      | some (body,_,_) => stackControlWeight body)
  | _ => 1

/-- Maximum control weight in a concrete Stack code table. -/
def stackCodeWeight (code : Spt (HolProg width)) : Nat :=
  (sptToAList code).foldr (fun row weight => max (stackControlWeight row.2) weight) 1

/-- Every code lookup is bounded by the concrete table maximum. -/
theorem stackCodeWeight_lookup (code : Spt (HolProg width)) (loc : Nat) (body : HolProg width)
    (found : sptLookup loc code = some body) : stackControlWeight body ≤ stackCodeWeight code := by
  have member : (loc,body) ∈ sptToAList code := (sptToAList_mem_iff_lookup code loc body).mpr found
  have aux (rows : List (Nat × HolProg width)) : ∀ row ∈ rows,
      stackControlWeight row.2 ≤ rows.foldr (fun row weight => max (stackControlWeight row.2) weight) 1 := by
    induction rows with
    | nil => simp
    | cons row rest ih =>
      intro entry member
      simp only [List.mem_cons] at member
      cases member with
      | inl same => subst entry; simp
      | inr inRest => exact (ih entry inRest).trans (Nat.le_max_right _ _)
  exact aux _ _ member

/-- The compile oracle supplies no new code. Bitmap output may still vary. -/
def emptyCodeOracle (s : StackSemStateFiniteExact width C F) : Prop :=
  ∀ i, (s.compileOracle i).2.1 = []

/-- With an empty code oracle, evaluation cannot increase the table maximum. -/
theorem stackWeight_preserved (p : HolProg width) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width)) (run : evaluate (p,s) = (r,t)) (empty : emptyCodeOracle s) :
    stackCodeWeight t.code ≤ stackCodeWeight s.code ∧ emptyCodeOracle t := by
  have origin := codeOrigin_evaluate p s t r run
  have effect := oracleRunEffect_evaluate p s t r run
  obtain ⟨used,_,shift,_⟩ := effect
  have he : emptyCodeOracle t := by
    intro i
    rw [shift]
    exact empty _
  constructor
  · unfold stackCodeWeight
    have aux (rows : List (Nat × HolProg width)) :
        (∀ row ∈ rows, stackControlWeight row.2 ≤ stackCodeWeight s.code) →
        rows.foldr (fun row weight => max (stackControlWeight row.2) weight) 1 ≤ stackCodeWeight s.code := by
      intro h
      induction rows with
      | nil =>
        have nonempty : 1 ≤ stackCodeWeight s.code := by
          unfold stackCodeWeight
          induction sptToAList s.code with
          | nil => simp
          | cons a rest ih => simp only [List.foldr_cons]; exact ih.trans (Nat.le_max_right _ _)
        exact nonempty
      | cons row rest ih =>
        simp only [List.foldr_cons, max_le_iff]
        exact ⟨h row (by simp), ih (fun row mem => h row (by simp [mem]))⟩
    apply aux
    intro row mem
    obtain ⟨label,program⟩ := row
    have lookup := (sptToAList_mem_iff_lookup t.code label program).mp mem
    rcases origin label program lookup with found | ⟨i,_,name,inside⟩
    · exact stackCodeWeight_lookup s.code label program found
    · rw [empty i] at inside
      cases inside
  · exact he

set_option linter.unnecessarySeqFocus false in
private theorem stackWeight_pos (p : HolProg width) : 1 ≤ stackControlWeight p := by
  cases p <;> (try simp only [stackControlWeight]) <;> try omega
  case call ret dest handler =>
    cases ret <;> cases handler <;> simp [stackControlWeight] <;> omega

set_option maxHeartbeats 5000000 in
/-- Nested calls and handlers visit at most the program weight plus the table
maximum for each unit of clock consumed. -/
theorem stackTable_consumption_bound (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (K : Nat) (empty : emptyCodeOracle s) (weight : stackControlWeight p ≤ K)
    (table : stackCodeWeight s.code ≤ K) :
    steps (p,s) ≤ stackControlWeight p + K * (s.clock - (evaluate (p,s)).2.clock) := by
  by_cases leaf : isRecursive p = false
  · rw [steps_leaf _ _ leaf]
    have pos := stackWeight_pos p
    omega
  · cases hp : p <;> rw [hp] at leaf
    all_goals try (simp [isRecursive] at leaf)
    case seq a b =>
      rw [hp] at weight
      have wa : stackControlWeight a ≤ K := by simp [stackControlWeight] at weight; omega
      have wb : stackControlWeight b ≤ K := by simp [stackControlWeight] at weight; omega
      rcases ha : evaluate (a,s) with ⟨result,middle⟩
      have ba := stackTable_consumption_bound a s K empty wa table
      rw [ha] at ba
      have ca := StackSemEvaluateClock.evaluateClock a s result middle ha
      have stable := stackWeight_preserved a s middle result ha empty
      rw [steps_seq, evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,ha]
      cases result with
      | none =>
        have smaller := seq_second_measure_lt a b s (evaluate (a,s))
        rw [StackSemEvaluateClock.fixClockEvaluate,ha] at smaller
        have bb := stackTable_consumption_bound b middle K stable.2 wb (stable.1.trans table)
        rcases hb : evaluate (b,middle) with ⟨out,post⟩
        have cb := StackSemEvaluateClock.evaluateClock b middle out post hb
        rw [hb] at bb
        simp only [hb]
        have spent : s.clock-middle.clock + (middle.clock-post.clock) = s.clock-post.clock := by omega
        simp only [stackControlWeight]
        nlinarith
      | some r =>
        simp only [stackControlWeight]
        nlinarith
    case ite cmp reg ri a b =>
      rw [hp] at weight
      have wa : stackControlWeight a ≤ K := by simp [stackControlWeight] at weight; omega
      have wb : stackControlWeight b ≤ K := by simp [stackControlWeight] at weight; omega
      rw [steps_ite, evaluate_ite]
      cases hx : getVar reg s with
      | none => simp [stackControlWeight]; omega
      | some x =>
        cases hy : getVarImm (HolRegImm.toWordRegImm ri) s with
        | none => simp [stackControlWeight]; omega
        | some y =>
          cases hw : wordSemWordCmp cmp x y with
          | none => simp [hw,stackControlWeight]; omega
          | some v =>
            cases v with
            | false =>
              have hb := stackTable_consumption_bound b s K empty wb table
              simp only [hw,stackControlWeight]
              omega
            | true =>
              have ha := stackTable_consumption_bound a s K empty wa table
              simp only [hw,stackControlWeight]
              omega
    case loop body =>
      rw [hp] at weight
      have wb : stackControlWeight body ≤ K := by simp [stackControlWeight] at weight; omega
      rcases hb : evaluate (body,s) with ⟨res,middle⟩
      have bb := stackTable_consumption_bound body s K empty wb table
      rw [hb] at bb
      have hc := StackSemEvaluateClock.evaluateClock body s res middle hb
      have stable := stackWeight_preserved body s middle res hb empty
      rw [steps_loop,evaluate_loop,StackSemEvaluateClock.fixClockEvaluate,hb]
      simp only
      by_cases cont : contLoop res = true
      · by_cases hz : middle.clock = 0
        · simp [cont,hz,StackSemStateOps.emptyEnv,stackControlWeight] at *
          nlinarith
        · have smaller := loop_reentry_measure_lt body s (evaluate (body,s)) (by
            rw [StackSemEvaluateClock.fixClockEvaluate,hb]; exact hz)
          rw [StackSemEvaluateClock.fixClockEvaluate,hb] at smaller
          have rest := stackTable_consumption_bound (.loop body) (decClock middle) K stable.2 weight (stable.1.trans table)
          rcases hl : evaluate (.loop body,decClock middle) with ⟨out,post⟩
          have cl := StackSemEvaluateClock.evaluateClock (.loop body) (decClock middle) out post hl
          have spent : s.clock-post.clock = (s.clock-middle.clock)+(middle.clock-1-post.clock)+1 := by simp only [decClock] at cl; omega
          rw [hl] at rest
          simp only [decClock,stackControlWeight] at rest
          simp only [decClock] at hl
          simp [cont,hz,decClock,stackControlWeight]
          simp only [stackControlWeight] at weight
          nlinarith
      · simp [cont,stackControlWeight]
        nlinarith
    case rawCall label =>
      cases hf : sptLookup label s.code with
      | none => simp [steps_rawCall,evaluate_rawCall,hf,stackControlWeight]
      | some prog =>
        cases hd : destSeq prog with
        | none => simp [steps_rawCall,evaluate_rawCall,hf,hd,stackControlWeight]
        | some pair =>
          obtain ⟨first,body⟩ := pair
          have bodyWeight : stackControlWeight body ≤ K := by
            have h := (stackCodeWeight_lookup s.code label prog hf).trans table
            cases prog <;> simp [destSeq] at hd
            case seq a b =>
              obtain ⟨rfl,rfl⟩ := hd
              simp [stackControlWeight] at h
              omega
          by_cases hz : s.clock = 0
          · simp [steps_rawCall,evaluate_rawCall,hf,hd,hz,StackSemStateOps.emptyEnv,stackControlWeight]
          · have smaller := callee_measure_lt body (.rawCall label) s hz
            have hrec := stackTable_consumption_bound body (decClock s) K empty bodyWeight table
            rcases run : evaluate (body,decClock s) with ⟨out,post⟩
            have clock := StackSemEvaluateClock.evaluateClock body (decClock s) out post run
            change post.clock ≤ s.clock-1 at clock
            rw [run] at hrec
            change steps (body,decClock s) ≤ stackControlWeight body + K*(s.clock-1-post.clock) at hrec
            have spent : s.clock-post.clock = (s.clock-1-post.clock)+1 := by omega
            rw [steps_rawCall,evaluate_rawCall]
            simp only [hf,hd,hz,if_false,run,stackControlWeight]
            split_ifs <;> simp_all only <;> nlinarith
    case jumpLower left right label =>
      cases h1 : getVar left s with
      | none => simp [steps_jumpLower,evaluate_jumpLower,h1,stackControlWeight]
      | some v1 =>
        cases v1 with
        | loc l o => simp [steps_jumpLower,evaluate_jumpLower,h1,stackControlWeight]
        | word x =>
          cases h2 : getVar right s with
          | none => simp [steps_jumpLower,evaluate_jumpLower,h1,h2,stackControlWeight]
          | some v2 =>
            cases v2 with
            | loc l o => simp [steps_jumpLower,evaluate_jumpLower,h1,h2,stackControlWeight]
            | word y =>
              by_cases hw : wordCmpHOL .lower x y = true
              · cases hf : findCode (.inl label) s.regs s.code with
                | none => simp [steps_jumpLower,evaluate_jumpLower,h1,h2,hw,hf,stackControlWeight]
                | some prog =>
                  have lookup : sptLookup label s.code = some prog := by simpa [findCode] using hf
                  have progWeight := (stackCodeWeight_lookup s.code label prog lookup).trans table
                  by_cases hz : s.clock = 0
                  · simp [steps_jumpLower,evaluate_jumpLower,h1,h2,hw,hf,hz,StackSemStateOps.emptyEnv,stackControlWeight]
                  · have smaller := callee_measure_lt prog (.jumpLower left right label) s hz
                    have hrec := stackTable_consumption_bound prog (decClock s) K empty progWeight table
                    rcases run : evaluate (prog,decClock s) with ⟨out,post⟩
                    have clock := StackSemEvaluateClock.evaluateClock prog (decClock s) out post run
                    change post.clock ≤ s.clock-1 at clock
                    rw [run] at hrec
                    change steps (prog,decClock s) ≤ stackControlWeight prog + K*(s.clock-1-post.clock) at hrec
                    have spent : s.clock-post.clock = (s.clock-1-post.clock)+1 := by omega
                    rw [steps_jumpLower,evaluate_jumpLower]
                    simp only [h1,h2,hw,if_true,hf,hz,if_false,run,stackControlWeight]
                    split_ifs <;> simp_all only <;> nlinarith
              · simp [steps_jumpLower,evaluate_jumpLower,h1,h2,hw,stackControlWeight]
    case call ret dest handler =>
      cases ret with
      | none =>
        cases hf : findCode dest s.regs s.code with
        | none =>
          have pos := stackWeight_pos (.call none dest handler : HolProg width)
          simp [steps_call_none,evaluate_call,hf]; omega
        | some prog =>
          cases handler with
          | some h =>
            obtain ⟨body,l1,l2⟩ := h
            simp [steps_call_none,evaluate_call,hf,stackControlWeight]
          | none =>
            by_cases hz : s.clock = 0
            · simp [steps_call_none,evaluate_call,hf,hz,StackSemStateOps.emptyEnv,stackControlWeight]
            · obtain ⟨label,lookup⟩ := findCode_sptLookup hf
              have progWeight := (stackCodeWeight_lookup s.code label prog lookup).trans table
              have smaller := callee_measure_lt prog (.call none dest none) s hz
              have hrec := stackTable_consumption_bound prog (decClock s) K empty progWeight table
              rcases run : evaluate (prog,decClock s) with ⟨out,post⟩
              have clock := StackSemEvaluateClock.evaluateClock prog (decClock s) out post run
              change post.clock ≤ s.clock-1 at clock
              rw [run] at hrec
              change steps (prog,decClock s) ≤ stackControlWeight prog + K*(s.clock-1-post.clock) at hrec
              have spent : s.clock-post.clock = (s.clock-1-post.clock)+1 := by omega
              rw [steps_call_none,evaluate_call]
              simp only [hf,hz,if_false,stackControlWeight]
              rw [StackSemEvaluateClock.fixClockEvaluate,run]
              split_ifs <;> simp_all only <;> nlinarith
      | some entry =>
        obtain ⟨body,link,l1,l2⟩ := entry
        rw [hp] at weight
        have bodyWeight : 1 + stackControlWeight body ≤
            stackControlWeight (.call (some (body,link,l1,l2)) dest handler) := by
          cases handler with
          | none => simp [stackControlWeight]
          | some h => obtain ⟨hprog,hl1,hl2⟩ := h; simp [stackControlWeight]
        have bodyLe : stackControlWeight body ≤ K := by omega
        cases hf : findCode dest (s.regs.eraseEq link) s.code with
        | none => simp [steps_call_some,evaluate_call,hf]; omega
        | some prog =>
          by_cases hz : s.clock = 0
          · simp [steps_call_some,evaluate_call,hf,hz,StackSemStateOps.emptyEnv]; omega
          · obtain ⟨label,lookup⟩ := findCode_sptLookup hf
            have progWeight := (stackCodeWeight_lookup s.code label prog lookup).trans table
            let start := decClock (setVar link (.loc l1 l2) s)
            have hs0 : (setVar link (.loc l1 l2) s).clock ≠ 0 := by simpa [setVar] using hz
            have smaller := callee_measure_lt prog (.call (some (body,link,l1,l2)) dest handler)
              (setVar link (.loc l1 l2) s) hs0
            have hpar : stackSemMeasure (.call (some (body,link,l1,l2)) dest handler)
                (setVar link (.loc l1 l2) s) = stackSemMeasure (.call (some (body,link,l1,l2)) dest handler) s := by
              simp [stackSemMeasure,setVar]
            rw [hpar] at smaller
            have callee := stackTable_consumption_bound prog start K empty progWeight table
            rcases he : evaluate (prog,start) with ⟨out,post⟩
            have clock := StackSemEvaluateClock.evaluateClock prog start out post he
            change post.clock ≤ s.clock-1 at clock
            have stable := stackWeight_preserved prog start post out he empty
            rw [he] at callee
            change steps (prog,start) ≤ stackControlWeight prog + K*(s.clock-1-post.clock) at callee
            have spent : s.clock-post.clock = (s.clock-1-post.clock)+1 := by omega
            change evaluate (prog,decClock (setVar link (.loc l1 l2) s)) = (out,post) at he
            have hfix := StackSemEvaluateClock.fixClockEvaluate prog start
            rw [he] at hfix
            change fixClock (decClock (setVar link (.loc l1 l2) s)) (out,post) = (out,post) at hfix
            rw [steps_call_some,evaluate_call]
            simp only [hf,hz,if_false,he,hfix]
            cases out with
            | none => (try simp only); rw [spent]; nlinarith
            | some result =>
              cases result <;> (try simp only) <;> try { rw [spent]; nlinarith }
              case result value =>
                by_cases hv : value = .loc l1 l2
                · have hcont := stackTable_consumption_bound body post K stable.2 bodyLe (stable.1.trans table)
                  rcases hr : evaluate (body,post) with ⟨res,final⟩
                  have finalClock := StackSemEvaluateClock.evaluateClock body post res final hr
                  rw [hr] at hcont
                  have partition : s.clock-final.clock = (s.clock-1-post.clock)+(post.clock-final.clock)+1 := by omega
                  simp only [hv,if_true,ne_eq,not_true_eq_false,if_false]
                  rw [partition]
                  nlinarith
                · simp [hv]
                  rw [spent]
                  nlinarith
              case exception value =>
                cases handler with
                | none => simp only; rw [spent]; nlinarith
                | some h =>
                  obtain ⟨handlerBody,hl1,hl2⟩ := h
                  have handlerWeight : 1 + stackControlWeight handlerBody ≤
                      stackControlWeight (.call (some (body,link,l1,l2)) dest (some (handlerBody,hl1,hl2))) := by
                    simp [stackControlWeight]
                  have handlerLe : stackControlWeight handlerBody ≤ K := by omega
                  by_cases hv : value = .loc hl1 hl2
                  · have hcont := stackTable_consumption_bound handlerBody post K stable.2 handlerLe (stable.1.trans table)
                    rcases hr : evaluate (handlerBody,post) with ⟨res,final⟩
                    have finalClock := StackSemEvaluateClock.evaluateClock handlerBody post res final hr
                    rw [hr] at hcont
                    have partition : s.clock-final.clock = (s.clock-1-post.clock)+(post.clock-final.clock)+1 := by omega
                    simp only [hv,if_true,ne_eq,not_true_eq_false,if_false,hr]
                    rw [partition]
                    nlinarith
                  · simp [hv]
                    rw [spent]
                    nlinarith
termination_by stackSemMeasure p s
decreasing_by
  all_goals subst p
  all_goals try (rw [StackSemEvaluateClock.fixClockEvaluate,ha] at smaller)
  all_goals try (rw [StackSemEvaluateClock.fixClockEvaluate,hb] at smaller)
  all_goals try (rw [hpar] at smaller)
  all_goals try (rw [hp])
  all_goals try (have _hh := StackSemEvaluateClock.evaluateClock _ _ _ _ he
                 apply lexNat_of_clock_lt
                 simp only [start,decClock,setVar] at *
                 omega)
  all_goals try (apply lexNat_of_clock_lt; simp only [decClock]; omega)
  all_goals try (first | exact smaller | exact seq_first_measure_lt _ _ _ | exact if_first_measure_lt _ _ _ _ _ _ | exact if_second_measure_lt _ _ _ _ _ _ | exact loop_body_measure_lt _ _)


/-- A concrete visit bound from the initial program, code table, and clock. -/
theorem stackTable_clock_bound (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (empty : emptyCodeOracle s) :
    steps (p,s) ≤ stackControlWeight p + max (stackControlWeight p) (stackCodeWeight s.code) * s.clock := by
  let K := max (stackControlWeight p) (stackCodeWeight s.code)
  have bound := stackTable_consumption_bound p s K empty (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have sub : s.clock - (evaluate (p,s)).2.clock ≤ s.clock := Nat.sub_le _ _
  exact bound.trans (Nat.add_le_add_left (Nat.mul_le_mul_left K sub) _)

end SteppedFlapjack.StackSteps
