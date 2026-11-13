import SteppedFlapjack.WordSimpSteps.LoopSequenceCompile
import SteppedFlapjack.WordToStackSteps.NormalizedClock

/-! Clock-based visit bounds for recursive, call-free Word programs. -/
namespace SteppedFlapjack.WordSimpSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
open SteppedFlapjack.WordToStackSteps SteppedFlapjack.WordInstSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- Executable count of control nodes, independent of literal values. -/
def wordControlWeight : WordLangProgHOL (BitVec width) → Nat
  | .seq a b | .ite _ _ _ a b => 1 + wordControlWeight a + wordControlWeight b
  | .loop _ body _ => 1 + wordControlWeight body
  | .call ret _ _ handler => 1 + (match ret with
      | none => 0
      | some (_,_,body,_,_) => wordControlWeight body) + (match handler with
      | none => 0
      | some (_,body,_,_) => wordControlWeight body)
  | _ => 1
/-- Maximum control weight of any function in the concrete Word code table. -/
def wordCodeWeight (code : Spt (Nat × WordLangProgHOL (BitVec width))) : Nat :=
  (sptToAList code).foldr (fun row weight => max (wordControlWeight row.2.2) weight) 1

omit [NeZero width] in
/-- Every looked-up function is bounded by the computed table weight. -/
theorem wordCodeWeight_lookup (code : Spt (Nat × WordLangProgHOL (BitVec width)))
    (loc arity : Nat) (body : WordLangProgHOL (BitVec width))
    (found : sptLookup loc code = some (arity,body)) : wordControlWeight body ≤ wordCodeWeight code := by
  have member : (loc,(arity,body)) ∈ sptToAList code := (sptToAList_mem_iff_lookup code loc (arity,body)).mpr found
  have aux (rows : List (Nat × (Nat × WordLangProgHOL (BitVec width)))) : ∀ row ∈ rows,
      wordControlWeight row.2.2 ≤ rows.foldr (fun row weight => max (wordControlWeight row.2.2) weight) 1 := by
    induction rows with
    | nil => simp
    | cons row rest ih =>
      intro entry member
      simp only [List.mem_cons] at member
      cases member with
      | inl same => subst entry; simp
      | inr inRest => exact (ih entry inRest).trans (Nat.le_max_right _ _)
  exact aux _ _ member

theorem wordControl_consumption_bound {p : WordLangProgHOL (BitVec width)} (shape : Program p)
    (s : WordSemStateFiniteExact width C F) :
    steps p s ≤ wordControlWeight p * (s.clock - (evaluate p s).2.clock + 1) := by
  induction shape generalizing s <;> try { rw [steps_leaf _ _ rfl]; apply Nat.mul_pos <;> simp [wordControlWeight] }
  case seq a b ha hb iha ihb =>
    have ha := iha s
    rw [steps_seq, evaluate, fix_clock_evaluate]
    rcases run : evaluate a s with ⟨result,mid⟩
    simp only [run] at ha
    cases result with
    | some r =>
      simp only
      have sz : wordControlWeight a + 1 ≤ wordControlWeight (.seq a b : WordLangProgHOL (BitVec width)) := by simp [wordControlWeight]; omega
      nlinarith
    | none =>
      have hb := ihb mid
      have ca := (evaluate_clock a s none mid run).1
      rcases runb : evaluate b mid with ⟨result,post⟩
      have cb := (evaluate_clock b mid result post runb).1
      simp only [runb] at hb ⊢
      have sz : 1 + wordControlWeight a + wordControlWeight b ≤ wordControlWeight (.seq a b : WordLangProgHOL (BitVec width)) := by simp [wordControlWeight]
      have spent : s.clock - mid.clock + (mid.clock - post.clock) = s.clock - post.clock := by omega
      nlinarith
  case ite cmp r ri a b ha hb iha ihb =>
    have sizea : wordControlWeight a + 1 ≤ wordControlWeight (.ite cmp r ri a b : WordLangProgHOL (BitVec width)) := by simp [wordControlWeight]; omega
    have sizeb : wordControlWeight b + 1 ≤ wordControlWeight (.ite cmp r ri a b : WordLangProgHOL (BitVec width)) := by simp [wordControlWeight]; omega
    rw [steps_ite, evaluate]
    cases hx : getVar r s with
    | none => simp; omega
    | some x =>
      cases hy : getVarImm ri s with
      | none => simp; omega
      | some y =>
        cases hv : wordSemWordCmp cmp x y with
        | none => simp [hv]; omega
        | some v =>
          cases v with
          | false =>
            have h := ihb s
            simp only [hv] at ⊢
            nlinarith
          | true =>
            have h := iha s
            simp only [hv] at ⊢
            nlinarith
  case loop names exits body hb ih =>
    induction hc : s.clock using Nat.strongRecOn generalizing s with
    | _ clock rec =>
      simp only [wordControlWeight]
      have sz : wordControlWeight body + 1 ≤ 1 + wordControlWeight body := by omega
      rw [steps_loop, evaluate]
      cases cut : cutState (names,.ln) s with
      | none => simp; nlinarith
      | some entry =>
        obtain ⟨c,_⟩ := cutState_clock_termdep _ _ _ cut
        have entryClock : entry.clock = clock := c.trans hc
        have hbody := ih entry
        simp only [fix_clock_evaluate]
        rcases run : evaluate body entry with ⟨result,post⟩
        have hclock := (evaluate_clock body entry result post run).1
        simp only [run,entryClock] at hbody
        rw [entryClock] at hclock
        have sizeProduct := Nat.mul_le_mul_right (clock - post.clock + 1) sz
        have positive : 1 ≤ clock - post.clock + 1 := by omega
        by_cases cont : wordSemContLoop result = true
        · by_cases hz : post.clock = 0
          · simp only [hz, Nat.sub_zero] at hbody sizeProduct positive
            simp [cont,hz,flushState]
            nlinarith
          · have smaller : (decClock post).clock < s.clock := by simp [decClock]; omega
            have rest := rec _ (by simpa [hc] using smaller) (decClock post) rfl
            rcases hfinal : evaluate (.loop names body exits) (decClock post) with ⟨res,final⟩
            have finalClock := (evaluate_clock (.loop names body exits) (decClock post) res final hfinal).1
            have spent : clock - final.clock = (clock - post.clock) + (post.clock - 1 - final.clock) + 1 := by
              simp only [decClock] at finalClock
              omega
            have sizeEq : wordControlWeight (.loop names body exits : WordLangProgHOL (BitVec width)) =
                1 + wordControlWeight body := by rfl
            rw [hfinal] at rest
            simp only [decClock, sizeEq] at rest
            simp only [decClock] at hfinal
            simp [cont, hz, wordSemSTOP, decClock, hfinal]
            nlinarith
        · simp only [cont, Bool.false_eq_true, ↓reduceIte, false_and]
          cases result with
          | none => simp [wordSemContLoop] at cont
          | some r =>
            cases r <;> simp only [wordSemExitLoop]
            case «break» n =>
              cases n with
              | zero =>
                cases out : cutState (exits,.ln) post with
                | none => simp; nlinarith
                | some final =>
                  have outClock := cutState_clock_termdep _ _ _ out
                  rcases outClock with ⟨outClock,_⟩
                  simp [outClock]
                  nlinarith
              | succ n => simp; nlinarith
            all_goals simp; nlinarith


theorem wordControl_le_size {p : WordLangProgHOL (BitVec width)} (shape : Program p) :
    wordControlWeight p ≤ sizeOf p := by
  induction shape <;> simp_all [wordControlWeight] <;> omega

/-- The executable control-node count bounds visits using the initial clock. -/
theorem wordControl_clock_bound {p : WordLangProgHOL (BitVec width)} (shape : Program p)
    (s : WordSemStateFiniteExact width C F) : steps p s ≤ wordControlWeight p * (s.clock + 1) := by
  have bound := wordControl_consumption_bound shape s
  exact bound.trans (Nat.mul_le_mul_left _ (by omega))

/-- The control-node bound implies the earlier size-based consumption bound. -/
theorem wordProgram_consumption_bound {p : WordLangProgHOL (BitVec width)} (shape : Program p)
    (s : WordSemStateFiniteExact width C F) :
    steps p s ≤ sizeOf p * (s.clock - (evaluate p s).2.clock + 1) :=
  (wordControl_consumption_bound shape s).trans
    (Nat.mul_le_mul_right _ (wordControl_le_size shape))

/-- A call-free Word execution has a syntax-based bound in the initial clock. -/
theorem wordProgram_clock_bound {p : WordLangProgHOL (BitVec width)} (shape : Program p)
    (s : WordSemStateFiniteExact width C F) : steps p s ≤ sizeOf p * (s.clock + 1) := by
  have bound := wordProgram_consumption_bound shape s
  have h := Nat.mul_le_mul_left (sizeOf p) (show s.clock - (evaluate p s).2.clock + 1 ≤ s.clock + 1 by omega)
  exact Nat.le_trans bound h

/-- The existing sequence bound follows from the general recursive bound. -/
theorem loopSequence_clock_bound {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p)
    (s : WordSemStateFiniteExact width C F) : steps p s ≤ sizeOf p * (s.clock+1) :=
  wordProgram_clock_bound (loopSequence_program shape) s


set_option linter.unnecessarySeqFocus false in
omit [NeZero width] in
private theorem weight_pos (p : WordLangProgHOL (BitVec width)) : 1 ≤ wordControlWeight p := by
  cases p <;> (try simp only [wordControlWeight]) <;> try omega
  case call ret dest args handler =>
    cases ret <;> cases handler <;> simp [wordControlWeight] <;> omega

set_option maxHeartbeats 5000000 in
/-- An execution over a safe Word function table visits at most its initial
control weight plus the concrete table maximum per unit of clock consumed.
This covers nested ordinary and tail calls and both continuation paths. -/
theorem wordTable_consumption_bound : ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F) (K : Nat),
    noMtSubprogsHOL p = true → noInstallSubprogsHOL p = true →
    WordProps.noMtCode s.code → WordProps.noInstallCode s.code →
    wordControlWeight p ≤ K → wordCodeWeight s.code ≤ K →
    steps p s ≤ wordControlWeight p + K * (s.clock - (evaluate p s).2.clock) := by
  apply evaluate_ind (fun p s => ∀ K, noMtSubprogsHOL p = true → noInstallSubprogsHOL p = true →
    WordProps.noMtCode s.code → WordProps.noInstallCode s.code →
    wordControlWeight p ≤ K → wordCodeWeight s.code ≤ K →
    steps p s ≤ wordControlWeight p + K * (s.clock - (evaluate p s).2.clock))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try { intros; rw [steps_leaf _ _ rfl]; simp [wordControlWeight] }
  case refine_12 =>
    intro p s ih K mt
    simp [noMtSubprogsHOL,notCreatedSubprogsWithMemOp] at mt
  case refine_13 =>
    intro a b s ih K mt ni mtCode niCode weight table
    simp only [noMtSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] at mt
    simp only [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] at ni
    have wa : wordControlWeight a ≤ K := by simp [wordControlWeight] at weight; omega
    have wb : wordControlWeight b ≤ K := by simp [wordControlWeight] at weight; omega
    have ha := ih.2 K mt.1 ni.1 mtCode niCode wa table
    have code := code_evaluate a s ni.1 niCode
    rw [steps_seq, evaluate, fix_clock_evaluate]
    rcases he : evaluate a s with ⟨res,t⟩
    rw [he] at code
    simp only at code
    simp only [he] at ha
    have ca := (evaluate_clock a s res t he).1
    cases res with
    | none =>
      have hb := ih.1 none t ⟨he.symm,rfl⟩ K mt.2 ni.2
        (by simpa only [code] using mtCode) (by simpa only [code] using niCode) wb
        (by simpa only [code] using table)
      rcases hbRun : evaluate b t with ⟨out,post⟩
      have cb := (evaluate_clock b t out post hbRun).1
      simp only [hbRun] at hb ⊢
      have spent : s.clock - t.clock + (t.clock - post.clock) = s.clock - post.clock := by omega
      simp only [wordControlWeight]
      nlinarith
    | some r =>
      simp only [wordControlWeight]
      nlinarith
  case refine_18 =>
    intro cmp r ri a b s ih K mt ni mtCode niCode weight table
    simp only [noMtSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] at mt
    simp only [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] at ni
    have wa : wordControlWeight a ≤ K := by simp [wordControlWeight] at weight; omega
    have wb : wordControlWeight b ≤ K := by simp [wordControlWeight] at weight; omega
    rw [steps_ite, evaluate]
    cases hx : getVar r s with
    | none => simp [wordControlWeight]; omega
    | some x =>
      cases hy : getVarImm ri s with
      | none => simp [wordControlWeight]; omega
      | some y =>
        cases hv : wordSemWordCmp cmp x y with
        | none => simp [hv,wordControlWeight]; omega
        | some v =>
          cases v with
          | false =>
            have hb := ih.2 (some x) (some y) x y false ⟨by simp [hx,hy],rfl,rfl,hv,by simp⟩
              K mt.2 ni.2 mtCode niCode wb table
            simp only [hv,wordControlWeight]
            omega
          | true =>
            have ha := ih.1 (some x) (some y) x y true ⟨by simp [hx,hy],rfl,rfl,hv,rfl⟩
              K mt.1 ni.1 mtCode niCode wa table
            simp only [hv,wordControlWeight]
            omega
  case refine_19 =>
    intro names body exitNames s ih K mt ni mtCode niCode weight table
    have mtBody : noMtSubprogsHOL body = true := by simpa [noMtSubprogsHOL,notCreatedSubprogsWithMemOp] using mt
    have niBody : noInstallSubprogsHOL body = true := by simpa [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp] using ni
    have wb : wordControlWeight body ≤ K := by simp [wordControlWeight] at weight; omega
    rw [steps_loop, evaluate]
    cases hc : cutState (names, .ln) s with
    | none => simp [wordControlWeight]
    | some u =>
      have ucode : u.code = s.code := by obtain ⟨l,rfl⟩ := cutStateConst _ _ _ hc; rfl
      have hcut := cutState_clock_termdep _ _ _ hc
      have uMt : WordProps.noMtCode u.code := by simpa only [ucode] using mtCode
      have uNi : WordProps.noInstallCode u.code := by simpa only [ucode] using niCode
      have uTable : wordCodeWeight u.code ≤ K := by simpa only [ucode] using table
      have hb := ih.2 u hc K mtBody niBody uMt uNi wb uTable
      have hcode := code_evaluate body u niBody uNi
      simp only [fix_clock_evaluate]
      rcases he : evaluate body u with ⟨res, v⟩
      rw [he] at hcode
      simp only at hcode
      simp only [he] at hb
      rw [hcut.1] at hb
      have hclock := (evaluate_clock body u res v he).1
      by_cases hcont : wordSemContLoop res = true
      · by_cases hz : v.clock = 0
        · simp only [hz,Nat.sub_zero] at hb
          simp [hcont, hz, flushState,wordControlWeight]
          nlinarith
        · have vMt : WordProps.noMtCode v.code := by simpa only [hcode] using uMt
          have vNi : WordProps.noInstallCode v.code := by simpa only [hcode] using uNi
          have vTable : wordCodeWeight v.code ≤ K := by simpa only [hcode] using uTable
          have ht := ih.1 u res v ⟨hc, he.symm, hcont, hz⟩ K mt ni vMt vNi weight vTable
          rcases hf : evaluate (.loop names body exitNames) (decClock v) with ⟨out,post⟩
          have finalClock := (evaluate_clock (.loop names body exitNames) (decClock v) out post hf).1
          have spent : s.clock-post.clock = (s.clock-v.clock)+(v.clock-1-post.clock)+1 := by simp only [decClock] at finalClock; omega
          dsimp only [wordSemSTOP] at ht
          rw [hf] at ht
          simp only [decClock,wordControlWeight] at ht
          simp only [decClock] at hf
          simp [hcont,hz,wordSemSTOP,decClock,hf,wordControlWeight]
          simp only [wordControlWeight] at weight
          nlinarith
      · simp only [hcont, Bool.false_eq_true, ↓reduceIte, false_and]
        cases res with
        | none => simp [wordSemContLoop] at hcont
        | some r =>
          cases r <;> simp only [wordSemExitLoop,wordControlWeight] <;> try nlinarith
          case «break» k =>
            cases k with
            | zero =>
              cases hout : cutState (exitNames, .ln) v with
              | none => simp; nlinarith
              | some w =>
                have hw := cutState_clock_termdep _ _ _ hout
                change 1 + (steps body u + 0) ≤ 1 + wordControlWeight body + K * (s.clock-w.clock)
                rw [hw.1]
                nlinarith
            | succ n => simp; nlinarith
  case refine_26 =>
    intro ret dest args handler s ih K mt ni mtCode niCode weight table
    rcases ih with ⟨hreturn, hexception, hcallee, htail⟩
    cases hg : getVars args s with
    | none =>
      have h := weight_pos (.call ret dest args handler : WordLangProgHOL (BitVec width))
      simp [evaluate, steps.eq_def, hg]; omega
    | some xs =>
      by_cases hbad : wordSemBadDestArgs dest args = true
      · have h := weight_pos (.call ret dest args handler : WordLangProgHOL (BitVec width))
        simp [evaluate, steps.eq_def, hg, hbad]; omega
      · cases hf : wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with
        | none =>
          have h := weight_pos (.call ret dest args handler : WordLangProgHOL (BitVec width))
          simp [evaluate, steps.eq_def, hg, hbad, hf]; omega
        | some triple =>
          obtain ⟨args1, prog, ss⟩ := triple
          obtain ⟨k,n,lookup⟩ := WordProps.findCode_lookup s.code dest _ _ _ prog _ hf
          have progMt := mtCode k n prog lookup
          have progNi := niCode k n prog lookup
          have progW := (wordCodeWeight_lookup s.code k n prog lookup).trans table
          cases ret with
          | none =>
            cases handler with
            | some handler => simp [evaluate, steps.eq_def, hg, hbad, hf, wordControlWeight]
            | none =>
              by_cases hz : s.clock = 0
              · simp [evaluate, steps.eq_def, hg, hbad, hf, hz, flushState,wordControlWeight]
              · have ht := htail xs (args1,prog,ss) args1 (prog,ss) prog ss
                  ⟨hg,hbad,hf,rfl,rfl,rfl,rfl,hz⟩ K progMt progNi mtCode niCode progW table
                rw [evaluate, steps.eq_def]
                simp only [hg, hbad, Bool.false_eq_true, ↓reduceIte, hf, hz]
                simp only [dif_pos (tailCallMeasure dest args s args1 ss prog hz)]
                change steps prog (WordSemStateFiniteExact.callEnv args1 ss (decClock s)) ≤
                  wordControlWeight prog + K * (s.clock - 1 - (evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (decClock s))).2.clock) at ht
                rcases run : evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (decClock s)) with ⟨out,post⟩
                have clock := (evaluate_clock prog _ out post run).1
                change post.clock ≤ s.clock-1 at clock
                rw [run] at ht
                have spent : s.clock-post.clock = (s.clock-1-post.clock)+1 := by omega
                simp only [↓reduceDIte]
                split_ifs <;> simp_all only [wordControlWeight] <;> nlinarith
          | some ret =>
            obtain ⟨n, names, retHandler, l1, l2⟩ := ret
            have retWeight : 1 + wordControlWeight retHandler ≤
                wordControlWeight (.call (some (n,names,retHandler,l1,l2)) dest args handler) := by
              cases handler with
              | none => simp [wordControlWeight]
              | some h => obtain ⟨v,hprog,hl1,hl2⟩ := h; simp [wordControlWeight]
            have retLe : wordControlWeight retHandler ≤ K := by omega
            by_cases hnames : sptDomainEmpty names.1 ∨ ¬ n.Nodup
            · simp [evaluate, steps.eq_def, hg, hbad, hf, hnames]; omega
            · cases he : wordSemCutEnvs names s.locals with
              | none => simp [evaluate, steps.eq_def, hg, hbad, hf, hnames, he]; omega
              | some envs =>
                by_cases hz : s.clock = 0
                · simp [evaluate, steps.eq_def, hg, hbad, hf, hnames, he, hz,flushState]; omega
                · have hpre : (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))).code = s.code :=
                    code_pushEnv envs handler _
                  have hc := hcallee xs (args1,prog,ss) args1 (prog,ss) prog ss
                    (n,names,retHandler,l1,l2) n (names,retHandler,l1,l2) names
                    (retHandler,l1,l2) retHandler (l1,l2) l1 l2 envs
                    ⟨hg,hbad,hf,rfl,rfl,rfl,rfl,rfl,rfl,rfl,hnames,he,hz⟩
                      K progMt progNi (hpre ▸ mtCode) (hpre ▸ niCode) progW (hpre ▸ table)
                  let entry := WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))
                  rcases ev : evaluate prog entry with ⟨result,middle⟩
                  have hc' := hc
                  change steps prog entry ≤ wordControlWeight prog + K * (entry.clock - (evaluate prog entry).2.clock) at hc'
                  have entryClock : entry.clock = s.clock-1 := by simp [entry,WordSemStateFiniteExact.callEnv,pushEnv_clock,decClock]
                  have bodyClock := (evaluate_clock prog entry result middle ev).1
                  rw [entryClock] at bodyClock
                  rw [entryClock,ev] at hc'
                  dsimp only [entry] at hc'
                  have spent : s.clock-middle.clock = (s.clock-1-middle.clock)+1 := by omega
                  have badFalse : wordSemBadDestArgs dest args = false := Bool.eq_false_of_not_eq_true hbad
                  rw [steps_call_returning dest args n names retHandler l1 l2 handler s middle result xs args1 ss prog envs hg badFalse hf hnames he hz ev]
                  have hcall := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                  rw [hcall]
                  simp only [hg,hbad,hf,hnames,he,hz, ↓reduceIte]
                  change evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))) = (result,middle) at ev
                  simp only [Bool.false_eq_true,↓reduceIte,ev]
                  cases result with
                  | none => simp only; rw [spent]; nlinarith
                  | some result =>
                    cases result <;> simp only <;> try { rw [spent]; nlinarith }
                    case result x ys =>
                      by_cases hv : x ≠ .loc l1 l2 ∨ ys.length ≠ n.length
                      · simp only [hv,if_true]; rw [spent]; nlinarith
                      · cases hp : popEnv middle with
                        | none => simp only [hv,if_false]; rw [spent]; nlinarith
                        | some restored =>
                          have hclock := popEnv_clock middle restored hp
                          by_cases hd : sptDomainEqUnion restored.locals envs.1 envs.2
                          · have retMt : noMtSubprogsHOL retHandler = true := by
                              cases handler with
                              | none => simpa [noMtSubprogsHOL,notCreatedSubprogsWithMemOp] using mt
                              | some h => obtain ⟨v,hprog,hl1,hl2⟩ := h; simp only [noMtSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] at mt ⊢; exact mt.1.2
                            have retNi : noInstallSubprogsHOL retHandler = true := by
                              cases handler with
                              | none => simpa [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp] using ni
                              | some h => obtain ⟨v,hprog,hl1,hl2⟩ := h; simp only [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] at ni ⊢; exact ni.1.2
                            have middleCode : middle.code = s.code := by
                              have h := code_evaluate prog entry progNi (hpre ▸ niCode)
                              rw [ev] at h
                              exact h.trans hpre
                            have restoredCode : restored.code = s.code := by
                              have h := popEnvConst middle restored hp
                              exact h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans middleCode
                            have hr := hreturn xs (args1,prog,ss) args1 (prog,ss) prog ss
                              (n,names,retHandler,l1,l2) n (names,retHandler,l1,l2) names
                              (retHandler,l1,l2) retHandler (l1,l2) l1 l2 envs
                              (some (.result x ys)) middle (.result x ys) x ys restored
                              ⟨hg,hbad,hf,rfl,rfl,rfl,rfl,rfl,rfl,rfl,hnames,he,hz,ev,rfl,rfl,hv,hp,hd⟩
                              K retMt retNi (by simpa [WordSemStateFiniteExact.setVars,restoredCode] using mtCode)
                              (by simpa [WordSemStateFiniteExact.setVars,restoredCode] using niCode) retLe
                              (by simpa [WordSemStateFiniteExact.setVars,restoredCode] using table)
                            rcases contRun : evaluate retHandler (setVars n ys restored) with ⟨out,post⟩
                            have contClock := (evaluate_clock retHandler _ out post contRun).1
                            change post.clock ≤ restored.clock at contClock
                            rw [hclock] at contClock
                            rw [contRun] at hr
                            change steps retHandler (setVars n ys restored) ≤
                              wordControlWeight retHandler + K * (restored.clock-post.clock) at hr
                            rw [hclock] at hr
                            have partition : s.clock-post.clock = (s.clock-1-middle.clock)+(middle.clock-post.clock)+1 := by omega
                            simp only [hv,if_false,hd,if_true,contRun]
                            rw [partition]
                            nlinarith
                          · simp only [hv,if_false,hd]
                            rw [hclock,spent]
                            nlinarith
                    case exception x y =>
                      cases handler with
                      | none => simp only; rw [spent]; nlinarith
                      | some h =>
                        obtain ⟨v,hprog,hl1,hl2⟩ := h
                        simp only
                        by_cases hx : x ≠ .loc hl1 hl2
                        · simp [hx]; rw [spent]; nlinarith
                        · by_cases hd : sptDomainEqUnion middle.locals envs.1 envs.2
                          · have handlerMt : noMtSubprogsHOL hprog = true := by
                              simp only [noMtSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] at mt ⊢
                              exact mt.2.2
                            have handlerNi : noInstallSubprogsHOL hprog = true := by
                              simp only [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] at ni ⊢
                              exact ni.2.2
                            have handlerWeight : 1 + wordControlWeight hprog ≤
                                wordControlWeight (.call (some (n,names,retHandler,l1,l2)) dest args (some (v,hprog,hl1,hl2))) := by
                              simp [wordControlWeight]
                            have handlerLe : wordControlWeight hprog ≤ K := by omega
                            have middleCode : middle.code = s.code := by
                              have h := code_evaluate prog entry progNi (hpre ▸ niCode)
                              rw [ev] at h
                              exact h.trans hpre
                            have hx' : x = .loc hl1 hl2 := by simpa using hx
                            have hh := hexception xs (args1,prog,ss) args1 (prog,ss) prog ss
                              (n,names,retHandler,l1,l2) n (names,retHandler,l1,l2) names
                              (retHandler,l1,l2) retHandler (l1,l2) l1 l2 envs
                              (some (.exception x y)) middle (.exception x y) x y
                              (v,hprog,hl1,hl2) v (hprog,hl1,hl2) hprog (hl1,hl2) hl1 hl2
                              ⟨hg,hbad,hf,rfl,rfl,rfl,rfl,rfl,rfl,rfl,hnames,he,hz,ev,rfl,rfl,rfl,rfl,rfl,rfl,hx',hd⟩
                              K handlerMt handlerNi (by simpa [WordSemStateFiniteExact.setVar,middleCode] using mtCode)
                              (by simpa [WordSemStateFiniteExact.setVar,middleCode] using niCode) handlerLe
                              (by simpa [WordSemStateFiniteExact.setVar,middleCode] using table)
                            rcases contRun : evaluate hprog (setVar v y middle) with ⟨out,post⟩
                            have contClock := (evaluate_clock hprog _ out post contRun).1
                            change post.clock ≤ middle.clock at contClock
                            rw [contRun] at hh
                            change steps hprog (setVar v y middle) ≤ wordControlWeight hprog + K * (middle.clock-post.clock) at hh
                            have partition : s.clock-post.clock = (s.clock-1-middle.clock)+(middle.clock-post.clock)+1 := by omega
                            simp only [hx,if_false,hd,if_true]
                            rw [partition]
                            nlinarith
                          · simp only [hx,if_false,hd]
                            rw [spent]
                            nlinarith

/-- An explicit bound on visits, computed from the program, its code table,
and its initial clock. -/
theorem wordTable_clock_bound (p : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F)
    (noMt : noMtSubprogsHOL p = true) (noInstall : noInstallSubprogsHOL p = true)
    (tableNoMt : WordProps.noMtCode s.code) (tableNoInstall : WordProps.noInstallCode s.code) :
    steps p s ≤ wordControlWeight p + max (wordControlWeight p) (wordCodeWeight s.code) * s.clock := by
  let K := max (wordControlWeight p) (wordCodeWeight s.code)
  have bound := wordTable_consumption_bound p s K noMt noInstall tableNoMt tableNoInstall
    (Nat.le_max_left _ _) (Nat.le_max_right _ _)
  have sub : s.clock - (evaluate p s).2.clock ≤ s.clock := Nat.sub_le _ _
  exact bound.trans (Nat.add_le_add_left (Nat.mul_le_mul_left K sub) _)


end SteppedFlapjack.WordSimpSteps
