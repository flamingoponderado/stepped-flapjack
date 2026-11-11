import SteppedFlapjack.WordToStackSteps.Loops
import SteppedFlapjack.WordSteps.CallSteps
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.NoMtCode
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.EvaluateAddClock
namespace SteppedFlapjack.WordSteps
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordToStackSteps
variable {width : Nat} [NeZero width] {C F : Type}

theorem const_consumption (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (h : wordProgClockConst p = true) : s.clock ≤ (evaluate p s).2.clock + steps p s := by
  rw [evaluate_const_clock s p h]
  omega

/-- In a call-free loop-fragment run, clock consumption is bounded by the
number of WordSem evaluator invocations, even when loops are nested. -/
theorem loopWord_consumption : ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F),
    loopWord p = true → s.clock ≤ (evaluate p s).2.clock + steps p s := by
  apply evaluate_ind (fun p s => loopWord p = true → s.clock ≤ (evaluate p s).2.clock + steps p s)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try { intros; apply const_consumption; rfl }
  case refine_11 =>
    intro s _
    have hs := steps_pos (.tick : WordLangProgHOL (BitVec width)) s
    rw [evaluate]
    split <;> simp only [flushState, decClock] <;> omega
  case refine_12 =>
    intro p s ih hp
    rw [evaluate]
    split
    · simp
    · split
      rename_i res t hrun
      cases res with
      | none => simp
      | some r => cases r <;> simp
  case refine_13 =>
    intro a b s ih hp
    simp only [loopWord, Bool.and_eq_true] at hp
    have ha := ih.2 hp.1
    rw [steps_seq]
    rw [evaluate, fix_clock_evaluate]
    rcases he : evaluate a s with ⟨res, t⟩
    cases res with
    | none =>
      have hb := ih.1 none t ⟨he.symm, rfl⟩ hp.2
      simp only [he] at ha
      simp only
      omega
    | some r =>
      simp only [he] at ha
      simp only
      omega
  case refine_18 =>
    intro cmp r ri a b s ih hp
    simp only [loopWord, Bool.and_eq_true] at hp
    rw [evaluate, steps_ite]
    cases hx : getVar r s with
    | none => simp
    | some x =>
      cases hy : getVarImm ri s with
      | none => simp
      | some y =>
        cases hv : wordSemWordCmp cmp x y with
        | none => simp [hv]
        | some v =>
          cases v with
          | false =>
            have hb := ih.2 (some x) (some y) x y false ⟨by simp [hx, hy], rfl, rfl, hv, by simp⟩ hp.2
            simp only [hv]
            omega
          | true =>
            have ha := ih.1 (some x) (some y) x y true ⟨by simp [hx, hy], rfl, rfl, hv, rfl⟩ hp.1
            simp only [hv]
            omega
  case refine_19 =>
    intro names body exitNames s ih hp
    simp only [loopWord] at hp
    rw [steps_loop, evaluate]
    cases hc : cutState (names, .ln) s with
    | none => simp
    | some u =>
      have hcut := cutState_clock_termdep _ _ _ hc
      have hb := ih.2 u hc hp
      simp only [fix_clock_evaluate]
      rcases he : evaluate body u with ⟨res, v⟩
      simp only [he] at hb
      by_cases hcont : wordSemContLoop res = true
      · by_cases hz : v.clock = 0
        · simp [hcont, hz, flushState]
          omega
        · have ht := ih.1 u res v ⟨hc, he.symm, hcont, hz⟩ hp
          dsimp only [wordSemSTOP, decClock] at ht
          simp [hcont, hz, wordSemSTOP, decClock]
          omega
      · simp only [hcont, Bool.false_eq_true, ↓reduceIte, false_and]
        cases res with
        | none => simp [wordSemContLoop] at hcont
        | some r =>
          cases r <;> simp only [wordSemExitLoop] <;> try omega
          case «break» k =>
            cases k with
            | zero =>
              cases hout : cutState (exitNames, .ln) v with
              | none => simp; omega
              | some w =>
                have hw := cutState_clock_termdep _ _ _ hout
                change s.clock ≤ w.clock + (1 + (steps body u + 0))
                omega
            | succ n => simp; omega
  case refine_26 =>
    intro ret dest args handler s ih hp
    simp only [loopWord, straightWord, Bool.false_eq_true] at hp
/-- The consumed clock, expressed with natural subtraction, is at most the
actual source step count. -/
theorem loopWord_consumed_le_steps (p : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) (fragment : loopWord p = true) :
    s.clock - (evaluate p s).2.clock ≤ steps p s := by
  have h := loopWord_consumption p s fragment
  omega


/-- In a Word execution whose program and function table contain neither
MustTerminate nor code installation, clock consumption is at most the number
of evaluator visits. This includes ordinary calls, tail calls, exceptions,
loops, and their continuations. -/
theorem table_consumption : ∀ (p : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F),
    noMtSubprogsHOL p = true → noInstallSubprogsHOL p = true →
    WordProps.noMtCode s.code → WordProps.noInstallCode s.code →
    s.clock ≤ (evaluate p s).2.clock + steps p s := by
  apply evaluate_ind (fun p s => noMtSubprogsHOL p = true → noInstallSubprogsHOL p = true →
    WordProps.noMtCode s.code → WordProps.noInstallCode s.code →
    s.clock ≤ (evaluate p s).2.clock + steps p s)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try { intros; apply const_consumption; rfl }
  case refine_11 =>
    intro s _ _ _ _
    have hs := steps_pos (.tick : WordLangProgHOL (BitVec width)) s
    rw [evaluate]
    split <;> simp only [flushState, decClock] <;> omega
  case refine_12 =>
    intro p s ih mt
    simp [noMtSubprogsHOL,notCreatedSubprogsWithMemOp] at mt
  case refine_13 =>
    intro a b s ih mt ni mtCode niCode
    simp only [noMtSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] at mt
    simp only [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] at ni
    have ha := ih.2 mt.1 ni.1 mtCode niCode
    have code := code_evaluate a s ni.1 niCode
    rw [steps_seq, evaluate, fix_clock_evaluate]
    rcases he : evaluate a s with ⟨res,t⟩
    rw [he] at code
    simp only at code
    cases res with
    | none =>
      have hb := ih.1 none t ⟨he.symm,rfl⟩ mt.2 ni.2
        (by simpa only [code] using mtCode) (by simpa only [code] using niCode)
      simp only [he] at ha
      simp only
      omega
    | some r =>
      simp only [he] at ha
      simp only
      omega
  case refine_18 =>
    intro cmp r ri a b s ih mt ni mtCode niCode
    simp only [noMtSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] at mt
    simp only [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] at ni
    rw [evaluate, steps_ite]
    cases hx : getVar r s with
    | none => simp
    | some x =>
      cases hy : getVarImm ri s with
      | none => simp
      | some y =>
        cases hv : wordSemWordCmp cmp x y with
        | none => simp [hv]
        | some v =>
          cases v with
          | false =>
            have hb := ih.2 (some x) (some y) x y false ⟨by simp [hx, hy], rfl, rfl, hv, by simp⟩ mt.2 ni.2 mtCode niCode
            simp only [hv]
            omega
          | true =>
            have ha := ih.1 (some x) (some y) x y true ⟨by simp [hx, hy], rfl, rfl, hv, rfl⟩ mt.1 ni.1 mtCode niCode
            simp only [hv]
            omega
  case refine_19 =>
    intro names body exitNames s ih mt ni mtCode niCode
    have mtBody : noMtSubprogsHOL body = true := by simpa [noMtSubprogsHOL,notCreatedSubprogsWithMemOp] using mt
    have niBody : noInstallSubprogsHOL body = true := by simpa [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp] using ni
    rw [steps_loop, evaluate]
    cases hc : cutState (names, .ln) s with
    | none => simp
    | some u =>
      have ucode : u.code = s.code := by obtain ⟨l,rfl⟩ := cutStateConst _ _ _ hc; rfl
      have hcut := cutState_clock_termdep _ _ _ hc
      have uMt : WordProps.noMtCode u.code := by simpa only [ucode] using mtCode
      have uNi : WordProps.noInstallCode u.code := by simpa only [ucode] using niCode
      have hb := ih.2 u hc mtBody niBody uMt uNi
      have hcode := code_evaluate body u niBody uNi
      simp only [fix_clock_evaluate]
      rcases he : evaluate body u with ⟨res, v⟩
      rw [he] at hcode
      simp only at hcode
      simp only [he] at hb
      by_cases hcont : wordSemContLoop res = true
      · by_cases hz : v.clock = 0
        · simp [hcont, hz, flushState]
          omega
        · have vMt : WordProps.noMtCode v.code := by simpa only [hcode] using uMt
          have vNi : WordProps.noInstallCode v.code := by simpa only [hcode] using uNi
          have ht := ih.1 u res v ⟨hc, he.symm, hcont, hz⟩ mt ni vMt vNi
          dsimp only [wordSemSTOP, decClock] at ht
          simp [hcont, hz, wordSemSTOP, decClock]
          omega
      · simp only [hcont, Bool.false_eq_true, ↓reduceIte, false_and]
        cases res with
        | none => simp [wordSemContLoop] at hcont
        | some r =>
          cases r <;> simp only [wordSemExitLoop] <;> try omega
          case «break» k =>
            cases k with
            | zero =>
              cases hout : cutState (exitNames, .ln) v with
              | none => simp; omega
              | some w =>
                have hw := cutState_clock_termdep _ _ _ hout
                change s.clock ≤ w.clock + (1 + (steps body u + 0))
                omega
            | succ n => simp; omega
  case refine_26 =>
    intro ret dest args handler s ih mt ni mtCode niCode
    rcases ih with ⟨hreturn, hexception, hcallee, htail⟩
    cases hg : getVars args s with
    | none => simp [evaluate, steps.eq_def, hg]
    | some xs =>
      by_cases hbad : wordSemBadDestArgs dest args = true
      · simp [evaluate, steps.eq_def, hg, hbad]
      · cases hf : wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with
        | none => simp [evaluate, steps.eq_def, hg, hbad, hf]
        | some triple =>
          obtain ⟨args1, prog, ss⟩ := triple
          obtain ⟨k,n,lookup⟩ := WordProps.findCode_lookup s.code dest _ _ _ prog _ hf
          have progMt := mtCode k n prog lookup
          have progNi := niCode k n prog lookup
          cases ret with
          | none =>
            cases handler with
            | some handler => simp [evaluate, steps.eq_def, hg, hbad, hf]
            | none =>
              by_cases hz : s.clock = 0
              · simp [evaluate, steps.eq_def, hg, hbad, hf, hz, flushState]
              · have ht := htail xs (args1,prog,ss) args1 (prog,ss) prog ss
                  ⟨hg,hbad,hf,rfl,rfl,rfl,rfl,hz⟩ progMt progNi mtCode niCode
                rw [evaluate, steps.eq_def]
                simp only [hg, hbad, Bool.false_eq_true, ↓reduceIte, hf, hz]
                simp only [dif_pos (tailCallMeasure dest args s args1 ss prog hz)]
                change s.clock - 1 ≤ (evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (decClock s))).2.clock +
                  steps prog (WordSemStateFiniteExact.callEnv args1 ss (decClock s)) at ht
                simp only [↓reduceDIte]
                split_ifs <;> simp_all only <;> omega
          | some ret =>
            obtain ⟨n, names, retHandler, l1, l2⟩ := ret
            by_cases hnames : sptDomainEmpty names.1 ∨ ¬ n.Nodup
            · simp [evaluate, steps.eq_def, hg, hbad, hf, hnames]
            · cases he : wordSemCutEnvs names s.locals with
              | none => simp [evaluate, steps.eq_def, hg, hbad, hf, hnames, he]
              | some envs =>
                by_cases hz : s.clock = 0
                · simp [evaluate, steps.eq_def, hg, hbad, hf, hnames, he, hz,flushState]
                · have hpre : (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))).code = s.code :=
                    code_pushEnv envs handler _
                  have hc := hcallee xs (args1,prog,ss) args1 (prog,ss) prog ss
                    (n,names,retHandler,l1,l2) n (names,retHandler,l1,l2) names
                    (retHandler,l1,l2) retHandler (l1,l2) l1 l2 envs
                    ⟨hg,hbad,hf,rfl,rfl,rfl,rfl,rfl,rfl,rfl,hnames,he,hz⟩
                      progMt progNi (hpre ▸ mtCode) (hpre ▸ niCode)
                  let entry := WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))
                  rcases ev : evaluate prog entry with ⟨result,middle⟩
                  have hc' := hc
                  change entry.clock ≤ (evaluate prog entry).2.clock + steps prog entry at hc'
                  have entryClock : entry.clock = s.clock-1 := by simp [entry,WordSemStateFiniteExact.callEnv,pushEnv_clock,decClock]
                  rw [entryClock,ev] at hc'
                  dsimp only [entry] at hc'
                  have badFalse : wordSemBadDestArgs dest args = false := by cases h : wordSemBadDestArgs dest args <;> simp_all only [Bool.false_eq_true, not_false_eq_true, not_true_eq_false]
                  rw [steps_call_returning dest args n names retHandler l1 l2 handler s middle result xs args1 ss prog envs hg badFalse hf hnames he hz ev]
                  have hcall := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                  rw [hcall]
                  simp only [hg,hbad,hf,hnames,he,hz, ↓reduceIte]
                  change evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))) = (result,middle) at ev
                  simp only [Bool.false_eq_true,↓reduceIte,ev]
                  cases result with
                  | none => simp only; omega
                  | some result =>
                    cases result <;> simp only <;> try omega
                    case result x ys =>
                      by_cases hv : x ≠ .loc l1 l2 ∨ ys.length ≠ n.length
                      · simp only [hv,if_true]; omega
                      · cases hp : popEnv middle with
                        | none => simp only [hv,if_false]; omega
                        | some restored =>
                          have hclock := popEnv_clock middle restored hp
                          by_cases hd : sptDomainEqUnion restored.locals envs.1 envs.2
                          · have retMt : noMtSubprogsHOL retHandler = true := by
                              cases handler with
                              | none => simpa [noMtSubprogsHOL,notCreatedSubprogsWithMemOp] using mt
                              | some h =>
                                obtain ⟨v,hprog,hl1,hl2⟩ := h
                                simp only [noMtSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] at mt ⊢
                                exact mt.1.2
                            have retNi : noInstallSubprogsHOL retHandler = true := by
                              cases handler with
                              | none => simpa [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp] using ni
                              | some h =>
                                obtain ⟨v,hprog,hl1,hl2⟩ := h
                                simp only [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] at ni ⊢
                                exact ni.1.2
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
                              retMt retNi (by simpa [WordSemStateFiniteExact.setVars,restoredCode] using mtCode)
                              (by simpa [WordSemStateFiniteExact.setVars,restoredCode] using niCode)
                            change restored.clock ≤ (evaluate retHandler (setVars n ys restored)).2.clock +
                              steps retHandler (setVars n ys restored) at hr
                            rw [hclock] at hr
                            simp only [hv,if_false,hd,if_true]
                            omega
                          · simp only [hv,if_false,hd]; omega
                    case exception x y =>
                      cases handler with
                      | none => simp only; omega
                      | some h =>
                        obtain ⟨v,hprog,hl1,hl2⟩ := h
                        simp only
                        by_cases hx : x ≠ .loc hl1 hl2
                        · simp [hx]
                          omega
                        · by_cases hd : sptDomainEqUnion middle.locals envs.1 envs.2
                          · have handlerMt : noMtSubprogsHOL hprog = true := by
                              simp only [noMtSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] at mt ⊢
                              exact mt.2.2
                            have handlerNi : noInstallSubprogsHOL hprog = true := by
                              simp only [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true] at ni ⊢
                              exact ni.2.2
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
                              handlerMt handlerNi (by simpa [WordSemStateFiniteExact.setVar,middleCode] using mtCode)
                              (by simpa [WordSemStateFiniteExact.setVar,middleCode] using niCode)
                            change middle.clock ≤ (evaluate hprog (setVar v y middle)).2.clock +
                              steps hprog (setVar v y middle) at hh
                            simp only [hx,if_false,hd,if_true]
                            omega
                          · simp only [hx,if_false,hd]; omega

end SteppedFlapjack.WordSteps
