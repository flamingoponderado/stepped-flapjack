import SteppedFlapjack.WordToStackSteps.BudgetSimulation
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.ShareInst
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.ShareInst
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
private theorem shareLoad_one {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame : Nat} {op : WordMemOp} {v ad : Nat}
    {offset : BitVec width} {s s1 : WordSemStateFiniteExact width (Nat × C) F}
    {t : StackSemStateFiniteExact width C F} {lens : List Nat}
    {res : Option (WordSemResult width)} :
    WordSemStateFiniteExact.evaluate
        (.shareInst op (2 * v) (.op .add [.var (2 * ad), .const offset])) s = (res, s1) ∧
      res ≠ some .error ∧ stateRel ac k f frame s t lens 0 ∧ v < frame + k ∧ ad < frame + k ∧
      (op = .load ∨ op = .load8 ∨ op = .load16 ∨ op = .load32) →
    ∃ t1,
      StackSemEvaluate.evaluate
          (wShareInstNative op (2 * v) (.addr (2 * ad) offset) (k, f, frame),
            { t with clock := 1 + t.clock }) = (res.map compileResult, t1) ∧
      ((∃ fv, res = some (.finalFfi fv) ∧ s1.ffi = t1.ffi ∧ s1.clock = t1.clock) ∨
        (res = none ∧ stateRel ac k f frame s1 t1 lens 0)) := by
  rintro ⟨hrun, notError, related, hv, had, hop⟩
  obtain ⟨x, hx, hshare⟩ := shareInstSource hrun notError
  rcases fmt : Compiler.Backend.WordToStackRegFormat.wReg1 (2 * ad) (k, f, frame) with ⟨xs, reg⟩
  obtain ⟨t1, run1, clock1, rel1, len1, sp1, -, -, -, loaded⟩ :=
    LoadRegister.evaluateWStackLoadWReg1 ac k f frame (2 * ad) reg xs s t lens (.word x) fmt
      (by omega) hx related
  have hloads : StackSemEvaluate.evaluate (wStackLoadNative xs .skip,
      { t with clock := 1 + t.clock }) = (none, { t1 with clock := 1 + t.clock }) := by
    rw [LoadRegisterClock.evaluateWStackLoadClock, run1]; rfl
  have hfix : StackSemControl.fixClock { t with clock := 1 + t.clock }
      ((none : Option (StackSemResult width)), { t1 with clock := 1 + t.clock }) =
      (none, { t1 with clock := 1 + t.clock }) := by
    simp [StackSemControl.fixClock]
  have hdec : StackSemStateOps.decClock { t1 with clock := 1 + t.clock } = t1 := by
    simp only [StackSemStateOps.decClock, clock1]
    congr 1
    omega
  have haddr : StackSemExpressions.wordExp { t1 with clock := 1 + t.clock }
      (.op .add [.var reg, .const offset]) = some (x + offset) :=
    stackAddr (t := { t1 with clock := 1 + t.clock }) loaded
  rcases hop with rfl | rfl | rfl | rfl <;>
    simp only [wShareInstNative, fmt] <;>
    rw [LoadRegister.evaluateWStackLoadSeq, StackSemEvaluate.evaluate_seq, hloads, hfix] <;>
    simp only [wRegWrite1Native, show 2 * v / 2 = v by omega]
  all_goals
    split
    · rename_i hlt
      rw [StackSemEvaluate.evaluate_shMemOp, haddr]
      simp only [show ¬ (1 + t.clock = 0) by omega, if_false, hdec]
      exact shareLoadLemma2 ⟨hshare, rel1, hlt, by simp, notError⟩
    · rename_i hge
      rw [StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_shMemOp, haddr]
      simp only [show ¬ (1 + t.clock = 0) by omega, if_false, hdec]
      obtain ⟨t2, h2, hc⟩ := shareLoadLemma1 ⟨hshare, rel1, hv, by omega, by simp, notError⟩
      have hclk : t2.clock = t.clock := by
        have hc' := congrArg (fun p => p.2.clock) h2
        simp only [shMemOp_clock] at hc'
        omega
      have hmin : min (1 + t.clock) t2.clock = t2.clock := by omega
      rw [h2]
      have hfix2 : ∀ r : Option (StackSemResult width), StackSemControl.fixClock
          { t1 with clock := 1 + t.clock } (r, t2) = (r, t2) := by
        intro r
        show (r, { t2 with clock := min (1 + t.clock) t2.clock }) = (r, t2)
        rw [hmin]
      rw [hfix2]
      have related' := related
      unfold stateRel at related'
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
        -, -, -, -, -, r33, -, r35, -⟩ := related'
      rcases hc with ⟨fv, rfl, hffi, hcl⟩ | ⟨rfl, hrel, ⟨xv, hxv⟩, hsp, hlen⟩
      · exact ⟨t2, rfl, .inl ⟨fv, rfl, hffi, hcl⟩⟩
      · have huse : t2.useStack = true := by
          have hrel' := hrel
          unfold stateRel at hrel'
          exact hrel'.2.2.2.2.1
        have hf : f = frame + 1 := by split at r35 <;> omega
        have hidx : f - 1 - (v - k) = f + k - (v + 1) := by omega
        refine ⟨_, ?_, .inr ⟨rfl, hrel⟩⟩
        simp only [Option.map_none]
        rw [StackSemEvaluate.evaluate_stackStore]
        simp only [huse, Bool.not_true, Bool.false_eq_true, if_false,
          StackSemStateOps.getVar, hxv, hidx, Flapjack.holThe]
        rw [if_neg (by omega)]


private theorem shareStore_one {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame : Nat} {op : WordMemOp} {v ad : Nat}
    {offset : BitVec width} {s s1 : WordSemStateFiniteExact width (Nat × C) F}
    {t : StackSemStateFiniteExact width C F} {lens : List Nat}
    {res : Option (WordSemResult width)} :
    WordSemStateFiniteExact.evaluate
        (.shareInst op (2 * v) (.op .add [.var (2 * ad), .const offset])) s = (res, s1) ∧
      stateRel ac k f frame s t lens 0 ∧ v < frame + k ∧ ad < frame + k ∧
      res ≠ some .error ∧ (op = .store ∨ op = .store8 ∨ op = .store16 ∨ op = .store32) →
    ∃ t1,
      StackSemEvaluate.evaluate
          (wShareInstNative op (2 * v) (.addr (2 * ad) offset) (k, f, frame),
            { t with clock := 1 + t.clock }) = (res.map compileResult, t1) ∧
      ((∃ fv, res = some (.finalFfi fv) ∧ s1.ffi = t1.ffi ∧ s1.clock = t1.clock) ∨
        (res = none ∧ stateRel ac k f frame s1 t1 lens 0)) := by
  rintro ⟨hrun, related, hv, had, notError, hop⟩
  obtain ⟨x, hx, hshare⟩ := shareInstSource hrun notError
  -- The stored source word.
  have hw : ∃ w, WordSemStateFiniteExact.getVar (2 * v) s = some (.word w) := by
    rcases hg : WordSemStateFiniteExact.getVar (2 * v) s with _ | (w | ⟨p, q⟩)
    all_goals first
      | exact ⟨w, rfl⟩
      | (rcases hop with rfl | rfl | rfl | rfl <;>
          simp only [WordSemStateFiniteExact.shareInst, hg, Prod.mk.injEq] at hshare <;>
          exact absurd hshare.1.symm notError)
  obtain ⟨w, hw⟩ := hw
  rcases fmt1 : Compiler.Backend.WordToStackRegFormat.wReg1 (2 * ad) (k, f, frame) with
    ⟨xs, reg1⟩
  rcases fmt2 : Compiler.Backend.WordToStackRegFormat.wReg2 (2 * v) (k, f, frame) with
    ⟨ys, reg2⟩
  obtain ⟨t1, run1, clock1, rel1, -, -, -, -, regNe, loaded1⟩ :=
    LoadRegister.evaluateWStackLoadWReg1 ac k f frame (2 * ad) reg1 xs s t lens (.word x) fmt1
      (by omega) hx related
  obtain ⟨t2, run2, clock2, -, rel2, -, -, otherReads, -, loaded2⟩ :=
    LoadRegisterTwo.evaluateWStackLoadWReg2 ac k f frame (2 * v) reg2 ys s t1 lens (.word w) fmt2
      (by omega) hw rel1
  have hl1 : StackSemEvaluate.evaluate (wStackLoadNative xs .skip,
      { t with clock := 1 + t.clock }) = (none, { t1 with clock := 1 + t.clock }) := by
    rw [LoadRegisterClock.evaluateWStackLoadClock, run1]; rfl
  have hl2 : StackSemEvaluate.evaluate (wStackLoadNative ys .skip,
      { t1 with clock := 1 + t.clock }) = (none, { t2 with clock := 1 + t.clock }) := by
    rw [LoadRegisterClock.evaluateWStackLoadClock, run2]; rfl
  have hfix : ∀ (u u' : StackSemStateFiniteExact width C F), StackSemControl.fixClock
      { u with clock := 1 + t.clock }
      ((none : Option (StackSemResult width)), { u' with clock := 1 + t.clock }) =
      (none, { u' with clock := 1 + t.clock }) := by
    intro u u'; simp [StackSemControl.fixClock]
  have hdec : StackSemStateOps.decClock { t2 with clock := 1 + t.clock } = t2 := by
    simp only [StackSemStateOps.decClock]
    congr 1
    omega
  have read1 : StackSemStateOps.getVar reg1 t2 = some (.word x) := by
    rw [otherReads reg1 regNe]; exact loaded1
  have haddr : StackSemExpressions.wordExp { t2 with clock := 1 + t.clock }
      (.op .add [.var reg1, .const offset]) = some (x + offset) :=
    stackAddr (t := { t2 with clock := 1 + t.clock }) read1
  rcases hop with rfl | rfl | rfl | rfl <;>
    simp only [wShareInstNative, fmt1, fmt2, wStackLoadAppend, Function.comp_apply] <;>
    rw [LoadRegister.evaluateWStackLoadSeq, StackSemEvaluate.evaluate_seq, hl1, hfix] <;>
    dsimp only <;>
    rw [LoadRegister.evaluateWStackLoadSeq, StackSemEvaluate.evaluate_seq, hl2, hfix] <;>
    dsimp only <;>
    rw [StackSemEvaluate.evaluate_shMemOp, haddr] <;>
    simp only [show ¬ (1 + t.clock = 0) by omega, if_false, hdec] <;>
    exact shareStoreGeneric hshare rel2 hw loaded2 (by simp) notError



private theorem shareCorrect_one {width : Nat} [NeZero width] {C F : Type}
    {ac : AsmConfigExact width} {k f frame : Nat} {op : WordMemOp} {v ad : Nat}
    {offset : BitVec width} {s s1 : WordSemStateFiniteExact width (Nat × C) F}
    {t : StackSemStateFiniteExact width C F} {lens : List Nat}
    {res : Option (WordSemResult width)} :
    WordSemStateFiniteExact.evaluate
        (.shareInst op (2 * v) (.op .add [.var (2 * ad), .const offset])) s = (res, s1) ∧
      res ≠ some .error ∧ stateRel ac k f frame s t lens 0 ∧ v < frame + k ∧ ad < frame + k →
    ∃ t1,
      StackSemEvaluate.evaluate
          (wShareInstNative op (2 * v) (.addr (2 * ad) offset) (k, f, frame),
            { t with clock := 1 + t.clock }) = (res.map compileResult, t1) ∧
      ((res = none ∧ stateRel ac k f frame s1 t1 lens 0) ∨
        (∃ fv, res = some (.finalFfi fv) ∧ s1.ffi = t1.ffi ∧ s1.clock = t1.clock)) := by
  rintro ⟨hrun, notError, related, hv, had⟩
  cases op
  case load | load8 | load16 | load32 =>
    obtain ⟨t1, run, result⟩ := shareLoad_one ⟨hrun, notError, related, hv, had, by simp⟩
    exact ⟨t1,run,result.symm⟩
  case store | store8 | store16 | store32 =>
    obtain ⟨t1, run, result⟩ := shareStore_one ⟨hrun, related, hv, had, notError, by simp⟩
    exact ⟨t1,run,result.symm⟩


private theorem shareInst_oneClock {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (op : WordMemOp) (v : Nat) (exp : WordLangExpHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    ∀ (k f frame : Nat) (sourcePost : WordSemStateFiniteExact width (Nat × C) F)
      (target : StackSemStateFiniteExact width C F) (result : Option (WordSemResult width))
      (bs bsPost : AppList (BitVec width)) (n nPost : Nat) (compiled : HolProg width) (lens : List Nat),
      (WordSemStateFiniteExact.evaluate (.shareInst op v exp) source = (result, sourcePost) ∧
        result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
        postAllocConventionsHOL k ((.shareInst op v exp) : WordLangProgHOL (BitVec width)) = true ∧ flatExpConventions ((.shareInst op v exp) : WordLangProgHOL (BitVec width)) = true ∧
        compNative ac false (.shareInst op v exp) (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
        (appListAppend bs).length ≤ n ∧ n - (appListAppend bs).length ≤ target.bitmaps.length ∧
        List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
        (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
        maxVarHOL ((.shareInst op v exp) : WordLangProgHOL (BitVec width)) < 2 * frame + 2 * k) →
      ∃ targetPost,
        StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + 1}) = (result.map compileResult,targetPost) ∧
        compCorrectResult ac k f frame source sourcePost targetPost result (result.map compileResult) lens := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  obtain ⟨execution, notError, related, conventions, flat, compilation, -, -, -, -,
    maxBound⟩ := premises
  rcases flatExpConventionsShareInstExpSimp flat with ⟨ad, rfl⟩ | ⟨ad, offset, rfl⟩
  all_goals
    simp [postAllocConventionsHOL, everyVarHOL, everyVarExpHOL, everyVarExpsHOL,
      everyStackVarHOL, callArgConventionHOL, isPhyVar] at conventions
    simp [maxVarHOL, maxVarExpHOL, maxList] at maxBound
    simp only [compNative, expToAddrHOL, Prod.mk.injEq] at compilation
    obtain ⟨rfl, -, -⟩ := compilation
  case inl =>
    rw [evaluateShareInstVarEqOpAdd] at execution
    obtain ⟨v', rfl⟩ : ∃ v', v = 2 * v' := ⟨v / 2, by omega⟩
    obtain ⟨a', rfl⟩ : ∃ a', ad = 2 * a' := ⟨ad / 2, by omega⟩
    obtain ⟨t1, h, hc⟩ :=
      shareCorrect_one ⟨execution, notError, related, by omega, by omega⟩
    refine ⟨t1, ?_, ?_⟩
    · simpa [Nat.add_comm, HolAddr.ofWordLangAddr] using h
    · rcases hc with ⟨rfl, hr⟩ | ⟨fv, rfl, hffi, hclk⟩
      · simpa [compCorrectResult] using hr
      · simp [compCorrectResult, hffi, hclk]
  case inr =>
    obtain ⟨v', rfl⟩ : ∃ v', v = 2 * v' := ⟨v / 2, by omega⟩
    obtain ⟨a', rfl⟩ : ∃ a', ad = 2 * a' := ⟨ad / 2, by omega⟩
    obtain ⟨t1, h, hc⟩ :=
      shareCorrect_one ⟨execution, notError, related, by omega, by omega⟩
    refine ⟨t1, ?_, ?_⟩
    · simpa [Nat.add_comm, HolAddr.ofWordLangAddr] using h
    · rcases hc with ⟨rfl, hr⟩ | ⟨fv, rfl, hffi, hclk⟩
      · simpa [compCorrectResult] using hr
      · simp [compCorrectResult, hffi, hclk]

/-- Shared-memory instructions have a one-clock simulation budget. -/
theorem shareInst_budget {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (op : WordMemOp) (v : Nat) (exp : WordLangExpHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    BudgetSimulation ac (.shareInst op v exp) source 1 := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises reserve
  obtain ⟨sourceRun,notError,notTimeout,rest⟩ := premises
  obtain ⟨post,run,relation⟩ := shareInst_oneClock ac op v exp source k f frame sourcePost target result
    bs bsPost n nPost compiled lens ⟨sourceRun,notError,rest⟩
  have outNotTimeout : result.map compileResult ≠ some .timeOut := by
    cases result with
    | none => simp
    | some r => cases r <;> simp_all [compileResult]
  have boosted := Compiler.Backend.StackProps.evaluateAddClock reserve compiled {target with clock := target.clock+1}
    (result.map compileResult) post ⟨run,outNotTimeout⟩
  refine ⟨{post with clock := post.clock+reserve},result.map compileResult,by simpa using boosted,by simp,?_,?_⟩
  · by_cases limit : result.map compileResult = some (.halt (.word 2))
    · exact Or.inl limit
    · have clocks := compCorrectResult_clocks ac k f frame source sourcePost post result
        (result.map compileResult) lens relation limit
      right; constructor <;> simp only <;> omega
  · simpa using compCorrectResult_setClocks ac k f frame source sourcePost post result
      (result.map compileResult) lens sourcePost.clock relation

end SteppedFlapjack.WordToStackSteps
