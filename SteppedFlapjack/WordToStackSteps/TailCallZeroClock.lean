import SteppedFlapjack.WordToStackSteps.LoopZeroClock
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallTail

/-! Zero-extra-clock tail-call simulation. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallTail
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

theorem zeroCallTail {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (ih : ∀ (xs : List (WordLocW width)) (args1 : List (WordLocW width))
        (prog : WordLangProgHOL (BitVec width)) (ss : Option Nat),
      WordSemStateFiniteExact.getVars args source = some xs ∧
        ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat)) xs) source.code source.stackSize =
          some (args1, prog, ss) ∧
        handler = none ∧ source.clock ≠ 0 →
      ZeroSimulation ac prog
        (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.decClock source)))
    : ZeroSimulation ac (.call none dest args handler) source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  obtain ⟨execution, notError, related, conventions, flat, compilation, hbsn, hbsl, hpre,
    labels, maxVar⟩ := premises
  simp only [compNative] at compilation
  rcases hcd : callDestNative (width := width) dest args (k, f, frame) with ⟨q0, dest'⟩
  rw [hcd] at compilation
  simp only [Prod.mk.injEq] at compilation
  obtain ⟨rfl, rfl, rfl⟩ := compilation
  -- the source run
  rw [WordSemStateFiniteExact.evaluate] at execution
  rcases hgv : WordSemStateFiniteExact.getVars args source with _ | xs
  · simp only [hgv, Prod.mk.injEq] at execution; exact absurd execution.1.symm notError
  simp only [hgv] at execution
  by_cases hbad : wordSemBadDestArgs dest args = true
  · simp only [hbad, if_true, Prod.mk.injEq] at execution
    exact absurd execution.1.symm notError
  simp only [hbad, Bool.false_eq_true, if_false] at execution
  rcases hfc : wordSemFindCode dest (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat)) xs) source.code source.stackSize with
    _ | ⟨args1, prog, ss⟩
  · simp only [hfc, Prod.mk.injEq] at execution; exact absurd execution.1.symm notError
  simp only [hfc] at execution
  rcases handler with _ | hnd
  swap
  · simp only [Prod.mk.injEq] at execution; exact absurd execution.1.symm notError
  simp only at execution
  -- the compiled destination finds the compiled callee
  obtain ⟨t4, hev4, hrel4, hlen4, hsp4, hcode⟩ :=
    CallDest.callDestLemma ac k f frame dest args source target lens q0 dest' xs none
      ⟨hbad, related, hcd, hgv⟩
  obtain ⟨bs0, i0, bs2, i2, fs, stackProg, hcomp, hb1, hb2, hb3, hss, hfind⟩ :=
    hcode args1 prog ss hfc
  have hrel4' := hrel4
  unfold stateRel at hrel4'
  obtain ⟨r1, -, r3, r4, r5, -, -, -, -, r10, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    r28, -, -, -, -, r33, -, r35, -, r37, r38, rloc⟩ := hrel4'
  -- argument conventions and the frame bound on the arguments
  have hargs : args = (List.range args.length).map (fun x => 2 * x) := by
    simp only [postAllocConventionsHOL, callArgConventionHOL, Bool.and_eq_true,
      beq_iff_eq] at conventions
    exact conventions.2.2
  have hxslen : xs.length = args.length :=
    WordSemStateFiniteExact.getVarsLengthLemma args source xs hgv
  have hargbound : ∀ i, i < args.length → i < frame + k := by
    intro i hi
    have hmem : 2 * i ∈ args := by
      rw [hargs]; exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
    have := maxList_ge_of_mem args (2 * i) hmem
    simp only [maxVarHOL] at maxVar
    omega
  -- the freed caller frame keeps exactly the callee's stack arguments
  set sac := Compiler.Backend.WordToStack.stackArgCount dest' args.length k with hsac
  have hlenb : args.length ≤ frame + k := by
    rcases Nat.eq_zero_or_pos args.length with h | h
    · omega
    · have := hargbound (args.length - 1) (by omega); omega
  have hsacf : sac ≤ f := by
    have : sac ≤ args.length - k := by
      simp only [hsac, Compiler.Backend.WordToStack.stackArgCount]; split <;> omega
    by_cases h0 : frame = 0
    · rw [if_pos h0] at r35; omega
    · rw [if_neg h0] at r35; omega
  obtain ⟨pLoc, hpLoc, hssLoc, hnone, hsome⟩ :=
    findCode_facts dest _ source.code source.stackSize args1 prog ss hfc
  have hsac1 : sac = args1.length - k := by
    rcases dest with _ | p
    · have hne : args ≠ [] := by rintro rfl; simp [wordSemBadDestArgs] at hbad
      have hlen0 : ¬ args.length = 0 := by simpa using hne
      simp only [callDestNative, dif_neg hlen0, Prod.mk.injEq] at hcd
      obtain ⟨-, rfl⟩ := hcd
      rw [hnone rfl]
      simp only [hsac, Compiler.Backend.WordToStack.stackArgCount, wordSemAddRetLoc,
        List.length_dropLast, hxslen]
    · simp only [callDestNative, Prod.mk.injEq] at hcd
      obtain ⟨-, rfl⟩ := hcd
      rw [hsome (by simp)]
      simp only [hsac, Compiler.Backend.WordToStack.stackArgCount, wordSemAddRetLoc, hxslen]
  have huse4 : t4.useStack = true := r5
  have hfree : t4.stackSpace + Compiler.Backend.WordToStack.stackFree dest' args.length k f frame ≤
      t4.stack.length := by
    simp only [Compiler.Backend.WordToStack.stackFree]
    omega
  have hcall : ∀ extra : Nat,
      StackSemEvaluate.evaluate
          (Compiler.Backend.StackLang.Prog.seq q0
            (seqStackFreeNative (Compiler.Backend.WordToStack.stackFree dest' args.length k f frame)
              (Compiler.Backend.StackLang.Prog.call none dest' none)),
            {target with clock := target.clock + extra}) =
        StackSemEvaluate.evaluate (Compiler.Backend.StackLang.Prog.call none dest' none,
          {t4 with
            stackSpace := t4.stackSpace +
              Compiler.Backend.WordToStack.stackFree dest' args.length k f frame
            clock := t4.clock + extra}) := by
    intro extra
    have hev4' := Compiler.Backend.StackProps.evaluateAddClock extra q0 target none t4
      ⟨hev4, by simp⟩
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, hev4']
    simp only
    rw [CallHelpers.evaluateSeqStackFree _ _ {t4 with clock := t4.clock + extra}
        ⟨huse4, by simp only; omega⟩, StackSemEvaluate.evaluate_seq,
      StackSemEvaluate.evaluate_stackFree, if_neg (by simp [huse4]), if_neg (by simp; omega)]
    simp only [StackSemControl.fixClock, Nat.min_self]
  by_cases hclk : source.clock = 0
  · -- the clock runs out at the call
    rw [dif_pos hclk] at execution
    simp only [Prod.mk.injEq] at execution
    obtain ⟨rfl, rfl⟩ := execution
    have hrun := hcall 0
    rw [StackSemEvaluate.evaluate_call] at hrun
    simp only [hfind, Nat.add_zero, r1.symm.trans hclk, if_true] at hrun
    refine ⟨_, _, by simpa using hrun, ?_⟩
    · unfold compCorrectResult
      simp only [Option.map_some, compileResult, ne_eq, not_true_eq_false, if_false]
      exact ⟨r4.symm, hclk⟩
  · rw [dif_neg hclk] at execution
    rcases hbody : WordSemStateFiniteExact.evaluate prog
        (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.decClock source)) with
      ⟨res', s'⟩
    rw [hbody] at execution
    by_cases hbf : wordSemBadFunReturn res' = true
    · simp only [hbf, if_true, Prod.mk.injEq] at execution
      exact absurd execution.1.symm notError
    simp only [hbf, Bool.false_eq_true, if_false, Prod.mk.injEq] at execution
    obtain ⟨rfl, rfl⟩ := execution
    -- the compiled callee: a frame allocation followed by the compiled body
    have hsacfs : args1.length - k ≤ fs := CallHelpers.compileProgStackSize _ _ _ _ _ _ _ _ _ hcomp
    simp only [compileProgNative] at hcomp
    set svc := max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) with hsvc
    rcases hbc : compNative ac false prog (bs0, i0)
        (k, if svc = 0 then 0 else svc + 1, svc) with ⟨body, bsb⟩
    rw [hbc] at hcomp
    simp only [Prod.mk.injEq] at hcomp
    obtain ⟨rfl, hfsdef, hbsb⟩ := hcomp
    rw [hfsdef] at hfind hbc
    subst hbsb
    obtain ⟨hbm4, hcode4⟩ := CallDest.callDest_preserves _ _ _ _ _ _ _ hcd hev4
    have hc1 : 1 ≤ t4.clock := by omega
    set nfree := Compiler.Backend.WordToStack.stackFree dest' args.length k f frame with hnfree
    have hnfree' : nfree = f - (args1.length - k) := by
      simp only [hnfree, Compiler.Backend.WordToStack.stackFree]
      rw [← hsac1]
    set m := fs - (args1.length - k) with hm
    -- the target reaches the callee's allocation
    have hreach : ∀ extra : Nat,
        StackSemEvaluate.evaluate
            (Compiler.Backend.StackLang.Prog.seq q0
              (seqStackFreeNative nfree (Compiler.Backend.StackLang.Prog.call none dest' none)),
              {target with clock := target.clock + extra}) =
          (match StackSemControl.fixClock
              {t4 with stackSpace := t4.stackSpace + nfree, clock := t4.clock + extra - 1}
              (StackSemEvaluate.evaluate ((Prog.stackAlloc m).seq body,
                {t4 with stackSpace := t4.stackSpace + nfree, clock := t4.clock + extra - 1})) with
            | (res, s2) => if StackSemControl.badFunReturn res then (some .error, s2) else (res, s2)) := by
      intro extra
      rw [hcall extra, StackSemEvaluate.evaluate_call]
      simp only [hfind, if_neg (show ¬ t4.clock + extra = 0 by omega)]
      rfl
    by_cases hlim : t4.stackSpace + nfree < m
    · -- the callee's frame does not fit: Halt (Word 2w)
      have hrun := hreach 0
      rw [StackSemEvaluate.evaluate_seq (Prog.stackAlloc m) body,
        StackSemEvaluate.evaluate_stackAlloc, if_neg (by simp [r5]),
        if_pos (by simp only; omega)] at hrun
      simp only [StackSemControl.fixClock, StackSemControl.badFunReturn] at hrun
      refine ⟨_, _, by simpa using hrun, ?_⟩
      unfold compCorrectResult
      have hne : res'.map compileResult ≠ some (.halt (.word (BitVec.ofNat width 2))) := by
        rcases res' with _ | r
        · simp [wordSemBadFunReturn] at hbf
        · simp only [Option.map_some, ne_eq, Option.some.injEq]
          exact CallHelpers.compileResultNot2 r r28
      rw [if_pos hne]
      refine ⟨rfl, ?_, ?_⟩
      · show List.IsPrefix t4.ffi.ioEvents s'.ffi.ioEvents
        rw [r4]
        exact WordSemStateFiniteExact.evaluate_io_events_mono prog
          (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.decClock source))
          res' s' hbody
      · have hlimS := WordSemStateFiniteExact.evaluate_stack_limit prog _ res' s' hbody
        have hmaxS := WordSemStateFiniteExact.evaluate_stack_max prog _ res' s' hbody
        obtain ⟨-, rlim, rmax⟩ := r37
        simp only [WordSemStateFiniteExact.callEnv, WordSemStateFiniteExact.decClock] at hlimS hmaxS
        rw [hlimS, rlim]
        rcases hsm : source.stackMax with _ | a
        · rw [hsm] at hmaxS
          simp only [wordSemOptionMax] at hmaxS
          rw [hmaxS]; simp
        rcases hssc : ss with _ | c
        · rw [hsm, hssc] at hmaxS
          rcases hst : wordSemStackSize source.stack with _ | b <;>
            simp only [hst, wordSemOptionMax, wordSemOptionAdd] at hmaxS <;> (rw [hmaxS]; simp)
        rw [hssc] at hss
        simp only [Option.getD_some] at hss
        subst hss
        obtain ⟨-, -, b, hb, hbv⟩ := rmax a hsm
        rw [hsm, hssc, hb] at hmaxS
        simp only [wordSemOptionMax, wordSemOptionAdd] at hmaxS
        have hbig : t4.stack.length < max a (b + c) := by
          have := Nat.le_max_right a (b + c)
          omega
        rcases hs'm : s'.stackMax with _ | x
        · simp
        · rw [hs'm] at hmaxS
          simp only [miscThe] at hmaxS
          simp only [Option.getD_some]
          omega
    · -- the callee's frame fits: the body runs under the induction hypothesis
      set t5 : StackSemStateFiniteExact width C F :=
        {t4 with stackSpace := t4.stackSpace + nfree - m, clock := t4.clock - 1} with ht5
      have hrelC : stateRel ac k fs svc
          (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.decClock source))
          t5 lens 0 := by
        have hrel4'' := hrel4
        unfold stateRel at hrel4''
        obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18,
          g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, g33, g34, -, -,
          g37, g38, gloc⟩ := hrel4''
        have hsacf2 : args1.length - k ≤ f := by rw [← hsac1]; exact hsacf
        have hspace : t5.stackSpace = t4.stackSpace + f - fs := by
          simp only [t5]; omega
        have hpre1 : args1.IsPrefix xs := by
          by_cases hd : dest = none
          · rw [hnone hd]; exact List.dropLast_prefix xs
          · rw [hsome hd]; exact List.prefix_refl xs
        unfold stateRel
        refine ⟨?_, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18,
          g19, g20, g21, g22, g23, g24, g25, g26, g27, g28, g29, g30, g31, g32, ?_, g34, ?_,
          wfFromList2 args1, ?_, ?_, ?_⟩
        · show source.clock - 1 = t4.clock - 1
          rw [g1]
        · show t5.stackSpace + fs ≤ t4.stack.length
          omega
        · show if svc = 0 then fs = 0 else fs = svc + 1
          by_cases h : svc = 0
          · rw [if_pos h] at hfsdef ⊢; exact hfsdef.symm
          · rw [if_neg h] at hfsdef ⊢; exact hfsdef.symm
        · show stackSizeRel fs ss source.stackLimit
            (wordSemOptionMax source.stackMax (wordSemOptionAdd (wordSemStackSize source.stack) ss))
            source.stack t4.stack t5.stackSpace 0
          obtain ⟨-, glim, gmax⟩ := g37
          refine ⟨fun _ => hss, glim, ?_⟩
          intro M hM
          rcases hsm : source.stackMax with _ | a
          · rw [hsm] at hM; simp [wordSemOptionMax] at hM
          obtain ⟨hle0, -, b, hb, hbv⟩ := gmax a hsm
          rcases hssc : ss with _ | c
          · rw [hsm, hssc, hb] at hM; simp [wordSemOptionMax, wordSemOptionAdd] at hM
          rw [hssc] at hss
          simp only [Option.getD_some] at hss
          subst hss
          rw [hsm, hb, hssc] at hM
          simp only [wordSemOptionMax, wordSemOptionAdd, Option.some.injEq] at hM
          have := Nat.le_max_right a (b + c)
          refine ⟨by omega, rfl, b, hb, by omega⟩
        · show stackRel k source.handler source.stack (t4.store.lookup .handler)
            ((t4.stack.drop (t5.stackSpace + 0)).drop fs) t4.stack.length t4.bitmaps lens
          have e1 : (t4.stack.drop (t5.stackSpace + 0)).drop fs =
              (t4.stack.drop (t4.stackSpace + 0)).drop f := by
            rw [List.drop_drop, List.drop_drop]
            congr 1
            omega
          rw [e1]
          exact g38
        · intro nn v hn
          change sptLookup nn (sptFromList2 args1) = some v at hn
          have hidx : nn / 2 < args1.length := by
            have h := fromList2Lookup args1 nn
            rw [h] at hn
            split at hn
            · exact (List.getElem?_eq_some_iff.mp hn).1
            · cases hn
          have hsrc : sptLookup nn source.locals = some v :=
            getVarsFromList2Eq args source xs nn v (by rw [← hargs]; exact hgv)
              (lookupFromList2Prefix args1 xs nn v hpre1 hn)
          obtain ⟨he, hif⟩ := gloc nn v hsrc
          refine ⟨he, ?_⟩
          by_cases hlt : nn / 2 < k
          · rw [if_pos hlt] at hif ⊢
            exact hif
          · rw [if_neg hlt] at hif ⊢
            obtain ⟨hslot, -⟩ := hif
            refine ⟨?_, ?_⟩
            · rw [Nat.add_zero, List.getElem?_take, List.getElem?_drop] at hslot ⊢
              rw [if_pos (by omega)] at hslot ⊢
              rw [show t5.stackSpace + (fs - 1 - (nn / 2 - k)) =
                t4.stackSpace + (f - 1 - (nn / 2 - k)) by omega]
              exact hslot
            · have := Nat.le_max_right (maxVarHOL prog / 2 + 1 - k) (args1.length - k)
              rw [← hsvc] at this
              omega
      have hrel0 := related
      unfold stateRel at hrel0
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h25, -⟩ := hrel0
      obtain ⟨hpa, hflatp, -⟩ := h25 pLoc prog args1.length hpLoc
      have hlabels : ∀ loc, StackSem.getLabelsExact body loc → StackSem.locCheckExact t5.code loc :=
        fun loc hl => StackPropsCodeLabels.findCodeImpGetLabels dest' t4.regs t4.code _ hfind loc
          (by unfold StackSem.getLabelsExact; exact Or.inr hl)
      have hmaxv : maxVarHOL prog < 2 * svc + 2 * k := by
        have := Nat.le_max_left (maxVarHOL prog / 2 + 1 - k) (args1.length - k)
        rw [← hsvc] at this
        omega
      obtain ⟨tpost, tres, hrunb, hresb⟩ := ih xs args1 prog ss ⟨hgv, hbad, hfc, rfl, hclk⟩
        k fs svc s' t5 res' bs0 bs2 i0 i2 body lens
        ⟨hbody, notError, hrelC, hpa, hflatp, hbc, hb1, by rw [hbm4]; exact hb2,
          by rw [hbm4]; exact hb3, hlabels, hmaxv⟩
      have hbadT : StackSemControl.badFunReturn tres = false := by
        unfold compCorrectResult at hresb
        split_ifs at hresb with hne
        · rw [hresb.1]; rfl
        · rw [← not_not.mp hne]
          rcases res' with _ | r
          · simp [wordSemBadFunReturn] at hbf
          · cases r <;> first | rfl | simp [wordSemBadFunReturn] at hbf
      have hle : tpost.clock ≤ t4.clock - 1 := by
        have := StackSemEvaluateClock.evaluateClock body _ tres tpost hrunb
        exact this
      refine ⟨tpost, tres, ?_, ?_⟩
      · have reachZero := hreach 0
        simp only [Nat.add_zero] at reachZero
        rw [reachZero, StackSemEvaluate.evaluate_seq (Prog.stackAlloc m) body,
          StackSemEvaluate.evaluate_stackAlloc]
        simp only [r5, Bool.not_true, Bool.false_eq_true, if_false, hlim]
        simp only [StackSemControl.fixClock, Nat.min_self]
        simp only [t5, r5] at hrunb
        rw [hrunb]
        simp only [Nat.min_eq_right hle, hbadT, Bool.false_eq_true, if_false]
      · unfold compCorrectResult at hresb ⊢
        split_ifs at hresb ⊢ with hne
        · exact hresb
        · rcases res' with _ | r
          · simp [wordSemBadFunReturn] at hbf
          · cases r with
            | «break» l => simp [wordSemBadFunReturn] at hbf
            | «continue» l => simp [wordSemBadFunReturn] at hbf
            | _ => exact hresb


/-- A tail call into the proved loop-block fragment needs no extra target
clock, with the callee property checked against the actual code map. -/
theorem tailCall_zero_of_code {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (code : ∀ loc arity prog, sptLookup loc source.code = some (arity, prog) → LoopBlock prog) :
    ZeroSimulation ac (.call none dest args none) source := by
  apply zeroCallTail ac dest args none source
  intro xs args1 prog ss guard
  obtain ⟨loc, found, _, _, _⟩ := findCode_facts dest xs source.code source.stackSize args1 prog ss guard.2.2.1
  exact loopBlock_zero ac prog _ (code loc args1.length prog found)

end SteppedFlapjack.WordToStackSteps
