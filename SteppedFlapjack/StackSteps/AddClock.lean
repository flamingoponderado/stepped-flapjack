import SteppedFlapjack.StackSteps.Defs
import Flapjack.Compiler.Backend.StackProps.EvaluateAddClock

/-! ### Clock monotonicity of the step count

`steps` counts `evaluate` invocations and never observes the clock itself: each
clause equation picks its recursive calls from the run's result and states, and
those are unchanged when the input clock is raised, as long as the run does not
time out. So a run that stops normally at clock `s.clock` takes exactly the same
number of steps at clock `s.clock + d`, for every `d`.

This is what lets a run-clock bound be reused at a larger clock: the compiler
correctness induction hands the second half of a `Seq` a clock raised by the
first half's allowance, and the step count must not grow. -/

namespace SteppedFlapjack.StackSteps

open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemMeasure
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemStateOps Flapjack.StackSemControl

set_option maxHeartbeats 2000000 in
theorem steps_addClock {width : Nat} [NeZero width] {C F : Type} (d : Nat) :
    ∀ (measure : Nat × Nat) (program : HolProg width)
      (source : StackSemStateFiniteExact width C F),
      stackSemMeasure program source = measure →
      ∀ (result : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F),
      evaluate (program, source) = (result, post) → result ≠ some .timeOut →
      steps (program, {source with clock := source.clock + d}) = steps (program, source) := by
  intro measure
  induction measure using Compiler.Backend.StackProps.EvaluateAddClock.lexNat_wf.induction with
  | _ measure ih =>
    intro program source hm result post hfx hne
    subst hm
    cases program
    case seq a b =>
      rcases hfxA : evaluate (a, source) with ⟨ra, s1⟩
      have hra : ra ≠ some .timeOut := by
        intro h
        have h' := hfx
        rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, hfxA, h] at h'
        dsimp only at h'
        exact hne ((Prod.mk.injEq _ _ _ _).mp h').1.symm
      have haddA := Compiler.Backend.StackProps.evaluateAddClock d a source ra s1 ⟨hfxA, hra⟩
      have hsmallerA := seq_first_measure_lt a b source
      have hsmallerB : LexNat (stackSemMeasure b s1) (stackSemMeasure (.seq a b) source) := by
        have h := seq_second_measure_lt a b source (evaluate (a, source))
        rw [StackSemEvaluateClock.fixClockEvaluate, hfxA] at h
        exact h
      cases ra with
      | none =>
        have hrunB : evaluate (b, s1) = (result, post) := by
          have h' := hfx
          rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, hfxA] at h'
          dsimp only at h'
          exact h'
        rw [steps_seq_run a b _ _ haddA, steps_seq_run a b source s1 hfxA,
          ih _ hsmallerA a source rfl none s1 hfxA hra,
          ih _ hsmallerB b s1 rfl result post hrunB hne]
      | some r =>
        have hseq : steps ((.seq a b : HolProg width), source) = 1 + steps (a, source) := by
          rw [steps_seq, StackSemEvaluateClock.fixClockEvaluate, hfxA]
          dsimp only
          omega
        have hseqD : steps ((.seq a b : HolProg width), {source with clock := source.clock + d}) =
            1 + steps (a, {source with clock := source.clock + d}) := by
          rw [steps_seq, StackSemEvaluateClock.fixClockEvaluate, haddA]
          dsimp only
          omega
        rw [hseq, hseqD, ih _ hsmallerA a source rfl (some r) s1 hfxA hra]
    case ite cmp r ri a b =>
      have hx : getVar r {source with clock := source.clock + d} = getVar r source := rfl
      have hy : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm ri)
          {source with clock := source.clock + d} =
          StackSemStateOps.getVarImm (HolRegImm.toWordRegImm ri) source := rfl
      rw [steps_ite cmp r ri a b {source with clock := source.clock + d},
        steps_ite cmp r ri a b source, hx, hy]
      rcases hxr : getVar r source with _ | x
      · dsimp only
      · rcases hyr : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm ri) source with _ | y
        · dsimp only
        · rcases hwr : wordSemWordCmp cmp x y with _ | w
          · simp only [hwr]
          · cases w
            · have hrun : evaluate (b, source) = (result, post) := by
                have h' := hfx
                rw [evaluate_ite, hxr, hyr] at h'
                dsimp only at h'
                rw [hwr] at h'
                dsimp only at h'
                exact h'
              simp only [hwr]
              rw [ih _ (if_second_measure_lt cmp r ri a b source) b source rfl result post hrun hne]
            · have hrun : evaluate (a, source) = (result, post) := by
                have h' := hfx
                rw [evaluate_ite, hxr, hyr] at h'
                dsimp only at h'
                rw [hwr] at h'
                dsimp only at h'
                exact h'
              simp only [hwr]
              rw [ih _ (if_first_measure_lt cmp r ri a b source) a source rfl result post hrun hne]
    case loop body =>
      rcases hfxB : evaluate (body, source) with ⟨resB, s1⟩
      have hresB : resB ≠ some .timeOut := by
        intro h
        have h' := hfx
        rw [evaluate_loop, StackSemEvaluateClock.fixClockEvaluate, hfxB, h] at h'
        dsimp only at h'
        exact hne ((Prod.mk.injEq _ _ _ _).mp h').1.symm
      have haddB := Compiler.Backend.StackProps.evaluateAddClock d body source resB s1 ⟨hfxB, hresB⟩
      have hstepS : steps ((.loop body : HolProg width), source) =
          1 + steps (body, source) +
            (if contLoop resB ∧ s1.clock ≠ 0 then steps (.loop body, decClock s1) else 0) := by
        rw [steps_loop, StackSemEvaluateClock.fixClockEvaluate, hfxB]
      have hstepD : steps ((.loop body : HolProg width), {source with clock := source.clock + d}) =
          1 + steps (body, {source with clock := source.clock + d}) +
            (if contLoop resB ∧ s1.clock + d ≠ 0 then
              steps (.loop body, decClock {s1 with clock := s1.clock + d}) else 0) := by
        rw [steps_loop, StackSemEvaluateClock.fixClockEvaluate, haddB]
      rw [hstepS, hstepD,
        ih _ (loop_body_measure_lt body source) body source rfl resB s1 hfxB hresB]
      by_cases hc : contLoop resB
      · have hclock : s1.clock ≠ 0 := by
          intro h0
          have h' := hfx
          rw [evaluate_loop, StackSemEvaluateClock.fixClockEvaluate, hfxB] at h'
          dsimp only at h'
          rw [if_pos hc, if_pos h0] at h'
          exact hne ((Prod.mk.injEq _ _ _ _).mp h').1.symm
        have hcont : contLoop resB ∧ s1.clock ≠ 0 := ⟨hc, hclock⟩
        have hrun : evaluate (.loop body, decClock s1) = (result, post) := by
          have h' := hfx
          rw [evaluate_loop, StackSemEvaluateClock.fixClockEvaluate, hfxB] at h'
          dsimp only at h'
          rw [if_pos hc, if_neg hclock] at h'
          exact h'
        have hsmaller : LexNat (stackSemMeasure (.loop body) (decClock s1))
            (stackSemMeasure (.loop body) source) := by
          have hne0 : (fixClock source (evaluate (body, source))).2.clock ≠ 0 := by
            rw [StackSemEvaluateClock.fixClockEvaluate, hfxB]
            exact hclock
          have h := loop_reentry_measure_lt body source (evaluate (body, source)) hne0
          rw [StackSemEvaluateClock.fixClockEvaluate, hfxB] at h
          exact h
        have hd : decClock {s1 with clock := s1.clock + d} =
            {decClock s1 with clock := (decClock s1).clock + d} :=
          Compiler.Backend.StackProps.EvaluateAddClock.decClock_addClock s1 d hclock
        rw [hd, if_pos hcont, if_pos ⟨hc, by omega⟩]
        rw [ih _ hsmaller (.loop body) (decClock s1) rfl result post hrun hne]
      · rw [if_neg (by intro h; exact hc h.1), if_neg (by intro h; exact hc h.1)]
    case jumpLower r1 r2 dest =>
      have hx1 : getVar r1 {source with clock := source.clock + d} = getVar r1 source := rfl
      have hx2 : getVar r2 {source with clock := source.clock + d} = getVar r2 source := rfl
      have hcd : findCode (.inl dest) {source with clock := source.clock + d}.regs
          {source with clock := source.clock + d}.code =
          findCode (.inl dest) source.regs source.code := rfl
      rcases h1 : getVar r1 source with _ | x1
      · rw [steps_jumpLower r1 r2 dest {source with clock := source.clock + d},
            steps_jumpLower r1 r2 dest source, hx1, hx2, h1]
      · rcases h2 : getVar r2 source with _ | x2
        · rw [steps_jumpLower r1 r2 dest {source with clock := source.clock + d},
              steps_jumpLower r1 r2 dest source, hx1, hx2, h1, h2]
          simp only []
        · rcases x1 with v | ⟨b, o⟩
          · rcases x2 with v2 | ⟨b2, o2⟩
            · rw [steps_jumpLower r1 r2 dest {source with clock := source.clock + d},
                  steps_jumpLower r1 r2 dest source, hx1, hx2, hcd, h1, h2]
              simp only []
              cases hb : wordCmpHOL .lower v v2
              · try rw [hb]
                simp only [Bool.false_eq_true, if_false]
              · try rw [hb]
                rw [if_pos rfl]
                rcases hf : findCode (.inl dest) source.regs source.code with _ | prog
                · simp
                · simp
                  have hclock : source.clock ≠ 0 := by
                    intro h0
                    have h' := hfx
                    rw [evaluate_jumpLower, h1, h2] at h'
                    simp only [] at h'
                    rw [hb] at h'
                    rw [if_pos rfl] at h'
                    rw [hf] at h'
                    simp only [] at h'
                    rw [if_pos h0] at h'
                    exact hne (by
                      have hfst := congrArg Prod.fst h'
                      first | exact hfst | exact hfst.symm)
                  rcases hfxP : evaluate (prog, decClock source) with ⟨resP, s2⟩
                  have hresP : resP ≠ some .timeOut := by
                    intro h
                    have h' := hfx
                    rw [evaluate_jumpLower, h1, h2] at h'
                    simp only [] at h'
                    rw [hb] at h'
                    rw [if_pos rfl] at h'
                    rw [hf] at h'
                    simp only [] at h'
                    rw [if_neg hclock, hfxP] at h'
                    simp only [] at h'
                    rw [show StackSemControl.badFunReturn resP = false from by rw [h]; rfl] at h'
                    simp only [Bool.false_eq_true, if_false] at h'
                    exact hne (by
                      have hfst := congrArg Prod.fst h'
                      rw [h] at hfst
                      first | exact hfst | exact hfst.symm)
                  rw [if_neg (by omega : ¬ (source.clock = 0 ∧ d = 0)), if_neg hclock]
                  rw [Compiler.Backend.StackProps.EvaluateAddClock.decClock_addClock source d hclock]
                  rw [ih _ (callee_measure_lt prog (.jumpLower r1 r2 dest) source hclock)
                    prog (decClock source) rfl resP s2 hfxP hresP]
            · rw [steps_jumpLower r1 r2 dest {source with clock := source.clock + d},
                  steps_jumpLower r1 r2 dest source, hx1, hx2, h1, h2]
              try simp only []
          · rw [steps_jumpLower r1 r2 dest {source with clock := source.clock + d},
                steps_jumpLower r1 r2 dest source, hx1, hx2, h1, h2]
            try simp only []
    case rawCall dest =>
      have hk : sptLookup dest {source with clock := source.clock + d}.code =
          sptLookup dest source.code := rfl
      rcases hl : sptLookup dest source.code with _ | prog
      · rw [steps_rawCall dest {source with clock := source.clock + d}, steps_rawCall dest source, hk, hl]
      · rcases hd : destSeq prog with _ | ⟨fst, body⟩
        · rw [steps_rawCall dest {source with clock := source.clock + d}, steps_rawCall dest source, hk, hl]
          simp only []
          rw [hd]
          try simp only []
        · rw [steps_rawCall dest {source with clock := source.clock + d}, steps_rawCall dest source, hk, hl]
          simp only []
          rw [hd]
          try simp only []
          have hclock : source.clock ≠ 0 := by
            intro h0
            have h' := hfx
            rw [evaluate_rawCall, hl] at h'
            simp only [] at h'
            rw [hd] at h'
            simp only [] at h'
            rw [if_pos h0] at h'
            exact hne (by
              have hfst := congrArg Prod.fst h'
              first | exact hfst | exact hfst.symm)
          rcases hfxP : evaluate (body, decClock source) with ⟨resP, s2⟩
          have hresP : resP ≠ some .timeOut := by
            intro h
            have h' := hfx
            rw [evaluate_rawCall, hl] at h'
            simp only [] at h'
            rw [hd] at h'
            simp only [] at h'
            rw [if_neg hclock, hfxP] at h'
            simp only [] at h'
            rw [show StackSemControl.badFunReturn resP = false from by rw [h]; rfl] at h'
            simp only [Bool.false_eq_true, if_false] at h'
            exact hne (by
              have hfst := congrArg Prod.fst h'
              rw [h] at hfst
              first | exact hfst | exact hfst.symm)
          rw [if_neg (by omega : ¬ (source.clock + d = 0)), if_neg hclock]
          rw [Compiler.Backend.StackProps.EvaluateAddClock.decClock_addClock source d hclock]
          rw [ih _ (callee_measure_lt body (.rawCall dest) source hclock)
            body (decClock source) rfl resP s2 hfxP hresP]
    case call ret dest handler =>
      rcases ret with _ | ⟨retH, link, l1, l2⟩
      · have hf' : findCode dest {source with clock := source.clock + d}.regs
            {source with clock := source.clock + d}.code =
            findCode dest source.regs source.code := rfl
        rcases hf : findCode dest source.regs source.code with _ | prog
        · rw [steps_call_none dest handler {source with clock := source.clock + d},
              steps_call_none dest handler source, hf', hf]
        · rcases handler with _ | ⟨h, hl1, hl2⟩
          · rw [steps_call_none dest none {source with clock := source.clock + d},
                steps_call_none dest none source, hf', hf]
            simp only []
            have hclock : source.clock ≠ 0 := by
              intro h0
              have h' := hfx
              rw [evaluate_call, hf] at h'
              simp only [] at h'
              rw [if_pos h0] at h'
              exact hne (by
                have hfst := congrArg Prod.fst h'
                first | exact hfst | exact hfst.symm)
            rcases hfxP : evaluate (prog, decClock source) with ⟨resP, s2⟩
            have hfixP : fixClock (decClock source) (resP, s2) = (resP, s2) := by
              rw [← hfxP]
              exact StackSemEvaluateClock.fixClockEvaluate prog (decClock source)
            have hresP : resP ≠ some .timeOut := by
              intro h
              have h' := hfx
              rw [evaluate_call, hf] at h'
              simp only [] at h'
              rw [if_neg hclock, hfxP] at h'
              rw [hfixP] at h'
              rw [show StackSemControl.badFunReturn resP = false from by rw [h]; rfl] at h'
              simp only [Bool.false_eq_true, if_false] at h'
              exact hne (by
                have hfst := congrArg Prod.fst h'
                rw [h] at hfst
                first | exact hfst | exact hfst.symm)
            rw [if_neg (by omega : ¬ (source.clock + d = 0)), if_neg hclock]
            rw [Compiler.Backend.StackProps.EvaluateAddClock.decClock_addClock source d hclock]
            rw [ih _ (callee_measure_lt prog (.call none dest none) source hclock)
              prog (decClock source) rfl resP s2 hfxP hresP]
          · rw [steps_call_none dest (some (h, hl1, hl2))
                {source with clock := source.clock + d},
                steps_call_none dest (some (h, hl1, hl2)) source, hf', hf]
            try simp only []
      · have hf' : findCode dest ({source with clock := source.clock + d}.regs.eraseEq link)
            {source with clock := source.clock + d}.code =
            findCode dest (source.regs.eraseEq link) source.code := rfl
        rcases hf : findCode dest (source.regs.eraseEq link) source.code with _ | prog
        · rw [steps_call_some retH link l1 l2 dest handler
              {source with clock := source.clock + d},
              steps_call_some retH link l1 l2 dest handler source, hf', hf]
        · rw [steps_call_some retH link l1 l2 dest handler
              {source with clock := source.clock + d},
              steps_call_some retH link l1 l2 dest handler source, hf', hf]
          simp only []
          have hclock : source.clock ≠ 0 := by
            intro h0
            have h' := hfx
            rw [evaluate_call] at h'
            simp only [] at h'
            rw [hf] at h'
            simp only [] at h'
            rw [if_pos h0] at h'
            exact hne (by
              have hfst := congrArg Prod.fst h'
              first | exact hfst | exact hfst.symm)
          have hdec : decClock (setVar link (.loc l1 l2) {source with clock := source.clock + d}) =
              {decClock (setVar link (.loc l1 l2) source) with
                clock := (decClock (setVar link (.loc l1 l2) source)).clock + d} := by
            rw [show setVar link (.loc l1 l2) {source with clock := source.clock + d} =
                {setVar link (.loc l1 l2) source with
                  clock := (setVar link (.loc l1 l2) source).clock + d} from rfl]
            exact Compiler.Backend.StackProps.EvaluateAddClock.decClock_addClock
              (setVar link (.loc l1 l2) source) d hclock
          rcases hfxP : evaluate (prog, decClock (setVar link (.loc l1 l2) source)) with
            ⟨resP, s2⟩
          have hfixP : fixClock (decClock (setVar link (.loc l1 l2) source)) (resP, s2) =
              (resP, s2) := by
            rw [← hfxP]
            exact StackSemEvaluateClock.fixClockEvaluate prog
              (decClock (setVar link (.loc l1 l2) source))
          have hresP : resP ≠ some .timeOut := by
            intro h
            have h' := hfx
            rw [evaluate_call] at h'
            simp only [] at h'
            rw [hf] at h'
            simp only [] at h'
            rw [if_neg hclock] at h'
            rw [hfxP] at h'
            rw [hfixP] at h'
            rw [h] at h'
            simp only [] at h'
            exact hne (by
              have hfst := congrArg Prod.fst h'
              first | exact hfst | exact hfst.symm)
          rw [if_neg (by omega : ¬ (source.clock + d = 0)), if_neg hclock]
          have hfixD : fixClock
              {decClock (setVar link (.loc l1 l2) source) with
                clock := (decClock (setVar link (.loc l1 l2) source)).clock + d}
              (resP, {s2 with clock := s2.clock + d}) =
              (resP, {s2 with clock := s2.clock + d}) := by
            rw [← Compiler.Backend.StackProps.evaluateAddClock d prog _
              resP s2 ⟨hfxP, hresP⟩]
            exact StackSemEvaluateClock.fixClockEvaluate prog _
          rw [hdec]
          rw [Compiler.Backend.StackProps.evaluateAddClock d prog _
            resP s2 ⟨hfxP, hresP⟩]
          rw [hfixD, hfixP]
          simp only []
          rw [ih _ (callee_measure_lt prog (.call (some (retH, link, l1, l2)) dest handler)
              source hclock)
            prog (decClock (setVar link (.loc l1 l2) source)) rfl resP s2 hfxP hresP]
          rcases resP with _ | r
          · try simp only []
          · rcases r with ⟨x⟩ | ⟨x⟩ | _ | _ | _ | _ | _ | _
            · by_cases hx : x = .loc l1 l2
              · have hrun : evaluate (retH, s2) = (result, post) := by
                  have h' := hfx
                  rw [evaluate_call] at h'
                  simp only [] at h'
                  rw [hf] at h'
                  simp only [] at h'
                  rw [if_neg hclock] at h'
                  rw [hfxP] at h'
                  rw [hfixP] at h'
                  rw [hx] at h'
                  simp only [] at h'
                  try rw [if_neg (by intro hne; exact hne rfl)] at h'
                  exact h'
                simp only []
                rw [if_pos hx]
                rw [ih _ (call_continuation_measure_lt retH
                    (.call (some (retH, link, l1, l2)) dest handler) source link l1 l2
                    (evaluate (prog, decClock (setVar link (.loc l1 l2) source))) hclock)
                  retH s2 (by rw [hfxP, hfixP]) result post hrun hne]
                try rw [if_pos hx]
              · simp only []
                rw [if_neg hx]
                try rw [if_neg hx]
            · rcases handler with _ | ⟨h, hl1, hl2⟩
              · try simp only []
              · by_cases hx : x = .loc hl1 hl2
                · have hrun : evaluate (h, s2) = (result, post) := by
                    have h' := hfx
                    rw [evaluate_call] at h'
                    simp only [] at h'
                    rw [hf] at h'
                    simp only [] at h'
                    rw [if_neg hclock] at h'
                    rw [hfxP] at h'
                    rw [hfixP] at h'
                    rw [hx] at h'
                    simp only [] at h'
                    try rw [if_neg (by intro hne; exact hne rfl)] at h'
                    exact h'
                  simp only []
                  rw [if_pos hx]
                  rw [ih _ (call_continuation_measure_lt h
                      (.call (some (retH, link, l1, l2)) dest (some (h, hl1, hl2)))
                      source link l1 l2
                      (evaluate (prog, decClock (setVar link (.loc l1 l2) source))) hclock)
                    h s2 (by rw [hfxP, hfixP]) result post hrun hne]
                  try rw [if_pos hx]
                · simp only []
                  rw [if_neg hx]
                  try rw [if_neg hx]
            · try simp only []
            · try simp only []
            · try simp only []
            · try simp only []
            · try simp only []
            · try simp only []
    all_goals rw [steps_leaf _ _ (by simp [isRecursive]), steps_leaf _ _ (by simp [isRecursive])]

/-- The recursive call of `jumpLower`, `rawCall` and `call` runs on `decClock s`,
and `decClock` commutes with raising the clock. -/
theorem steps_decClock_addClock {width : Nat} [NeZero width] {C F : Type}
    (d : Nat) (program : HolProg width) (source : StackSemStateFiniteExact width C F)
    (hclock : source.clock ≠ 0)
    (result : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F)
    (hrun : evaluate (program, decClock source) = (result, post))
    (hne : result ≠ some .timeOut) :
    steps (program, decClock {source with clock := source.clock + d}) =
      steps (program, decClock source) := by
  rw [Compiler.Backend.StackProps.EvaluateAddClock.decClock_addClock source d hclock]
  exact steps_addClock d _ program (decClock source) rfl result post hrun hne

end SteppedFlapjack.StackSteps
