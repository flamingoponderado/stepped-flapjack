import Flapjack.Compiler.Encoders.AsmProps.EncoderCorrect
import Flapjack.Compiler.Encoders.RiscV.Target

/-!
# Encoder correctness with a step bound

`encoderCorrectWithin t steps` is the original `encoder_correct`
(`encoderCorrect`, `asmPropsScript.sml`) with its existential step count
bounded. A source `asm` step of instruction `i` is simulated by `n + 1` target
steps with `n + 1 ≤ steps i`. Everything else in the statement is unchanged,
so it implies `encoderCorrect` (`encoderCorrect_of_within`).

This is phase A of the step-preservation plan (stepped-flapjack#2). It is
stepped-flapjack infrastructure with no HOL counterpart.
-/

namespace SteppedFlapjack.RiscVSteps

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.AsmSem

/-- `encoder_correct` in which each `asm` step of `i` takes at most `steps i`
target steps. -/
def encoderCorrectWithin {width : Nat} [NeZero width] {β γ : Type}
    (t : HolAsmTarget width β γ) (steps : HolAsm width → Nat) : Prop :=
  targetOk t ∧
    ∀ (s1 : AsmState width) (i : HolAsm width) (s2 : AsmState width) (ms : β),
      asmStep t.config s1 i s2 ∧ targetStateRel t s1 ms →
      ∃ n : Nat, n + 1 ≤ steps i ∧ ∀ env : Nat → β → β,
        interferenceOk env (t.proj s1.memDomain) →
        let pcs := allPcs (t.config.encode i).length s1.pc
        asserts n (fun k s => env (n - k) (t.next s)) ms
            (fun ms' => t.stateOk ms' = true ∧
              (∀ pc, pc ∈ pcs 0 → t.getByte ms' pc = t.getByte ms pc) ∧
              t.getPc ms' ∈ pcs t.config.codeAlignment)
            (fun ms' => targetStateRel t s2 ms') ∧
          asserts2 (n + 1) (fun k => env (n + 1 - k)) t.next ms
            (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x → t.getByte ms1 x = t.getByte ms2 x)

/-- Forgetting the bound gives the original `encoder_correct`. -/
theorem encoderCorrect_of_within {width : Nat} [NeZero width] {β γ : Type}
    {t : HolAsmTarget width β γ} {steps : HolAsm width → Nat}
    (h : encoderCorrectWithin t steps) : encoderCorrect t := by
  refine ⟨h.1, fun s1 i s2 ms hs => ?_⟩
  obtain ⟨n, -, hn⟩ := h.2 s1 i s2 ms hs
  exact ⟨n, hn⟩

/-- Closes a copied case's step bound `n + 1 ≤ (riscvAst i).length` by
unfolding the emitted instruction list. -/
macro "riscv_steps_bound" : tactic => `(tactic| first
  | decide
  | omega
  | (simp (config := { zetaDelta := true }) only at *; omega)
  | (simp_all [Flapjack.Compiler.Encoders.RiscV.Target.riscvAst]; done)
  | (simp [Flapjack.Compiler.Encoders.RiscV.Target.riscvAst] <;> omega)
  | ((simp_all [Flapjack.Compiler.Encoders.RiscV.Target.riscvAst] <;> (repeat' split) <;>
      simp_all [Flapjack.Compiler.Encoders.RiscV.Target.inSignedRange, Bool.and_eq_true,
        BitVec.sle_iff_toInt_le, BitVec.reduceToInt] <;> omega); done)
  | ((simp_all [Flapjack.Compiler.Encoders.RiscV.Target.riscvAst] <;> (repeat' split) <;>
      simp_all); done))

end SteppedFlapjack.RiscVSteps
