import SteppedFlapjack.RiscVSteps.Defs
import SteppedFlapjack.RiscVSteps.ShiftLslRegister
import SteppedFlapjack.RiscVSteps.ShiftLslImmediate
import SteppedFlapjack.RiscVSteps.ShiftLsrRegister
import SteppedFlapjack.RiscVSteps.ShiftLsrImmediate
import SteppedFlapjack.RiscVSteps.ShiftAsrRegister
import SteppedFlapjack.RiscVSteps.ShiftAsrImmediate
import SteppedFlapjack.RiscVSteps.ShiftRorRegister
import SteppedFlapjack.RiscVSteps.ShiftRorImmediate

/-! Adapted copy of `Flapjack/RiscV/CorrectnessEncoding/Shift.lean` with the step
count of each encoder case bounded by the number of emitted RISC-V
instructions (stepped-flapjack#2, phase A). Apart from the bound, the
statements and proofs follow the original. -/

namespace SteppedFlapjack.RiscVSteps
open Flapjack Flapjack.RiscV.TargetProof RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm
  Compiler.Encoders.AsmProps Compiler.Encoders.AsmSem Compiler.Encoders.RiscV.Target
set_option autoImplicit false

/-- Full original Shift constructor (source560-620), assembled over all four
operators and both Reg/Imm forms. Sole original source-step/initial relation
premise and complete existential all-environment assertions remain unchanged.
Each concrete case derives actual native Next from emitted bytes, including
zero-count Ror and legal aliases. Inherits reals_as_rational_cuts through native
state closure (SOUNDNESS item8). `CorrectnessEncoding.Complete`
assembles the full encoder correctness theorem. -/
theorem riscv_encoder_correct_shift_within (op : Flapjack.Shift) (rd rs1 : Nat) (right : HolRegImm 64) (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.inst (.arith (.shift op rd rs1 right))) s2 ∧
      targetStateRel riscvTarget s1 ms) :
    ∃ n : Nat, n + 1 ≤ (riscvAst (.inst (.arith (.shift op rd rs1 right)))).length ∧ ∀ env : Nat → riscv_state → riscv_state,
      interferenceOk env (riscvTarget.proj s1.memDomain) →
      let pcs := allPcs (riscvTarget.config.encode (.inst (.arith (.shift op rd rs1 right)))).length s1.pc
      asserts n (fun k s => env (n - k) (riscvTarget.next s)) ms
        (fun ms' => riscvTarget.stateOk ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
          riscvTarget.getPc ms' ∈ pcs riscvTarget.config.codeAlignment)
        (fun ms' => targetStateRel riscvTarget s2 ms') ∧
      asserts2 (n + 1) (fun k => env (n + 1 - k)) riscvTarget.next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x →
          riscvTarget.getByte ms1 x = riscvTarget.getByte ms2 x) := by
  cases op <;> cases right
  · exact riscv_encoder_correct_shiftLslRegister_within rd rs1 _ s1 s2 ms h
  · exact riscv_encoder_correct_shiftLslImmediate_within rd rs1 _ s1 s2 ms h
  · exact riscv_encoder_correct_shiftLsrRegister_within rd rs1 _ s1 s2 ms h
  · exact riscv_encoder_correct_shiftLsrImmediate_within rd rs1 _ s1 s2 ms h
  · exact riscv_encoder_correct_shiftAsrRegister_within rd rs1 _ s1 s2 ms h
  · exact riscv_encoder_correct_shiftAsrImmediate_within rd rs1 _ s1 s2 ms h
  · exact riscv_encoder_correct_shiftRorRegister_within rd rs1 _ s1 s2 ms h
  · exact riscv_encoder_correct_shiftRorImmediate_within rd rs1 _ s1 s2 ms h

end SteppedFlapjack.RiscVSteps
