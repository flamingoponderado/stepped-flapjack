import SteppedFlapjack.RiscVSteps.Defs
import Flapjack.HolRef
import SteppedFlapjack.RiscVSteps.Skip
import Flapjack.Compiler.Encoders.RiscV.Target.AsmOkRewrites
/-! Adapted copy of `Flapjack/RiscV/CorrectnessEncoding/Rejected.lean` with the step
count of each encoder case bounded by the number of emitted RISC-V
instructions (stepped-flapjack#2, phase A). Apart from the bound, the
statements and proofs follow the original. -/

/-! Complete original LongDiv and FP encoder-correctness cases. The original
RISC-V configuration rejects LongDiv and every FP constructor in asm_ok.
The contradiction is derived from the actual source asmStep seventh conjunct;
it is not a new rejection premise. Both full existential/interference/assertion
conclusions are retained exactly. The native target statement retains the
reviewed reals_as_rational_cuts assurance limit (SOUNDNESS section 8), although
these proofs do not execute an instruction. Whole encoder/compiler correctness
remains separate assembling work. -/
namespace SteppedFlapjack.RiscVSteps
open Flapjack Flapjack.RiscV.TargetProof RiscV.L3 RiscV.L3.Step Compiler.Encoders.Asm Compiler.Encoders.AsmProps Compiler.Encoders.AsmSem Compiler.Encoders.RiscV.Target
/-- Original LongDiv637-642: all five registers remain arbitrary; the actual
source step is impossible under the reviewed RISC-V ISA configuration. -/
theorem riscv_encoder_correct_longdiv_within (r1 r2 r3 r4 r5 : Nat) (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.inst (.arith (.longDiv r1 r2 r3 r4 r5))) s2 ∧ targetStateRel riscvTarget s1 ms) :
    ∃ n : Nat, n + 1 ≤ (riscvAst (.inst (.arith (.longDiv r1 r2 r3 r4 r5)))).length ∧ ∀ env : Nat → riscv_state → riscv_state,
      interferenceOk env (riscvTarget.proj s1.memDomain) →
      let pcs := allPcs (riscvTarget.config.encode (.inst (.arith (.longDiv r1 r2 r3 r4 r5)))).length s1.pc
      asserts n (fun k s => env (n-k) (riscvTarget.next s)) ms
        (fun ms' => riscvTarget.stateOk ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
          riscvTarget.getPc ms' ∈ pcs riscvTarget.config.codeAlignment)
        (fun ms' => targetStateRel riscvTarget s2 ms') ∧
      asserts2 (n+1) (fun k => env (n+1-k)) riscvTarget.next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x →
          riscvTarget.getByte ms1 x = riscvTarget.getByte ms2 x) := by
  have good := h.1.2.2.2.2.2.2
  simp [riscvTarget,riscvConfig,asmOkExact,asmInstOkExact,asmArithOkExact] at good

/-- Original FP673-677: the entire sixteen-constructor original fp carrier
is retained; all constructors are rejected by the actual source config. -/
theorem riscv_encoder_correct_fp_within (f : HolFp) (s1 s2 : AsmState 64) (ms : riscv_state)
    (h : asmStep riscvTarget.config s1 (.inst (.fp f)) s2 ∧ targetStateRel riscvTarget s1 ms) :
    ∃ n : Nat, n + 1 ≤ (riscvAst (.inst (.fp f))).length ∧ ∀ env : Nat → riscv_state → riscv_state,
      interferenceOk env (riscvTarget.proj s1.memDomain) →
      let pcs := allPcs (riscvTarget.config.encode (.inst (.fp f))).length s1.pc
      asserts n (fun k s => env (n-k) (riscvTarget.next s)) ms
        (fun ms' => riscvTarget.stateOk ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
          riscvTarget.getPc ms' ∈ pcs riscvTarget.config.codeAlignment)
        (fun ms' => targetStateRel riscvTarget s2 ms') ∧
      asserts2 (n+1) (fun k => env (n+1-k)) riscvTarget.next ms
        (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x →
          riscvTarget.getByte ms1 x = riscvTarget.getByte ms2 x) := by
  have good := h.1.2.2.2.2.2.2
  cases f <;> simp [riscvTarget,riscvConfig,asmOkExact,asmInstOkExact,asmFpOkExact,asmFpRegOkExact,asmRegOkExact] at good

end SteppedFlapjack.RiscVSteps
