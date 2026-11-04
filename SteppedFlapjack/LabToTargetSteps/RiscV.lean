import SteppedFlapjack.LabToTargetSteps.CompileCorrect.Assembly
import SteppedFlapjack.RiscVSteps.Complete
import Flapjack.RiscV.CorrectnessEncoding.Length

/-!
# The bounded `lab_to_target` simulation on RISC-V

On RISC-V every emitted instruction is four bytes long, so `StepsFit` holds
with `unit = 4` for the phase A step counts `(riscvAst i).length`. With
`riscv_encoder_correct_within`, `compileCorrectWithin` then needs no encoder
hypothesis: evaluating the target with a clock of at most
`labTickBound 4 code2 s1.codeBuffer * s1.clock` ticks gives the source result.
That clock is sufficient, not the exact number of ticks the run uses, so it is
an upper bound on the ticks used.

This is stepped-flapjack infrastructure with no HOL counterpart
(stepped-flapjack#2, phase B).
-/

namespace SteppedFlapjack.LabToTargetSteps

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.RiscV.TargetProof SteppedFlapjack.RiscVSteps

/-- A RISC-V instruction that runs for `(riscvAst i).length` ticks takes
`4 * (riscvAst i).length` bytes. -/
theorem riscv_stepsFit : StepsFit 4 (fun i => (riscvAst i).length) riscvTarget :=
  ⟨by decide, fun i => (riscvEnc_length_eq i).ge⟩

/-- `compileCorrectWithin` on RISC-V, counted in total target ticks: a source
run with clock `s1.clock` is matched by the target evaluated at some clock `n`
with `s1.clock ≤ n ≤ labTickBound 4 code2 s1.codeBuffer * s1.clock`. `n` is a
sufficient clock, so the upper bound bounds the ticks used; the lower bound
says nothing about them. -/
theorem compileCorrectWithin_riscv {F : Type} (p : BitVec 64)
    (s1 : LabSem.State 64 Config F) (res : MachineResult)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (s2 : LabSem.State 64 Config F) (code2 : LabProgHOL 64) (labs : Spt (Spt Nat))
    (t1 : AsmState 64) (ms1 : RiscV.L3.riscv_state) (hmc : mc.target = riscvTarget)
    (h : oracleTie mc ms1 s1 ∧ evaluate s1 = (res, s2) ∧ res ≠ .error ∧
      stateRel (mc, code2, labs, p) s1 t1 ms1) :
    ∃ (n : Nat) (ms2 : RiscV.L3.riscv_state), s1.clock ≤ n ∧
      n ≤ labTickBound 4 code2 s1.codeBuffer * s1.clock ∧
      evaluateTargetHOL mc s1.ffi n ms1 = (res, ms2, s2.ffi) := by
  obtain ⟨ht, hev, hres, hrel⟩ := h
  exact compileCorrectWithin_total 4 (fun i => (riscvAst i).length) p s1 res mc s2 code2 labs
    t1 ms1 ⟨ht, hev, hres, hmc ▸ riscv_encoder_correct_within, hmc ▸ riscv_stepsFit, hrel⟩

end SteppedFlapjack.LabToTargetSteps
