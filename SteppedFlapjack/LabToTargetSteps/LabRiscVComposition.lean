import SteppedFlapjack.LabToTargetSteps.RiscV
import Flapjack.Compiler.Backend.LabToTarget.StateTransport
namespace SteppedFlapjack.LabToTargetSteps
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target

/-- A bounded terminating LabSem run yields a bounded RISC-V run, with the
same full FFI state. -/
theorem labToRiscVWithin {F : Type} (p : BitVec 64) (lab labPost : LabSem.State 64 Config F)
    (outcome : HolOutcome) (m B : Nat) (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (code : LabProgHOL 64) (labs : Spt (Spt Nat)) (asm : AsmState 64) (machine : RiscV.L3.riscv_state)
    (hmc : mc.target = riscvTarget)
    (tie : oracleTie mc machine lab) (rel : stateRel (mc, code, labs, p) lab asm machine)
    (run : evaluate {lab with clock := m} = (.halt outcome, labPost)) (bound : m ≤ B) :
    ∃ ticks finalMachine, ticks ≤ labTickBound 4 code lab.codeBuffer * B ∧
      evaluateTargetHOL mc lab.ffi ticks machine = (.halt outcome, finalMachine, labPost.ffi) := by
  have tie' := oracleTie_clock mc machine lab m tie
  have rel' := stateRelClock (mc, code, labs, p) lab asm machine m rel
  obtain ⟨ticks, finalMachine, _, upper, targetRun⟩ :=
    compileCorrectWithin_riscv p {lab with clock := m} (.halt outcome) mc labPost code labs asm machine hmc
      ⟨tie', run, by simp, rel'⟩
  refine ⟨ticks, finalMachine, ?_, targetRun⟩
  exact upper.trans (Nat.mul_le_mul_left _ bound)
end SteppedFlapjack.LabToTargetSteps
