import Flapjack.RiscV.CorrectnessEncoding.TargetOk
import SteppedFlapjack.RiscVSteps.Skip
import SteppedFlapjack.RiscVSteps.ConstAssertions
import SteppedFlapjack.RiscVSteps.Binop
import SteppedFlapjack.RiscVSteps.Shift
import SteppedFlapjack.RiscVSteps.Div
import SteppedFlapjack.RiscVSteps.LongMul
import SteppedFlapjack.RiscVSteps.Rejected
import SteppedFlapjack.RiscVSteps.AddCarry
import SteppedFlapjack.RiscVSteps.AddOverflow
import SteppedFlapjack.RiscVSteps.SubOverflow
import SteppedFlapjack.RiscVSteps.MemoryAssertions
import SteppedFlapjack.RiscVSteps.Jump
import SteppedFlapjack.RiscVSteps.JumpCmp
import SteppedFlapjack.RiscVSteps.Call
import SteppedFlapjack.RiscVSteps.JumpReg
import SteppedFlapjack.RiscVSteps.Loc
import SteppedFlapjack.RiscVSteps.Defs

/-! Adapted copy of `Flapjack/RiscV/CorrectnessEncoding/Complete.lean`: the
RISC-V encoder correctness assembled from the bounded case copies. Each `asm`
step of `i` is simulated by at most `(riscvAst i).length` machine steps, the
number of RISC-V instructions emitted for `i` (stepped-flapjack#2, phase A).
Forgetting the bound recovers Flapjack's `riscv_encoder_correct`
(`riscv_encoder_correct_of_within`). Like the original, the native model
inherits the reals_as_rational_cuts assurance limit (Flapjack SOUNDNESS
section 8). -/
namespace SteppedFlapjack.RiscVSteps
open Flapjack Flapjack.RiscV.TargetProof RiscV.L3 Compiler.Encoders.Asm Compiler.Encoders.AsmProps
  Compiler.Encoders.RiscV.Target
set_option autoImplicit false

/-- RISC-V encoder correctness with each `asm` step of `i` simulated by at most
`(riscvAst i).length` machine steps. -/
theorem riscv_encoder_correct_within :
    encoderCorrectWithin riscvTarget (fun i => (riscvAst i).length) := by
  refine ⟨riscv_target_ok, ?_⟩
  intro s1 i s2 ms h
  cases i with
  | inst value =>
    cases value with
    | skip => exact riscv_encoder_correct_skip_within s1 s2 ms h
    | const r c => exact riscv_encoder_correct_const_within r c s1 s2 ms h
    | arith a =>
      cases a with
      | binop op r t right => exact riscv_encoder_correct_binop_within op r t right s1 s2 ms h
      | shift op r t right => exact riscv_encoder_correct_shift_within op r t right s1 s2 ms h
      | div r t u => exact riscv_encoder_correct_div_within r t u s1 s2 ms h
      | longMul r t u v => exact riscv_encoder_correct_longmul_within r t u v s1 s2 ms h
      | longDiv r t u v q => exact riscv_encoder_correct_longdiv_within r t u v q s1 s2 ms h
      | addCarry r t u v => exact riscv_encoder_correct_addcarry_within r t u v s1 s2 ms h
      | addOverflow r t u v => exact riscv_encoder_correct_addoverflow_within r t u v s1 s2 ms h
      | subOverflow r t u v => exact riscv_encoder_correct_suboverflow_within r t u v s1 s2 ms h
    | mem m r address =>
      cases address with
      | addr base w => exact riscv_encoder_correct_mem_within m r base w s1 s2 ms h
  | jump c => exact riscv_encoder_correct_jump_within c s1 s2 ms h
  | jumpCmp c r right a => exact riscv_encoder_correct_jumpCmp_within c r right a s1 s2 ms h
  | call c => exact riscv_encoder_correct_call_within c s1 s2 ms h
  | jumpReg r => exact riscv_encoder_correct_jumpReg_within r s1 s2 ms h
  | loc r c => exact riscv_encoder_correct_loc_within r c s1 s2 ms h

/-- The bounded theorem implies the original `encoder_correct riscv_target`. -/
theorem riscv_encoder_correct_of_within : encoderCorrect riscvTarget :=
  encoderCorrect_of_within riscv_encoder_correct_within

end SteppedFlapjack.RiscVSteps
