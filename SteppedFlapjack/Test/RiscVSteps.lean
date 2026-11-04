import SteppedFlapjack.RiscVSteps.Complete

/-! Compile-time checks of the bounded RISC-V encoder correctness. -/

namespace SteppedFlapjack.Test.RiscVSteps

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.RiscVSteps

-- The bound is the number of emitted RISC-V instructions: one for Skip.
example : (riscvAst (.inst .skip)).length = 1 := by decide

-- The bounded theorem is unconditional and implies the original.
example : encoderCorrectWithin riscvTarget (fun i => (riscvAst i).length) :=
  riscv_encoder_correct_within
example : Flapjack.Compiler.Encoders.AsmProps.encoderCorrect riscvTarget :=
  riscv_encoder_correct_of_within

end SteppedFlapjack.Test.RiscVSteps
