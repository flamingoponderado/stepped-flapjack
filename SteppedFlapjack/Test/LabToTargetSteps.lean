import SteppedFlapjack.LabToTargetSteps

/-! Compile-time checks of the bounded `lab_to_target` simulation. -/

namespace SteppedFlapjack.Test.LabToTargetSteps

open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabToTarget
open SteppedFlapjack.RiscVSteps SteppedFlapjack.LabToTargetSteps

/-- One section with a label and a RISC-V `Skip` line of four bytes. -/
def skipCode : LabProgHOL 64 :=
  [⟨0, [.label 0 1 0, .asm (.asmi (.inst .skip)) [19, 0, 0, 0] 4]⟩]

/-- An empty code buffer with eight bytes of space left. -/
def buffer8 : WordSemBuffer 64 8 := ⟨0, [], 8⟩

-- The longest line of `skipCode` is the four-byte `Skip`.
example : maxLineBytes skipCode = 4 := by decide

-- Without code buffer space, one RISC-V `Skip` instruction (4 bytes, 1 tick)
-- gives `L = 4 / 4 + 1 = 2`: one tick for the line, one for an FFI or cache entry.
example : labTickBound 4 skipCode ⟨0, [], 0⟩ = 2 := by decide

-- Code that can be installed later from the buffer also counts: `L = 8 / 4 + 1`.
example : labTickBound 4 skipCode buffer8 = 3 := by decide

-- RISC-V instructions take four bytes per emitted instruction.
example : StepsFit 4 (fun i => (riscvAst i).length) riscvTarget := riscv_stepsFit

-- The bounded theorem implies the statement shape of the original.
example {width : Nat} [NeZero width] {S Q F : Type} (unit : Nat)
    (steps : HolAsm width → Nat) (p : BitVec width) (s1 s2 : State width Config F)
    (res : MachineResult) (mc : MachineConfig width S Q)
    (code2 : LabProgHOL width) (labs : Spt (Spt Nat)) (t1 : AsmState width) (ms1 : S)
    (h : oracleTie mc ms1 s1 ∧ evaluate s1 = (res, s2) ∧ res ≠ .error ∧
      encoderCorrectWithin mc.target steps ∧ StepsFit unit steps mc.target ∧
      stateRel (mc, code2, labs, p) s1 t1 ms1) :
    ∃ (k : Nat) (_t2 : Unit) (ms2 : S),
      evaluateTargetHOL mc s1.ffi (s1.clock + k) ms1 = (res, ms2, s2.ffi) :=
  compileCorrect_of_within unit steps p s1 res mc s2 code2 labs t1 ms1 h

end SteppedFlapjack.Test.LabToTargetSteps
