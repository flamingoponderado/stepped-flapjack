import SteppedFlapjack.Concrete.CountdownLabBounds

/-! The countdown's variable input affects label removal only through the
length of its RISC-V constant encoding. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.Phase6

/-- Same-sized constant encodings produce related compiled countdown code. -/
theorem countdown_removeLabels_rel (n m : Nat) (cfg : LabToTarget.Config)
    (same : constCount (BitVec.ofNat 64 n) = constCount (BitVec.ofNat 64 m)) :
    OptRel (removeLabels 5 riscvConfig 0 .ln [] (LabFilter.filterSkip (fixtureLab (countdownNativeStackCode n) cfg).code))
      (removeLabels 5 riscvConfig 0 .ln [] (LabFilter.filterSkip (fixtureLab (countdownNativeStackCode m) cfg).code)) := by
  change OptRel (removeLabels 5 riscvConfig 0 .ln [] (LabFilter.filterSkip
    (StackToLab.compile countdownRiscVBackend.stackConf countdownRiscVBackend.dataConf (2^53-1) 24
      riscvConfig.addrOffset (countdownNativeStackCode n))))
    (removeLabels 5 riscvConfig 0 .ln [] (LabFilter.filterSkip
    (StackToLab.compile countdownRiscVBackend.stackConf countdownRiscVBackend.dataConf (2^53-1) 24
      riscvConfig.addrOffset (countdownNativeStackCode m))))
  rw [countdown_nativeShape n,countdown_nativeShape m]
  exact prefix_removeLabels_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ same

/-- Three concrete constants cover every possible input encoding length. -/
theorem countdown_removeLabels_cases (n : Nat) (cfg : LabToTarget.Config) :
    OptRel (removeLabels 5 riscvConfig 0 .ln [] (LabFilter.filterSkip (fixtureLab (countdownNativeStackCode n) cfg).code))
      (removeLabels 5 riscvConfig 0 .ln [] (LabFilter.filterSkip (fixtureLab (countdownNativeStackCode 0) cfg).code)) ∨
    OptRel (removeLabels 5 riscvConfig 0 .ln [] (LabFilter.filterSkip (fixtureLab (countdownNativeStackCode n) cfg).code))
      (removeLabels 5 riscvConfig 0 .ln [] (LabFilter.filterSkip (fixtureLab (countdownNativeStackCode 2048) cfg).code)) ∨
    OptRel (removeLabels 5 riscvConfig 0 .ln [] (LabFilter.filterSkip (fixtureLab (countdownNativeStackCode n) cfg).code))
      (removeLabels 5 riscvConfig 0 .ln [] (LabFilter.filterSkip (fixtureLab (countdownNativeStackCode (2^31)) cfg).code)) := by
  rcases constCount_cases (BitVec.ofNat 64 n) with h | h | h
  · exact Or.inl (countdown_removeLabels_rel n 0 cfg h)
  · exact Or.inr (Or.inl (countdown_removeLabels_rel n 2048 cfg h))
  · exact Or.inr (Or.inr (countdown_removeLabels_rel n (2^31) cfg h))

end SteppedFlapjack.Concrete
