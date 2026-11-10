import SteppedFlapjack.PanToCrepSteps.CountdownColoring

/-! Concrete frame sizes for both compiled zero-count functions. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

/-- The original native compiler frame-size calculation for a Word row. -/
def countdownWordFrameSize (row : Nat × Nat × WordLangProgHOL (BitVec 64)) : Nat :=
  let frame := max (maxVarHOL row.2.2 / 2 + 1 - countdownZeroLimit) (row.2.1 - countdownZeroLimit)
  if frame = 0 then 0 else frame + 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The actual native compiler records the initial zero and then a zero
frame for each of the entry and countdown functions. -/
theorem countdownZero_native_frame_sizes :
    (WordToStack.Native.compileNative riscvConfig false
      (WordToWord.compileWith Flapjack.RegAlloc.regAllocExecutable countdownRiscVBackend.wordToWordConf riscvConfig
        (panToWordCompileProgHOL riscvConfig.isa
          (singleEntryProgram (ofString "main") (.dec (ofString "x") .one (.const (0 : BitVec 64)) (.seq .skip (.seq
            (.while (.var .local (ofString "x")) (.assign .local (ofString "x") (.op .sub [.var .local (ofString "x"),.const 1])))
            (.return (.const (0 : BitVec 64))))))))).2).2.2.1 = [0,0,0] := by
  rw [countdownZero_optimizedWord_exact]
  with_unfolding_all rfl

/-- Test whether the native Stack function begins with an allocation of zero. -/
def beginsWithZeroFrame : Option (Flapjack.Compiler.Backend.StackLang.HolProg 64) → Bool
  | some (.seq (.stackAlloc 0) _) => true
  | _ => false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Both actual native Stack functions start by allocating zero stack words. -/
theorem countdownZero_native_allocations_zero :
    let code := sptFromAList (WordToStack.Native.compileNative riscvConfig false
      (WordToWord.compileWith Flapjack.RegAlloc.regAllocExecutable countdownRiscVBackend.wordToWordConf riscvConfig
        (panToWordCompileProgHOL riscvConfig.isa
          (singleEntryProgram (ofString "main") (.dec (ofString "x") .one (.const (0 : BitVec 64)) (.seq .skip (.seq
            (.while (.var .local (ofString "x")) (.assign .local (ofString "x") (.op .sub [.var .local (ofString "x"),.const 1])))
            (.return (.const (0 : BitVec 64))))))))).2).2.2.2
    beginsWithZeroFrame (sptLookup 64 code) = true ∧ beginsWithZeroFrame (sptLookup 65 code) = true := by
  dsimp only
  rw [countdownZero_optimizedWord_exact]
  with_unfolding_all decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- The exact native entry wrapper: a zero allocation followed by the call
to the countdown body. -/
theorem countdownZero_native_entry_exact :
    sptLookup 64 (sptFromAList (WordToStack.Native.compileNative riscvConfig false
      (WordToWord.compileWith Flapjack.RegAlloc.regAllocExecutable countdownRiscVBackend.wordToWordConf riscvConfig
        (panToWordCompileProgHOL riscvConfig.isa
          (singleEntryProgram (ofString "main") (.dec (ofString "x") .one (.const (0 : BitVec 64)) (.seq .skip (.seq
            (.while (.var .local (ofString "x")) (.assign .local (ofString "x") (.op .sub [.var .local (ofString "x"),.const 1])))
            (.return (.const (0 : BitVec 64))))))))).2).2.2.2) =
    some (.seq (.stackAlloc 0) (.seq .skip (.seq .skip (.call none (.inl 65) none)))) := by
  rw [countdownZero_optimizedWord_exact]
  with_unfolding_all rfl

end SteppedFlapjack.PanToCrepSteps
