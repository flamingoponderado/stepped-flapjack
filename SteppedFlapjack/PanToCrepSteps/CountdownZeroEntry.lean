import SteppedFlapjack.PanToCrepSteps.CountdownZeroFrames
import SteppedFlapjack.StackSteps.ZeroFrameEntry

/-! Exclude immediate entry-frame exhaustion for the concrete countdown. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackLang SteppedFlapjack.StackSteps

/-- With the actual compiler code loaded and Stack enabled, the zero-count
entry takes at least four Stack steps. The entry allocation-failure alternative
in the compiler proof is bounded by three and therefore cannot occur. -/
theorem countdownZero_entry_not_short_failure {C F : Type}
    (entry : StackSemStateFiniteExact 64 C F) (limit : Nat)
    (codeEq : entry.code = sptFromAList (WordToStack.Native.compileNative riscvConfig false
      (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig
        (panToWordCompileProgHOL riscvConfig.isa
          (singleEntryProgram (ofString "main") (.dec (ofString "x") .one (.const (0 : BitVec 64)) (.seq .skip (.seq
            (.while (.var .local (ofString "x")) (.assign .local (ofString "x") (.op .sub [.var .local (ofString "x"),.const 1])))
            (.return (.const (0 : BitVec 64))))))))).2).2.2.2)
    (enabled : entry.useStack = true) :
    4 ≤ steps (.call none (.inl 64) none,{entry with clock := limit+1}) := by
  apply zeroFrame_entry_steps entry 64 limit (.seq .skip (.seq .skip (.call none (.inl 65) none)))
  · rw [codeEq, ← WordToWord.compileWith_eq_compile Flapjack.RegAlloc.regAllocExecutable (by
      funext a b c d e f g
      exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g)]
    exact countdownZero_native_entry_exact
  · exact enabled

end SteppedFlapjack.PanToCrepSteps
