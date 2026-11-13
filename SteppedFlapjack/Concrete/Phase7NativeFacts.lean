import SteppedFlapjack.Concrete.Phase7InitializedWord
import SteppedFlapjack.Concrete.CountdownStackSpan
import SteppedFlapjack.Concrete.WordTables
import SteppedFlapjack.Concrete.FixtureWordStarter
import SteppedFlapjack.WordAllocSteps.CompiledCodeTail
import SteppedFlapjack.Concrete.WordBitmap

/-! The actual supported program uses the fixed native tail-entry wrapper. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.WordToStackSteps

/-- The generated native program uses exactly the initializer bitmap. -/
theorem supported_native_bitmap (program : Prog (RiscV.Word 64)) (supported : CallFreeSupported program) :
    (supportedNative program).1 = [4] := by
  let simple := panSimpProg program
  let body := progToHOL simple
  let callee := supportedCallee body
  have shape := supportedCallee_scalar simple (supported_panSimp program supported).1
  have code := supported_crepPrograms simple (supported_panSimp program supported).1
  have fresh : ofString "main" ≠ entryName body := Ne.symm (entryName_fresh body)
  have loops := (twoLoopPrograms_eq riscvConfig.isa (ofString "main") (entryName body) callee shape).symm
  have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
  simp only [supportedNative,supportedAllocated,phase3WordConfig_eq,compileWith_eq_compile _ allocator]
  change (WordToStack.Native.compileNative riscvConfig false (compile countdownRiscVBackend.wordToWordConf riscvConfig
    (loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (crepPrograms body)))).2).1 = [4]
  rw [code,loops]
  exact twoWordTables_native_bitmaps riscvConfig.isa (ofString "main") (entryName body) callee fresh shape
    countdownRiscVBackend.wordToWordConf riscvConfig
end SteppedFlapjack.Concrete
