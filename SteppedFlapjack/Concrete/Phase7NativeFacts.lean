import SteppedFlapjack.Concrete.Phase7InitializedWord
import SteppedFlapjack.Concrete.TwoProgramNativeEntry
import SteppedFlapjack.Concrete.WordBitmap

/-! The actual supported program uses the fixed native tail-entry wrapper. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.WordToStackSteps

/-- The actual pre-allocation entry selected for any supported program. -/
def supportedEntry : WordLangProgHOL (BitVec 64) := loopToWordCompFuncHOL 64 [] branchingLoopEntry

/-- The compiler-generated optimized entry and frame are independent of the callee. -/
theorem supported_nativeEntry_facts (program : Prog (RiscV.Word 64)) (supported : Supported program)
    (cfg : LabToTarget.Config) :
    let words := supportedWordPrograms program
    let code := (supportedNative program).2.2.2
    (64,1,supportedEntry) ∈ words ∧ (words.map Prod.fst).Nodup ∧
    sptLookup 64 (sptFromAList (compile countdownRiscVBackend.wordToWordConf riscvConfig words).2) = some (1,countdownOptimizedEntry) ∧
    nativeTailEntryCode countdownRiscVBackend.wordToWordConf riscvConfig words 64 supportedEntry = countdownOptimizedEntry ∧
    sptLookup 64 (fixtureWord code (supportedAllocated program).2 cfg).stackSize = some 0 := by
  let simple := panSimpProg program
  let body := progToHOL simple
  let callee := supportedCallee body
  have shape := supportedCallee_scalar simple (supported_panSimp program supported).1
  have code := supported_crepPrograms simple (supported_panSimp program supported).1
  have fresh : ofString "main" ≠ entryName body := Ne.symm (entryName_fresh body)
  have tables := twoWordTables_facts riscvConfig.isa (ofString "main") (entryName body) callee fresh shape
  have loops := (twoLoopPrograms_eq riscvConfig.isa (ofString "main") (entryName body) callee shape).symm
  have wordEq : supportedWordPrograms program = loopToWordCompileHOL
      (twoLoopPrograms riscvConfig.isa (ofString "main") (entryName body) callee) := by
    change loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (crepPrograms body)) = _
    rw [code,loops]
  have alloc : (supportedAllocated program).2 = (compile countdownRiscVBackend.wordToWordConf riscvConfig (supportedWordPrograms program)).2 := by
    have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
      funext a b c d e f g
      exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
    simp only [supportedAllocated,phase3WordConfig_eq, compileWith_eq_compile _ allocator]
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [wordEq]
    exact tables.1
  · rw [wordEq]
    exact tables.2.2.1
  · simpa [supportedWordPrograms,body,simple,code] using twoProgram_optimizedEntry_lookup riscvConfig.isa (ofString "main") (entryName body) callee fresh shape
  · simpa [supportedWordPrograms,body,simple,code,supportedEntry] using twoProgram_selectedEntry riscvConfig.isa (ofString "main") (entryName body) callee fresh shape
  · rw [alloc]
    simpa [supportedWordPrograms,body,simple,code] using twoProgram_optimizedEntry_frame riscvConfig.isa (ofString "main") (entryName body) callee fresh shape (supportedNative program).2.2.2 cfg
/-- The generated native program uses exactly the initializer bitmap. -/
theorem supported_native_bitmap (program : Prog (RiscV.Word 64)) (supported : Supported program) :
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
