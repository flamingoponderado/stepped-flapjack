import SteppedFlapjack.Concrete.GlobalConfiguredWord
import SteppedFlapjack.Concrete.FixtureMachineGuards
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.LoopSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.WordDepth.Executable
open Flapjack.Compiler.Backend.BackendProps
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopLiveSteps
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordSimpSteps SteppedFlapjack.StackSteps
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

/-- The actual Crep table selected by the source-to-Word compiler. -/
def globalSourcePrograms (pan : List (DeclHOL 64)) : List (MlS × List Nat × CrepProgHOL 64) :=
  compileProgDeclsHOLW (compileTopExactHOL
    (Pancake.PanStructs.CompileShapeExact.compileTopExact (panSimpDeclsHOL pan)) (ofString "main"))
def globalSourceRaw (pan : List (DeclHOL 64)) := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa (globalSourcePrograms pan))
def globalSourceWords (pan : List (DeclHOL 64)) := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig (globalSourceRaw pan)).2
def globalSourceNative (pan : List (DeclHOL 64)) := compileNative riscvConfig false (globalSourceWords pan)
def globalSourceCode (pan : List (DeclHOL 64)) := (globalSourceNative pan).2.2.2
def globalSourceBitmaps (pan : List (DeclHOL 64)) := (globalSourceNative pan).1
def globalSourceEntry (pan : List (DeclHOL 64)) : WordLangProgHOL (BitVec 64) :=
  ((sptLookup 64 (sptFromAList (globalSourceWords pan))).getD (1,.skip)).2
def globalSourceFrame (pan : List (DeclHOL 64)) : Nat :=
  (compileProgNative riscvConfig false (globalSourceEntry pan) 1 (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1
def globalSourceFrames (pan : List (DeclHOL 64)) : Spt Nat :=
  sptMapi (fun _ (argc,body) => (compileProgNative riscvConfig false body argc
    (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1) (sptFromAList (globalSourceWords pan))

/-- The configured native code and bitmap are outputs of the Pancake compiler
whenever the original declarations produce this raw Word table. -/
theorem globalSource_compilerOutputFor (original pan : List (DeclHOL 64))
    (rawEq : panToWordCompileProgHOL riscvConfig.isa original = globalSourceRaw pan)
    (safe : fixtureStackSafe (globalSourceCode pan) = true)
    (success : (fixtureRemoveLabels (globalSourceCode pan)).isSome = true) :
    ∃ final, Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig original =
      some (fixtureCodeBytes (globalSourceCode pan),globalSourceBitmaps pan,final) := by
  have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
  have codeEq : (compileNative riscvConfig false
      (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (globalSourceRaw pan)).2).2.2.2 = globalSourceCode pan := by
    simp [globalSourceCode,globalSourceNative,globalSourceWords,compileWith_eq_compile _ allocator,phase3WordConfig_eq]
  have bitmapEq : (compileNative riscvConfig false
      (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig (globalSourceRaw pan)).2).1 = globalSourceBitmaps pan := by
    simp [globalSourceBitmaps,globalSourceNative,globalSourceWords,compileWith_eq_compile _ allocator,phase3WordConfig_eq]
  exact fixturePancakeCompiler_outputFor original (globalSourceBitmaps pan) (globalSourceRaw pan)
    (globalSourceCode pan) rawEq codeEq bitmapEq safe success

end SteppedFlapjack.Concrete
