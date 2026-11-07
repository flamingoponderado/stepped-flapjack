import SteppedFlapjack.PanToCrepSteps.SingleEntryGlobals
import Flapjack.Pancake.Proofs.PanToTarget.ExecutableCompileDefinitions
import Flapjack.Pancake.CrepInline.InlineRouteBridge

/-! Structural facts about the actual countdown compiler pipeline. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm

/-- The countdown frontend produces its wrapper and one user function,
independently of the numeric constants and target architecture. -/
theorem countdown_frontend_length (arch : AsmArchitecture) (name : MlString)
    (initial returned : BitVec 64) :
    (panToWordCompileProgHOL arch
      (singleEntryProgram (ofString "main") (.dec name .one (.const initial) (.seq .skip (.seq
        (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
        (.return (.const returned))))))).length = 2 := by
  rw [singleEntry_countdown_panToWord]
  simp only [loopToWordCompileHOL,loopToWordCompileProgHOL,List.length_map,compileProgHOLExact,
    List.length_zipWith,List.length_range,Nat.min_self,compileProgDeclsHOLW]
  rw [singleEntry_inline_selection_empty,CrepInlineRoute.compileInlTopHOLExact_nil]
  simp [compileToCrepExactHOLW,singleEntry_compileTop,functionsHOL]

/-- The executable allocator preserves the number of functions, with any
allocator and any coloring oracle. -/
theorem compileWith_length (ra : WordToWord.RegAllocFn) (wc : WordToWord.Config)
    (ac : AsmConfigExact 64) (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64))) :
    (WordToWord.compileWith ra wc ac programs).2.length = programs.length := by
  simp only [WordToWord.compileWith,List.length_map,List.length_zip,WordToWord.nextNOracle_length,Nat.min_self]

/-- The real countdown output still contains exactly the wrapper and the
compiled entry after executable register allocation. -/
theorem countdown_allocated_length (ra : WordToWord.RegAllocFn) (wc : WordToWord.Config)
    (ac : AsmConfigExact 64) (name : MlString) (initial returned : BitVec 64) :
    (WordToWord.compileWith ra wc ac (panToWordCompileProgHOL ac.isa
      (singleEntryProgram (ofString "main") (.dec name .one (.const initial) (.seq .skip (.seq
        (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
        (.return (.const returned)))))))).2.length = 2 := by
  rw [compileWith_length,countdown_frontend_length]

end SteppedFlapjack.PanToCrepSteps
