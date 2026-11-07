import SteppedFlapjack.PanToCrepSteps.SingleEntryGlobals
import Flapjack.Pancake.Proofs.PanToTarget.ExecutableCompileDefinitions
import Flapjack.Pancake.CrepInline.InlineRouteBridge
import Flapjack.Compiler.Backend.WordToStack.Proofs.ProgramBitmaps
import SteppedFlapjack.PanToCrepSteps.CountdownExecutableCompiler
import SteppedFlapjack.PanToCrepSteps.CountdownMachineConfig
import Flapjack.Pancake.Proofs.PanToTarget.ExecutableCompileProgMaxAsmWith

/-! Structural facts about the actual countdown compiler pipeline. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm

/-- A single entry named main is renamed to the first fresh variant. -/
theorem singleEntry_main_freshName (body : ProgHOL 64) :
    newMainNameHOL (singleEntryProgram (ofString "main") body) = ofString "main'" := by
  simp [newMainNameHOL,singleEntryProgram,functionsHOL,freshNameMlS,mlstrAppend,ofString]

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

/-- Native compilation keeps the initial bitmap word at the beginning of its
output, for every program and assembler configuration. -/
theorem native_initial_bitmap_prefix (ac : AsmConfigExact 64)
    (ps : List (Nat × Nat × WordLangProgHOL (BitVec 64))) :
    [(4 : BitVec 64)].IsPrefix (WordToStack.Native.compileNative ac false ps).1 := by
  let bs : AppList (BitVec 64) × Nat := (.list [4],1)
  let out := WordToStack.Native.compileWordToStackNative ac false (ac.regCount - (5+ac.avoidRegs.length)) ps bs
  have h := WordToStack.Native.compileWordToStackIsPrefix ac false (ac.regCount - (5+ac.avoidRegs.length))
    ps bs out.1 out.2.1 out.2.2 (by exact Prod.mk.eta.symm)
  simpa [WordToStack.Native.compileNative,bs,out,appListAppend,appendAux] using h

set_option maxHeartbeats 1000000 in
/-- Any successful compilation of the countdown preserves the initializer
bitmap at the beginning of its emitted bitmap list. -/
theorem countdown_artifact_bitmap_prefix (name : MlString) (initial returned : BitVec 64)
    (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64)) (final : Backend.Config)
    (hcompile : Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend
      Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig
      (singleEntryProgram (ofString "main") (.dec name .one (.const initial) (.seq .skip (.seq
        (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
        (.return (.const returned)))))) = some (bytes,bitmaps,final)) :
    [(4 : BitVec 64)].IsPrefix bitmaps := by
  let source := singleEntryProgram (ofString "main") (.dec name .one (.const initial) (.seq .skip (.seq
    (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
    (.return (.const returned)))))
  let full := Flapjack.Pancake.Proofs.PanToTarget.compileProgMaxAsmExecutable countdownRiscVBackend
    Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig source
  have artifact : full.1 = some (bytes,bitmaps,final) := by
    simpa only [full,source,Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast_eq_fst] using hcompile
  have hfull : full = (some (bytes,bitmaps,final),full.2) := Prod.ext artifact rfl
  have hbm := (countdown_executableCompiler_lab name initial returned countdownMachineConfig rfl
    bytes bitmaps final full.2 (by simpa only [full,source] using hfull)).2
  rw [← hbm]
  exact native_initial_bitmap_prefix _ _

/-- A successful countdown artifact with one bitmap has the specific initial
bitmap word 4, rather than an arbitrary value. -/
theorem countdown_artifact_single_bitmap (name : MlString) (initial returned : BitVec 64)
    (bytes : List (BitVec 8)) (bitmap : BitVec 64) (final : Backend.Config)
    (hcompile : Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend
      Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig
      (singleEntryProgram (ofString "main") (.dec name .one (.const initial) (.seq .skip (.seq
        (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
        (.return (.const returned)))))) = some (bytes,[bitmap],final)) : bitmap = 4 := by
  have pref := countdown_artifact_bitmap_prefix name initial returned bytes [bitmap] final hcompile
  have eq : (4 : BitVec 64) = bitmap := by simpa using pref
  exact eq.symm

end SteppedFlapjack.PanToCrepSteps
