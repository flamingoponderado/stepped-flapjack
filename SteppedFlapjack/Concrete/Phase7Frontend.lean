import SteppedFlapjack.Concrete.WitnessLoopCode
import SteppedFlapjack.Concrete.CountedApplications
import SteppedFlapjack.Concrete.BranchEntryLoop
import SteppedFlapjack.CrepSteps.TailEntry
import SteppedFlapjack.CrepToLoopSteps.TailEntryLoop
import SteppedFlapjack.CrepToLoopSteps.ScalarSequenceBound

/-! Generated code for the supported Phase 7 frontend. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open Flapjack.Compiler.Encoders.Asm Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

def supportedCallee (body : ProgHOL 64) : CrepProgHOL 64 :=
  let caller := frontendContext body
  compileProgExactHOLW (ctxtFcExactHOL caller.funcs caller.eids [] [] []) body

/-- The actual generated singleton program contains its entry and compiled body. -/
theorem supported_crepPrograms (program : Prog (RiscV.Word 64)) (supported : CallFreeSupported program) :
    crepPrograms (progToHOL program) =
      twoPrograms (ofString "main") (entryName (progToHOL program)) (supportedCallee (progToHOL program)) := by
  let body := progToHOL program
  have renameEq : fpermHOL (ofString "main") (entryName body) body = body := supported_fperm supported _ _
  have renameEq' : fpermHOL (ofString "main") (newMainNameHOL (singleEntryProgram (ofString "main") body)) body = body := by
    simpa [entryName] using renameEq
  have globalEq : compileProgExactHOL emptyGlobalsContext body = body := supported_globals_fixed supported _
  change crepPrograms body = twoPrograms (ofString "main") (entryName body) (supportedCallee body)
  unfold crepPrograms declarations
  rw [compileProgDeclsHOLW, singleEntry_inline_selection_empty, CrepInlineRoute.compileInlTopHOLExact_nil,
    singleEntry_compileTop]
  simp [twoPrograms, supportedCallee, frontendContext, declarations, singleEntry_compileTop, entryName,
    compileToCrepExactHOLW, functionsHOL, compFuncExactHOLW, compileProgExactHOLW,
    compileCallNoReturnExactHOLW, compileExpExactHOLWList, crepVarsHOL, renameEq', globalEq, ctxtFcExactHOL, panToCrepMakeVmapHOLExact, mkCtxtExactHOL, maxList]

/-- A supported singleton generates a scalar Crep callee. -/
theorem supportedCallee_scalar (program : Prog (RiscV.Word 64)) (supported : CallFreeSupported program) :
    ScalarProgram (supportedCallee (progToHOL program)) :=
  supported_compiled_scalar program supported _ (supported_crepPrograms program supported)

end SteppedFlapjack.Concrete
