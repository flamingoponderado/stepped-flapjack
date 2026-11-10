import SteppedFlapjack.PanToCrepSteps.SingleEntryGlobals
import Flapjack.Pancake.Proofs.PanToTarget.ExecutableCompileDefinitions
import Flapjack.Pancake.CrepInline.InlineRouteBridge

/-! Structural facts about the actual countdown compiler pipeline. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm

/-- A single entry named main is renamed to the first fresh variant. -/
theorem singleEntry_main_freshName (body : ProgHOL 64) :
    newMainNameHOL (singleEntryProgram (ofString "main") body) = ofString "main'" := by
  simp [newMainNameHOL,singleEntryProgram,functionsHOL,freshNameMlS,mlstrAppend,ofString]

end SteppedFlapjack.PanToCrepSteps
