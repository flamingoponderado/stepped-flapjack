import SteppedFlapjack.Concrete.GlobalStructActualLoop
import SteppedFlapjack.Concrete.CountedSpan
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.LoopSemStateFiniteExact
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopLiveSteps SteppedFlapjack.LoopToWordSteps

def globalStructActualEntryCrep : CrepProgHOL 64 := .seq globalStructActualInit (.call none (newMainNameHOL globalStructProgram) [])
def globalStructActualEntryLoop : HolLoopProg 64 := compileHOLExact globalStructActualLoopContext .ln globalStructActualEntryCrep

theorem globalStruct_actualEntry_simp : crepSimpProgHOL globalStructActualEntryCrep = globalStructActualEntryCrep := by
  unfold globalStructActualEntryCrep
  rw [← globalStruct_actualPan_compiled]
  exact callFrontend_simp_fixed globalStruct_actualPan_shape

theorem globalStruct_actualLoop_first : ∃ tail,
    compileProgHOLExact riscvConfig.isa globalStructCallPrograms =
      (firstLoopName,[],optimiseHOL globalStructActualEntryLoop) :: tail := by
  have h := firstCrep_loopEntry riscvConfig.isa (ofString "main") globalStructActualEntryCrep
    [(newMainNameHOL globalStructProgram,[],globalStructActualBody)] globalStruct_actualEntry_simp
  simpa [globalStruct_actualPrograms_eq,globalStructActualLoopContext,globalStructActualEntryLoop,
    globalStructActualEntryCrep] using h


end SteppedFlapjack.Concrete
