import SteppedFlapjack.Concrete.GlobalStructCallee
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

theorem globalStruct_initializer_context (ctxt : PanToCrepContextExact 64) (vmax : ctxt.vmax = 0) :
    compileProgExactHOLW ctxt (nestedSeqHOL (compileDecsExactHOL globalStructStart
      (fpermDecsHOL (ofString "main") (newMainNameHOL globalStructProgram) (resortDeclsHOL globalStructProgram))).1) =
    compileProgExactHOLW globalStructCrepContext (nestedSeqHOL (compileDecsExactHOL globalStructStart
      (fpermDecsHOL (ofString "main") (newMainNameHOL globalStructProgram) (resortDeclsHOL globalStructProgram))).1) := by
  rw [globalStruct_actual_initializer_eq]
  simp [compileProgExactHOLW,compileStoreExactHOLW,compileExpExactHOLW,
    compileExpExactHOLWList,sizeOfShapeHOL,sizeOfShapesHOL,nestedDecsHOL,
    globalStructCrepContext,mkCtxtExactHOL,vmax]

def globalStructCallPrograms := compileProgDeclsHOLW (compileTopExactHOL globalStructProgram (ofString "main"))
def globalStructCallPan := {globalStructTarget with clock := 1}
def globalStructCallCrep := concreteDeclCrepState globalStructCallPan globalStructCallPrograms

def globalStructActualInit : CrepProgHOL 64 := compileProgExactHOLW globalStructCrepContext
    (nestedSeqHOL (compileDecsExactHOL globalStructStart
      (fpermDecsHOL (ofString "main") (newMainNameHOL globalStructProgram) (resortDeclsHOL globalStructProgram))).1)
/-- The executable source wrapper matches the actual generated entry. -/
def pairWrapper : Prog (RiscV.Word 64) :=
  .seq (.seq (.assign .global "pair" (.rStruct [.const 0,.const 0])) .skip)
    (.call none (toStringOfBytes (newMainNameHOL globalStructProgram)) [])

theorem pairWrapper_supported : GlobalCallSupportedIn pairShapeMap [] pairWrapper := by
  unfold pairWrapper
  refine .seq (.seq (.assignGlobalStruct "pair" [.one,.one] (by simp [pairShapeMap]) ?_) (.base .skip)) (.tail _ [] (by simp))
  intro e member
  simp at member
  rcases member with rfl | rfl; exact .scalar (.local (.const _))

theorem pairWrapper_lowered : compileProgExactHOL globalStructContext (progToHOL pairWrapper) =
    .seq (.seq (.store (.op .sub [.topAddr,.const 16]) (.rstruct [.const 0,.const 0])) .skip)
      (.call none (newMainNameHOL globalStructProgram) []) := by
  simp only [pairWrapper,progToHOL,expToHOL,compileProgExactHOL,compileExpExactHOL,
    compileExpExactHOLList,globalStruct_pairLookup,ofString_toStringOfBytes,List.map]
theorem pairWrapper_compiled : compileProgExactHOLW globalStructCrepContext
    (compileProgExactHOL globalStructContext (progToHOL pairWrapper)) =
      .seq globalStructActualInit (.call none (newMainNameHOL globalStructProgram) []) := by
  rw [pairWrapper_lowered, ← globalStruct_actual_initializer_eq]
  simp [compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,globalStructActualInit]


theorem pairWrapper_Supported : Supported pairShapeMap pairWrapper := by
  refine ⟨pairWrapper_supported,?_⟩
  simp only [pairWrapper,ProgByteRanged,ExpByteRanged,ListExpByteRanged,and_true]
  exact ⟨by decide,nameRanged_toStringOfBytes_bridge _,by simp⟩


def globalStructActualBody : CrepProgHOL 64 :=
  compileProgExactHOLW globalStructCrepContext (compileProgExactHOL globalStructContext (progToHOL globalStructWitness))

end SteppedFlapjack.Concrete
