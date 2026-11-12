import SteppedFlapjack.Concrete.SourceState
import SteppedFlapjack.PanValueFfiSemantics

/-! A concrete executable witness for a global compound value. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString

/-- Update a global pair, then return its second component. -/
def globalStructWitness : Prog (RiscV.Word 64) :=
  .seq (.assign .global "pair" (.rStruct [.const 7,.const 8]))
    (.return (.rField 1 (.var .global "pair")))

def globalStructInitial : PanSemState (RiscV.Word 64) (FfiState Unit) :=
  {sourceProduction with globals := updatePanValueMap sourceProduction.globals "pair" (.rStruct [.word 0,.word 0])}

/-- The same global pair is present in related executable and HOL states. -/
theorem globalStructInitial_related (body : ProgHOL 64) :
    PanSemStateRelExec
      {executableState body with globals := updatePanValueMap (executableState body).globals "pair" (.rStruct [.word 0,.word 0])}
      (setGlobalHOLFinite (ofString "pair") (panValueToHOL (.rStruct [.word 0,.word 0])) (exactState body)).toExact := by
  exact (source_related body).updateGlobals "pair" (by decide) _

theorem globalStructInitial_ranged (body : ProgHOL 64) :
    PanSemStateRelExecRanged
      {executableState body with globals := updatePanValueMap (executableState body).globals "pair" (.rStruct [.word 0,.word 0])} := by
  exact (source_ranged body).updateGlobals "pair" _ (by simp [PanValueByteRanged])

/-- The two resulting global updates preserve the same state relation. -/
theorem globalStructUpdate_related (body : ProgHOL 64) :
    PanSemStateRelExec
      {{executableState body with globals := updatePanValueMap (executableState body).globals "pair" (.rStruct [.word 0,.word 0])} with
        globals := updatePanValueMap (updatePanValueMap (executableState body).globals "pair" (.rStruct [.word 0,.word 0])) "pair" (.rStruct [.word 7,.word 8])}
      (setGlobalHOLFinite (ofString "pair") (panValueToHOL (.rStruct [.word 7,.word 8]))
        (setGlobalHOLFinite (ofString "pair") (panValueToHOL (.rStruct [.word 0,.word 0])) (exactState body))).toExact := by
  exact (globalStructInitial_related body).updateGlobals "pair" (by decide) _

theorem globalStructWitness_ranged : ProgByteRanged globalStructWitness := by
  simp [globalStructWitness,ProgByteRanged,ExpByteRanged,NameRanged,ListExpByteRanged]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The global pair update returns its second component in eight source steps. -/
theorem globalStructWitness_run :
    evalPanValueFfiProgSteps (riscv64PanValueFfiContext (fun _ => false))
      (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) [] []
      globalStructInitial.baseAddress globalStructInitial.topAddress 8 10
      globalStructInitial.locals globalStructInitial.globals globalStructInitial.memory globalStructInitial.ffi globalStructWitness
      (memoryAccess := some (panSemBitVec64MemoryAccess globalStructInitial)) (contracts := none) =
        some (.returned globalStructInitial.locals
          (updatePanValueMap globalStructInitial.globals "pair" (.rStruct [.word 7,.word 8]))
          globalStructInitial.memory globalStructInitial.ffi [.word 8],8) := by
  with_unfolding_all rfl

/-- The HOL state corresponding to the concrete initial global pair. -/
def globalStructHOL : PanSemStateFiniteExact 64 Unit :=
  setGlobalHOLFinite (ofString "pair") (panValueToHOL (.rStruct [.word 0,.word 0])) sourceTemplate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- HOL evaluation returns the same second component with an explicit visit bound. -/
theorem globalStructWitness_hol :
    ∃ final, globalStructHOL.evaluateHOLFiniteState (progToHOL globalStructWitness) =
      (some (.returned (.val (.word 8))),final) ∧
      SteppedFlapjack.PanToCrepSteps.controlSteps (progToHOL globalStructWitness) globalStructHOL ≤ 8 := by
  refine ⟨(setGlobalHOLFinite (ofString "pair") (panValueToHOL (.rStruct [.word 7,.word 8])) globalStructHOL).emptyLocalsHOLFinite,?_,?_⟩
  · simp [globalStructWitness,progToHOL,expToHOL,evaluateHOLFiniteState_seq_line780,
      evaluateHOLFiniteState_assign,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,
      globalStructHOL,sourceTemplate,setGlobalHOLFinite,setKvarHOLFinite,isValidValueHOLFinite,
      lookupKvarHOLExact,FUPDATE,
      shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL,emptyLocalsHOLFinite]
  · rw [show progToHOL globalStructWitness = .seq (.assign .global (ofString "pair") (.rstruct [.const 7,.const 8])) (.return (.rfield 1 (.var .global (ofString "pair")))) from by simp [globalStructWitness,progToHOL,expToHOL], SteppedFlapjack.PanToCrepSteps.controlSteps_seq]
    simp [evaluateHOLFiniteState_assign,evalHOLExact,
      evalListHOLExact,globalStructHOL,sourceTemplate,setGlobalHOLFinite,setKvarHOLFinite,
      isValidValueHOLFinite,lookupKvarHOLExact,
      FUPDATE,shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL,SteppedFlapjack.PanToCrepSteps.controlSteps.eq_def]

/-- The pair declaration as seen by the global-lowering compiler. -/
def globalStructDecl : DeclHOL 64 :=
  .decl (.comb [.one,.one]) (ofString "pair") (.rstruct [.const 0,.const 0])

def globalStructStart : PanGlobalsContextExact 64 :=
  {globals := HolFiniteMapExact.empty, globalsSize := 0, maxGlobalsSize := 16}

def globalStructContext : PanGlobalsContextExact 64 :=
  (compileDecsExactHOL globalStructStart [globalStructDecl]).2.2.2

/-- Global lowering allocates the pair in two consecutive words and translates
its update and field read to the corresponding structured heap operations. -/
theorem globalStructWitness_lowering :
    compileProgExactHOL globalStructContext (progToHOL globalStructWitness) =
      .seq (.store (.op .sub [.topAddr,.const 16]) (.rstruct [.const 7,.const 8]))
        (.return (.rfield 1 (.load (.comb [.one,.one]) (.op .sub [.topAddr,.const 16])))) := by
  simp [globalStructContext,globalStructStart,globalStructDecl,globalStructWitness,
    compileDecsExactHOL,compileDecsGlobalAddressExact_eq,compileProgExactHOL,compileExpExactHOL,
    compileExpExactHOLList,progToHOL,expToHOL,sizeOfShapeHOL,cakeBytesInWord,
    HolFiniteMapExact.lookup_updateEq,FUPDATE_HOL]

end SteppedFlapjack.Concrete
