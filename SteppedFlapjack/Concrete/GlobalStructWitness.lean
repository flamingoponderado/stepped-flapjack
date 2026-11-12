import SteppedFlapjack.Concrete.SourceState
import SteppedFlapjack.PanValueFfiSemantics
import Flapjack.Pancake.Proofs.PanGlobals.CompileCorrect.Assembly
import Flapjack.Pancake.PanStructs.CompileDeclsExact

/-! A concrete executable witness for a global compound value. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend.StackRemove

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

/-- A complete program with the pair declared before its main function. -/
def globalStructProgram : List (DeclHOL 64) :=
  [globalStructDecl, .function ⟨ofString "main",false,false,[],progToHOL globalStructWitness,.one⟩]

/-- Source simplification preserves the concrete declaration and body. -/
theorem globalStruct_simp_fixed : panSimpDeclsHOL globalStructProgram = globalStructProgram := by
  simp [globalStructProgram,globalStructDecl,globalStructWitness,progToHOL,expToHOL,panSimpDeclsHOL,
    panSimpCompileHOL,seqAssocHOL,smartSeqHOL,retToTailHOL,seqCallRetHOL]

/-- The struct pass retains this already anonymous pair and its field access. -/
theorem globalStruct_structs_fixed :
    Flapjack.Pancake.PanStructs.CompileShapeExact.compileTopExact globalStructProgram = globalStructProgram := by
  simp [globalStructProgram,globalStructDecl,globalStructWitness,progToHOL,expToHOL,
    Flapjack.Pancake.PanStructs.CompileShapeExact.compileTopExact,
    Flapjack.Pancake.PanStructs.CompileShapeExact.getNamesExact,
    Flapjack.Pancake.PanStructs.CompileShapeExact.compileDeclsExact,
    Flapjack.Pancake.PanStructs.CompileShapeExact.compileProgExact,
    Flapjack.Pancake.PanStructs.CompileShapeExact.compileExpExact,
    Flapjack.Pancake.PanStructs.CompileShapeExact.compileExpsExact,
    Flapjack.Pancake.PanStructs.CompileShapeExact.compileShapeExact,
    Flapjack.Pancake.PanStructs.CompileShapeExact.compileShapesExact]

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

def globalStructTarget : PanSemStateFiniteExact 64 Unit :=
  { sourceTemplate with topAddr := heapTop + 16, memaddrs := fun a => ordinaryAddress a ∨ a = heapTop ∨ a = heapTop + 8 }

theorem globalStructTarget_layout :
    globalStructTarget.topAddr - 16 = globalStructHOL.topAddr ∧
    globalStructTarget.memaddrs heapTop ∧ globalStructTarget.memaddrs (heapTop + 8) ∧
    ¬ globalStructTarget.memaddrs globalStructTarget.topAddr ∧
    globalStructTarget.memory heapTop = .word 0 ∧ globalStructTarget.memory (heapTop + 8) = .word 0 := by
  simp only [globalStructTarget,globalStructHOL,sourceTemplate,setGlobalHOLFinite,HolWordLab.word.injEq]
  decide

theorem globalStructSlots_disjoint (slot : BitVec 64) (h : ordinaryAddress slot) :
    ¬ addresses heapTop 2 slot := by
  intro hs
  rw [mem_addresses] at hs
  obtain ⟨i,hi,heq⟩ := hs
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl
  · have eq : slot = heapTop := by simpa [bytesInWord] using heq
    subst slot
    exact (by decide : ¬ ordinaryAddress heapTop) h
  · have eq : slot = heapTop + 8 := by simpa [bytesInWord] using heq
    subst slot
    exact (by decide : ¬ ordinaryAddress (heapTop + 8)) h

def globalStructKnownCtx : PanGlobalsContextExact 64 :=
  {globals := HolFiniteMapExact.empty.updateEq (ofString "pair",(.comb [.one,.one],16)),
   globalsSize := 16, maxGlobalsSize := 16}

theorem globalStructContext_eq : globalStructContext = globalStructKnownCtx := by
  simp [globalStructContext,globalStructStart,globalStructDecl,globalStructKnownCtx,
    compileDecsExactHOL,compileDecsGlobalAddressExact_eq,sizeOfShapeHOL,cakeBytesInWord]

theorem globalStructTarget_aligned : panGlobalsByteAlignedHOL (heapTop + 16) := by
  unfold panGlobalsByteAlignedHOL
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem globalStruct_stateRel : panGlobalsStateRelHOLExact true globalStructContext globalStructHOL globalStructTarget := by
  classical
  rw [globalStructContext_eq]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change globalStructHOL.topAddr = globalStructTarget.topAddr - 16
    exact globalStructTarget_layout.1.symm
  · intro _; rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · intro name value found
    by_cases same : name = ofString "pair"
    · subst name
      simp [globalStructHOL,sourceTemplate,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] at found
      subst value
      refine ⟨16,?_,?_,?_,?_,?_⟩
      · simp [globalStructKnownCtx,HolFiniteMapExact.lookup_updateEq,FUPDATE_HOL,shapeOfHOLExact]
      · simp [shapeOfHOLExact,isWfShapeNilHOL,isWfShapeExactHOL]
      · rw [globalStructTarget_layout.1]
        have top : globalStructHOL.topAddr = heapTop := rfl
        rw [top]
        have hsecond : globalStructTarget.memaddrs (heapTop + (8#64)) := by
          change ordinaryAddress (heapTop + 8) ∨ heapTop + 8 = heapTop ∨ heapTop + 8 = heapTop + 8
          exact Or.inr (Or.inr rfl)
        have hword : globalStructTarget.memory (heapTop + (8#64)) = .word 0 := globalStructTarget_layout.2.2.2.2.2
        simp [shapeOfHOLExact,memLoadHOLExact,memLoadsHOLExact,bytesInWordHOL,
          globalStructTarget_layout.2.1,hsecond,globalStructTarget_layout.2.2.2.2.1,hword]
      · intro slot member
        change ordinaryAddress slot at member
        simp only [shapeOfHOLExact,sizeOfShapeHOL,sizeOfShapesHOL,List.map_cons,List.map_nil]
        change ¬ addresses (globalStructTarget.topAddr - 16) 2 slot
        rw [globalStructTarget_layout.1]
        exact globalStructSlots_disjoint slot member
      · simp [panGlobalsByteAlignedHOL,panByteAlignHOL]
    · simp [globalStructHOL,sourceTemplate,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm same] at found
  · intro name shape address found
    by_cases same : name = ofString "pair"
    · subst name
      simp [globalStructKnownCtx,HolFiniteMapExact.lookup_updateEq,FUPDATE_HOL] at found
      obtain ⟨rfl,rfl⟩ := found
      decide
    · simp [globalStructKnownCtx,HolFiniteMapExact.lookup_updateEq,FUPDATE_HOL,same] at found
  · intro address h; exact Or.inl h
  · rfl
  · intro address h; rfl
  · rfl
  · intro function parameters program returnShape found
    simp [globalStructHOL,sourceTemplate,setGlobalHOLFinite,HolFiniteMapExact.empty] at found
  · intro name name' shape address shape' address' distinct found found' entry entry' slot
    by_cases same : name = ofString "pair"
    · by_cases same' : name' = ofString "pair"
      · exact False.elim (distinct (same.trans same'.symm))
      · simp [globalStructHOL,sourceTemplate,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm same'] at found'
    · simp [globalStructHOL,sourceTemplate,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm same] at found
  · exact globalStructTarget_layout.2.2.2.1
  · change panGlobalsByteAlignedHOL (heapTop + 16)
    exact globalStructTarget_aligned
  · right; rfl

/-- The lowered structured store and return use at most three HOL visits. -/
theorem globalStruct_lowered_visits :
    SteppedFlapjack.PanToCrepSteps.controlSteps
      (compileProgExactHOL globalStructContext (progToHOL globalStructWitness)) globalStructTarget ≤ 3 := by
  rw [globalStructWitness_lowering,SteppedFlapjack.PanToCrepSteps.controlSteps_seq]
  simp only [SteppedFlapjack.PanToCrepSteps.controlSteps.eq_def]
  split <;> simp

/-- The actual global-lowering theorem carries the concrete pair program to
its structured heap implementation, with the resulting states related. -/
theorem globalStruct_lowered_run :
    ∃ sourcePost targetPost,
      globalStructHOL.evaluateHOLFiniteState (progToHOL globalStructWitness) =
        (some (.returned (.val (.word (8 : BitVec 64)))),sourcePost) ∧
      globalStructTarget.evaluateHOLFiniteState (compileProgExactHOL globalStructContext (progToHOL globalStructWitness)) =
        (some (.returned (.val (.word (8 : BitVec 64)))),targetPost) ∧
      panGlobalsStateRelHOLExact (goodResHOL (some (.returned (.val (.word (8 : BitVec 64))))))
        globalStructContext sourcePost targetPost := by
  obtain ⟨sourcePost,sourceRun,_⟩ := globalStructWitness_hol
  obtain ⟨targetPost,targetRun,postRel⟩ := PanGlobalsCompileCorrectAssembly.compileCorrectHOL
    (progToHOL globalStructWitness) globalStructHOL (some (.returned (.val (.word (8 : BitVec 64)))))
    globalStructContext globalStructTarget sourcePost ⟨globalStruct_stateRel,sourceRun,by simp⟩
  exact ⟨sourcePost,targetPost,sourceRun,targetRun,postRel⟩
end SteppedFlapjack.Concrete
