import SteppedFlapjack.Concrete.SourceState
import SteppedFlapjack.Concrete.GlobalShapes
import SteppedFlapjack.PanToCrepSteps.CountedGlobalAssign
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

/-- Global lowering reserves two words below the existing init-e heap endpoint. -/
def globalStructSourceTop : BitVec 64 := heapTop - 16

def globalStructSourceDomain (a : BitVec 64) : Prop :=
  ordinaryAddress a ∧ a.toNat < globalStructSourceTop.toNat

instance (a : BitVec 64) : Decidable (globalStructSourceDomain a) := by
  unfold globalStructSourceDomain
  infer_instance

def globalStructBase : PanSemStateFiniteExact 64 Unit :=
  {sourceTemplate with topAddr := globalStructSourceTop, memaddrs := globalStructSourceDomain}

def globalStructProductionBase (body : ProgHOL 64) : PanSemState (RiscV.Word 64) (FfiState Unit) :=
  {executableState body with topAddress := globalStructSourceTop, memaddrs := fun a => decide (globalStructSourceDomain a)}

def globalStructExactBase (body : ProgHOL 64) : PanSemStateFiniteExact 64 Unit :=
  {exactState body with topAddr := globalStructSourceTop, memaddrs := globalStructSourceDomain}

def globalStructInitial : PanSemState (RiscV.Word 64) (FfiState Unit) :=
  {sourceProduction with topAddress := globalStructSourceTop, memaddrs := fun a => decide (globalStructSourceDomain a), globals := updatePanValueMap sourceProduction.globals "pair" (.rStruct [.word 0,.word 0])}

theorem globalStructBase_related (body : ProgHOL 64) :
    PanSemStateRelExec (globalStructProductionBase body) (globalStructExactBase body).toExact := by
  obtain ⟨hl,hg,hs,hc,he,hm,hmd,hsm,hck,hbe,hffi,hb,ht⟩ := source_related body
  refine ⟨hl,hg,hs,hc,he,?_,?_,hsm,hck,hbe,hffi,hb,rfl⟩
  · intro a _; rfl
  · intro a; simp [globalStructProductionBase,globalStructExactBase]

/-- The global pair is present in related executable and HOL source states. -/
theorem globalStructInitial_related (body : ProgHOL 64) :
    PanSemStateRelExec
      {globalStructProductionBase body with globals := updatePanValueMap (globalStructProductionBase body).globals "pair" (.rStruct [.word 0,.word 0])}
      (setGlobalHOLFinite (ofString "pair") (panValueToHOL (.rStruct [.word 0,.word 0])) (globalStructExactBase body)).toExact := by
  exact (globalStructBase_related body).updateGlobals "pair" (by decide) _

theorem globalStructInitial_ranged (body : ProgHOL 64) :
    PanSemStateRelExecRanged
      {globalStructProductionBase body with globals := updatePanValueMap (globalStructProductionBase body).globals "pair" (.rStruct [.word 0,.word 0])} := by
  have ranged : PanSemStateRelExecRanged (globalStructProductionBase body) := by
    simpa [globalStructProductionBase,PanSemStateRelExecRanged] using source_ranged body
  exact ranged.updateGlobals "pair" _ (by simp [PanValueByteRanged])

/-- Updating the pair preserves the executable/HOL source relation. -/
theorem globalStructUpdate_related (body : ProgHOL 64) :
    PanSemStateRelExec
      {{globalStructProductionBase body with globals := updatePanValueMap (globalStructProductionBase body).globals "pair" (.rStruct [.word 0,.word 0])} with
        globals := updatePanValueMap (updatePanValueMap (globalStructProductionBase body).globals "pair" (.rStruct [.word 0,.word 0])) "pair" (.rStruct [.word 7,.word 8])}
      (setGlobalHOLFinite (ofString "pair") (panValueToHOL (.rStruct [.word 7,.word 8]))
        (setGlobalHOLFinite (ofString "pair") (panValueToHOL (.rStruct [.word 0,.word 0])) (globalStructExactBase body))).toExact := by
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
  setGlobalHOLFinite (ofString "pair") (panValueToHOL (.rStruct [.word 0,.word 0])) globalStructBase

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
      globalStructHOL,globalStructBase,sourceTemplate,setGlobalHOLFinite,setKvarHOLFinite,isValidValueHOLFinite,
      lookupKvarHOLExact,FUPDATE,
      shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL,emptyLocalsHOLFinite]
  · rw [show progToHOL globalStructWitness = .seq (.assign .global (ofString "pair") (.rstruct [.const 7,.const 8])) (.return (.rfield 1 (.var .global (ofString "pair")))) from by simp [globalStructWitness,progToHOL,expToHOL], SteppedFlapjack.PanToCrepSteps.controlSteps_seq]
    simp [evaluateHOLFiniteState_assign,evalHOLExact,
      evalListHOLExact,globalStructHOL,globalStructBase,sourceTemplate,setGlobalHOLFinite,setKvarHOLFinite,
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

def globalStructTarget : PanSemStateFiniteExact 64 Unit := sourceTemplate

theorem globalStructTarget_layout :
    globalStructTarget.topAddr - 16 = globalStructHOL.topAddr ∧
    globalStructTarget.memaddrs globalStructSourceTop ∧ globalStructTarget.memaddrs (globalStructSourceTop + 8) ∧
    ¬ globalStructTarget.memaddrs globalStructTarget.topAddr ∧
    globalStructTarget.memory globalStructSourceTop = .word 0 ∧ globalStructTarget.memory (globalStructSourceTop + 8) = .word 0 := by
  simp only [globalStructTarget,globalStructHOL,globalStructBase,sourceTemplate,setGlobalHOLFinite,HolWordLab.word.injEq]
  decide

theorem globalStructSlots_disjoint (slot : BitVec 64) (h : globalStructSourceDomain slot) :
    ¬ addresses globalStructSourceTop 2 slot := by
  intro hs
  rw [mem_addresses] at hs
  obtain ⟨i,hi,heq⟩ := hs
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with rfl | rfl
  · have eq : slot = globalStructSourceTop := by simpa [bytesInWord] using heq
    subst slot
    exact (by decide : ¬ globalStructSourceDomain globalStructSourceTop) h
  · have eq : slot = globalStructSourceTop + 8 := by simpa [bytesInWord] using heq
    subst slot
    exact (by decide : ¬ globalStructSourceDomain (globalStructSourceTop + 8)) h

def globalStructKnownCtx : PanGlobalsContextExact 64 :=
  {globals := HolFiniteMapExact.empty.updateEq (ofString "pair",(.comb [.one,.one],16)),
   globalsSize := 16, maxGlobalsSize := 16}

theorem globalStructContext_eq : globalStructContext = globalStructKnownCtx := by
  simp [globalStructContext,globalStructStart,globalStructDecl,globalStructKnownCtx,
    compileDecsExactHOL,compileDecsGlobalAddressExact_eq,sizeOfShapeHOL,cakeBytesInWord]

theorem globalStructTarget_aligned : panGlobalsByteAlignedHOL heapTop := by
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
      simp [globalStructHOL,globalStructBase,sourceTemplate,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] at found
      subst value
      refine ⟨16,?_,?_,?_,?_,?_⟩
      · simp [globalStructKnownCtx,HolFiniteMapExact.lookup_updateEq,FUPDATE_HOL,shapeOfHOLExact]
      · simp [shapeOfHOLExact,isWfShapeNilHOL,isWfShapeExactHOL]
      · rw [globalStructTarget_layout.1]
        have top : globalStructHOL.topAddr = globalStructSourceTop := rfl
        rw [top]
        have hsecond : globalStructTarget.memaddrs (globalStructSourceTop + (8#64)) := globalStructTarget_layout.2.2.1
        have hword : globalStructTarget.memory (globalStructSourceTop + (8#64)) = .word 0 := globalStructTarget_layout.2.2.2.2.2
        simp [shapeOfHOLExact,memLoadHOLExact,memLoadsHOLExact,bytesInWordHOL,
          globalStructTarget_layout.2.1,hsecond,globalStructTarget_layout.2.2.2.2.1,hword]
      · intro slot member
        change globalStructSourceDomain slot at member
        simp only [shapeOfHOLExact,sizeOfShapeHOL,sizeOfShapesHOL,List.map_cons,List.map_nil]
        change ¬ addresses (globalStructTarget.topAddr - 16) 2 slot
        rw [globalStructTarget_layout.1]
        exact globalStructSlots_disjoint slot member
      · simp [panGlobalsByteAlignedHOL,panByteAlignHOL]
    · simp [globalStructHOL,globalStructBase,sourceTemplate,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm same] at found
  · intro name shape address found
    by_cases same : name = ofString "pair"
    · subst name
      simp [globalStructKnownCtx,HolFiniteMapExact.lookup_updateEq,FUPDATE_HOL] at found
      obtain ⟨rfl,rfl⟩ := found
      decide
    · simp [globalStructKnownCtx,HolFiniteMapExact.lookup_updateEq,FUPDATE_HOL,same] at found
  · intro address h; exact h.1
  · rfl
  · intro address h; rfl
  · rfl
  · intro function parameters program returnShape found
    simp [globalStructHOL,globalStructBase,sourceTemplate,setGlobalHOLFinite,HolFiniteMapExact.empty] at found
  · intro name name' shape address shape' address' distinct found found' entry entry' slot
    by_cases same : name = ofString "pair"
    · by_cases same' : name' = ofString "pair"
      · exact False.elim (distinct (same.trans same'.symm))
      · simp [globalStructHOL,globalStructBase,sourceTemplate,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm same'] at found'
    · simp [globalStructHOL,globalStructBase,sourceTemplate,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm same] at found
  · exact globalStructTarget_layout.2.2.2.1
  · change panGlobalsByteAlignedHOL heapTop
    exact globalStructTarget_aligned
  · right; rfl

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
theorem globalStruct_stateRel_clock (clock : Nat) :
    panGlobalsStateRelHOLExact true globalStructContext {globalStructHOL with clock := clock} {globalStructTarget with clock := clock} := by
  have h := globalStruct_stateRel
  simp only [panGlobalsStateRelHOLExact] at h ⊢
  rcases h with ⟨a,b,c,d,e,_,rest⟩
  exact ⟨a,b,c,d,e,by trivial,rest⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem globalStruct_source_run_clock (clock : Nat) : ∃ final,
    ({globalStructHOL with clock := clock}).evaluateHOLFiniteState (progToHOL globalStructWitness) =
      (some (.returned (.val (.word (8 : BitVec 64)))),final) ∧ final.ffi = sourceFfi := by
  refine ⟨(setGlobalHOLFinite (ofString "pair") (panValueToHOL (.rStruct [.word 7,.word 8]))
    {globalStructHOL with clock := clock}).emptyLocalsHOLFinite,?_,rfl⟩
  simp [globalStructWitness,progToHOL,expToHOL,evaluateHOLFiniteState_seq_line780,
      evaluateHOLFiniteState_assign,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,
      globalStructHOL,globalStructBase,sourceTemplate,setGlobalHOLFinite,setKvarHOLFinite,isValidValueHOLFinite,
      lookupKvarHOLExact,FUPDATE,shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL,emptyLocalsHOLFinite]


open SteppedFlapjack.PanToCrepSteps

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- The concrete global pair assignment satisfies the general counted bridge. -/
theorem pair_assignment_bridge (body : ProgHOL 64) :
    let p := {globalStructProductionBase body with globals := updatePanValueMap (globalStructProductionBase body).globals "pair" (.rStruct [.word 0,.word 0])}
    let s := setGlobalHOLFinite (ofString "pair") (panValueToHOL (.rStruct [.word 0,.word 0])) (globalStructExactBase body)
    evalPanValueFfiProgSteps (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none)
      p.structs [] p.baseAddress p.topAddress panSemBitVec64BytesInWord 1 p.locals p.globals p.memory p.ffi
      (.assign .global "pair" (.rStruct [.const 7,.const 8])) (memoryAccess := some (panSemBitVec64MemoryAccess p)) =
      some (.normal p.locals (updatePanValueMap p.globals "pair" (.rStruct [.word 7,.word 8])) p.memory p.ffi,4) ∧
    s.evaluateHOLFiniteState (.assign .global (ofString "pair") (.rstruct [.const 7,.const 8])) =
      (none,setGlobalHOLFinite (ofString "pair") (panValueToHOL (.rStruct [.word 7,.word 8])) s) ∧
    controlSteps (.assign .global (ofString "pair") (.rstruct [.const 7,.const 8])) s ≤ 4 := by
  let : DecidablePred (setGlobalHOLFinite (ofString "pair") (panValueToHOL (.rStruct [.word 0,.word 0])) (globalStructExactBase body)).memaddrs := by
    change DecidablePred globalStructSourceDomain
    infer_instance
  dsimp only []
  have result := counted_assign_global _ _ (globalStructInitial_related body) (globalStructInitial_ranged body)
    "pair" (by decide) (.rStruct [.const 7,.const 8]) (by simp [ExpByteRanged,ListExpByteRanged])
    (.rStruct [.word 7,.word 8]) (by simp [evalPanSemStateExp_64_eq_previous,evalPanValueExp,evalPanValueExp.evalPanValueExps])
    (by simp [globalStructExactBase,exactState,sourceTemplate,setGlobalHOLFinite,isValidValueHOLFinite,lookupKvarHOLExact,FUPDATE,shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL])
    (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) [] 0
  refine ⟨?_,?_,?_⟩
  · simpa [panValueExpStepCost,panValueExpStepCost.panValueExpsStepCost] using result.1
  · simpa only [expToHOL,List.map] using result.2.1
  · simpa [panValueExpStepCost,panValueExpStepCost.panValueExpsStepCost,expToHOL] using result.2.2.2.2

/-- A concrete arithmetic expression using a global pair field is scalar. -/
example (value : PanValue (RiscV.Word 64))
    (run : evalPanSemStateExp globalStructInitial (.op .add [.rField 1 (.var .global "pair"),.const 1]) = some value) :
    ∃ word, value = .word word := by
  let shapes : VarName → Option ShapeHOL := fun n => (globalStructInitial.globals n).map (fun v => shapeOfHOLExact (panValueToHOL v))
  have layout : shapes "pair" = some (.comb [.one,.one]) := by
    simp [shapes,globalStructInitial,updatePanValueMap,shapeOfHOLExact]
  have path : GlobalRead shapes (.rField 1 (.var .global "pair")) .one :=
    .field (.global "pair" _ (by decide) layout) 1 .one rfl
  have expression : GlobalScalarExpression shapes [] (.op .add [.rField 1 (.var .global "pair"),.const 1]) :=
    .op .add (.global path) (.local (.const _))
  apply globalScalarExpression_word expression globalStructInitial
  · intro name v hv
    simp [globalStructInitial,sourceProduction] at hv
  · intro n hn; rfl
  · exact run

end SteppedFlapjack.Concrete
