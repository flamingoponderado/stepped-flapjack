import SteppedFlapjack.Concrete.GlobalStructWitness
import SteppedFlapjack.PanToCrepSteps.ConcreteDeclInitial
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Assembly
import SteppedFlapjack.CrepSteps.BranchStatic
import SteppedFlapjack.CrepToLoopSteps.ScalarProgram
import SteppedFlapjack.PanToCrepSteps.GlobalInitializers
import SteppedFlapjack.PanToCrepSteps.GlobalNoInline
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps

def globalStructCrepContext : PanToCrepContextExact 64 :=
  mkCtxtExactHOL HolFiniteMapExact.empty HolFiniteMapExact.empty 0 HolFiniteMapExact.empty

theorem globalStruct_pairLookup : globalStructContext.globals.lookup (ofString "pair") =
    some (.comb [.one,.one],(16 : BitVec 64)) := by
  simp [globalStructContext,globalStructStart,globalStructDecl,compileDecsExactHOL,
    compileDecsGlobalAddressExact_eq,sizeOfShapeHOL,cakeBytesInWord,
    HolFiniteMapExact.lookup_updateEq,FUPDATE_HOL]

theorem globalStruct_field_from_global : FrontendScalar globalStructCrepContext
    (compileExpExactHOL globalStructContext (.rfield 1 (.var .global (ofString "pair")))) := by
  exact globalCompile_globalField globalStructContext globalStructCrepContext (ofString "pair") 16 1 2
    (by decide) globalStruct_pairLookup
/-- The source global field read lowers to a supported frontend scalar. -/
theorem globalStruct_field_frontend :
    FrontendScalar globalStructCrepContext
      (.rfield 1 (.load (.comb [.one,.one]) (.op .sub [.topAddr,.const 16]))) := by
  simpa [compileExpExactHOL,globalStruct_pairLookup] using globalStruct_field_from_global

/-- Global lowering produces a program in the shared structured-store and
field-load frontend fragment. -/
theorem globalStruct_frontend : FrontendProgram globalStructCrepContext
    (compileProgExactHOL globalStructContext (progToHOL globalStructWitness)) := by
  rw [globalStructWitness_lowering]
  apply FrontendProgram.seq
  · apply FrontendProgram.storeStruct (.op .sub .topAddr (.const 16))
    intro e member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact .const _
  · exact .ret globalStruct_field_frontend

/-- The actual renamed declaration initializer uses the general frontend. -/
theorem globalStruct_initializer_frontend (globals : PanGlobalsContextExact 64) :
    FrontendProgram globalStructCrepContext
      (nestedSeqHOL (compileDecsExactHOL globals
        (fpermDecsHOL (ofString "main") (newMainNameHOL globalStructProgram)
          (resortDeclsHOL globalStructProgram))).1) := by
  apply globalCompile_frontend_initializer_sequence
  intro shape name value member
  simp only [globalStructProgram,globalStructDecl,resortDeclsHOL,isNameHOL,isExnDeclHOL,
    isDeclHOL,isFunctionHOL,List.filter_cons,List.filter_nil,if_true,if_false,Bool.false_eq_true,List.nil_append,
    List.cons_append,List.append_nil,fpermDecsHOL,List.mem_cons,List.not_mem_nil,or_false,
    DeclHOL.decl.injEq] at member
  rcases member with ⟨rfl,rfl,rfl⟩ | impossible
  · apply FrontendInitializer.flatStruct
    intro e member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact .const _
  · cases impossible

/-- The compiled declaration initializer has a code-derived visit bound and
satisfies the Crep-to-Loop shape invariant. -/
theorem globalStruct_initializer_compiled (globals : PanGlobalsContextExact 64)
    (state : CrepSemHOLState 64 Unit) :
    let program := compileProgExactHOLW globalStructCrepContext
      (nestedSeqHOL (compileDecsExactHOL globals
        (fpermDecsHOL (ofString "main") (newMainNameHOL globalStructProgram)
          (resortDeclsHOL globalStructProgram))).1)
    SteppedFlapjack.CrepToLoopSteps.ScalarProgram program ∧
      SteppedFlapjack.CrepSteps.steps program state ≤ SteppedFlapjack.CrepSteps.statementWeight program := by
  have h := globalStruct_initializer_frontend globals
  exact ⟨SteppedFlapjack.CrepToLoopSteps.frontend_scalar_program h,
    SteppedFlapjack.CrepSteps.staticProgram_statementWeight
      (frontendLoopFree_static h (globalCompile_initializers_noWhile
        (fpermDecsHOL (ofString "main") (newMainNameHOL globalStructProgram)
          (resortDeclsHOL globalStructProgram)) globals)) state⟩

/-- Writing the value already in a valid memory slot preserves memory. -/
private theorem panMemStore_same {width : Nat} [NeZero width] (address : BitVec width)
    (domain : BitVec width → Prop) [DecidablePred domain] (memory : BitVec width → HolWordLab width)
    (h : domain address) : panMemStoreHOL address (memory address) domain memory = some memory := by
  rw [panMemStoreHOL_hit _ _ _ _ h]
  congr 1
  funext current
  split <;> simp_all

theorem globalStruct_actual_initializer_eq :
    nestedSeqHOL (compileDecsExactHOL globalStructStart
      (fpermDecsHOL (ofString "main") (newMainNameHOL globalStructProgram)
        (resortDeclsHOL globalStructProgram))).1 =
      .seq (.store (.op .sub [.topAddr,.const 16]) (.rstruct [.const 0,.const 0])) .skip := by
  simp only [globalStructProgram,globalStructDecl,resortDeclsHOL,isNameHOL,isExnDeclHOL,
    isDeclHOL,isFunctionHOL,List.filter_cons,List.filter_nil,if_true,if_false,Bool.false_eq_true,List.nil_append,
    List.cons_append,List.append_nil,fpermDecsHOL]
  simp [compileDecsExactHOL,globalStructStart,compileDecsGlobalAddressExact_eq,
    sizeOfShapeHOL,cakeBytesInWord,nestedSeqHOL,compileExpExactHOL,compileExpExactHOLList]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem globalStruct_initializer_run :
    globalStructTarget.evaluateHOLFiniteState
      (nestedSeqHOL (compileDecsExactHOL globalStructStart
        (fpermDecsHOL (ofString "main") (newMainNameHOL globalStructProgram)
          (resortDeclsHOL globalStructProgram))).1) = (none,globalStructTarget) := by
  classical
  have hm1 : panMemStoreHOL globalStructSourceTop (.word 0) globalStructTarget.memaddrs globalStructTarget.memory =
      some globalStructTarget.memory := by
    simpa [globalStructTarget_layout.2.2.2.2.1] using
      panMemStore_same globalStructSourceTop globalStructTarget.memaddrs globalStructTarget.memory globalStructTarget_layout.2.1
  have hm2 : panMemStoreHOL (globalStructSourceTop + 8) (.word 0) globalStructTarget.memaddrs globalStructTarget.memory =
      some globalStructTarget.memory := by
    simpa only [globalStructTarget_layout.2.2.2.2.2] using
      panMemStore_same (globalStructSourceTop + 8) globalStructTarget.memaddrs globalStructTarget.memory globalStructTarget_layout.2.2.1
  change panMemStoreHOL globalStructSourceTop (.word (BitVec.ofNat 64 0)) globalStructTarget.memaddrs globalStructTarget.memory = some globalStructTarget.memory at hm1
  change panMemStoreHOL (globalStructSourceTop + BitVec.ofNat 64 8) (.word (BitVec.ofNat 64 0)) globalStructTarget.memaddrs globalStructTarget.memory = some globalStructTarget.memory at hm2
  have top : globalStructTarget.topAddr - 16 = globalStructSourceTop := by
    simpa [globalStructHOL,globalStructBase,setGlobalHOLFinite] using globalStructTarget_layout.1
  have topOp : wordOpHOL .sub [globalStructTarget.topAddr,(16 : BitVec 64)] = some globalStructSourceTop := by
    simpa [wordOpHOL,wordOp] using congrArg some top
  change wordOpHOL .sub [globalStructTarget.topAddr, BitVec.ofNat 64 16] = some globalStructSourceTop at topOp
  rw [globalStruct_actual_initializer_eq, evaluateHOLFiniteState_seq_line780]
  simp [evaluateHOLFiniteState_store,evalHOLExact,evalListHOLExact,
    flattenHOL,panMemStoresHOL,panBytesInWord,valueIsWord,valueWord,topOp,hm1,hm2]


theorem globalStruct_initializer_visits :
    controlSteps (nestedSeqHOL (compileDecsExactHOL globalStructStart
      (fpermDecsHOL (ofString "main") (newMainNameHOL globalStructProgram)
        (resortDeclsHOL globalStructProgram))).1) globalStructTarget ≤ 3 := by
  rw [globalStruct_actual_initializer_eq,controlSteps_seq]
  simp only [controlSteps.eq_def]
  split <;> simp


theorem globalStruct_initialized_body_visits :
    controlSteps (.seq (nestedSeqHOL (compileDecsExactHOL globalStructStart
      (fpermDecsHOL (ofString "main") (newMainNameHOL globalStructProgram)
        (resortDeclsHOL globalStructProgram))).1)
      (compileProgExactHOL globalStructContext (progToHOL globalStructWitness))) globalStructTarget ≤ 7 := by
  rw [controlSteps_seq,globalStruct_initializer_run]
  simp only
  have first := globalStruct_initializer_visits
  have second := globalStruct_lowered_visits
  omega

/-- The real initializer followed by the lowered body returns the source value. -/
theorem globalStruct_initialized_body_run : ∃ sourcePost targetPost,
    globalStructHOL.evaluateHOLFiniteState (progToHOL globalStructWitness) =
      (some (.returned (.val (.word (8 : BitVec 64)))),sourcePost) ∧
    globalStructTarget.evaluateHOLFiniteState
      (.seq (nestedSeqHOL (compileDecsExactHOL globalStructStart
        (fpermDecsHOL (ofString "main") (newMainNameHOL globalStructProgram)
          (resortDeclsHOL globalStructProgram))).1)
        (compileProgExactHOL globalStructContext (progToHOL globalStructWitness))) =
      (some (.returned (.val (.word (8 : BitVec 64)))),targetPost) ∧
    panGlobalsStateRelHOLExact (goodResHOL (some (.returned (.val (.word (8 : BitVec 64))))))
      globalStructContext sourcePost targetPost := by
  obtain ⟨sourcePost,targetPost,sourceRun,targetRun,rel⟩ := globalStruct_lowered_run
  refine ⟨sourcePost,targetPost,sourceRun,?_,rel⟩
  rw [evaluateHOLFiniteState_seq_line780, globalStruct_initializer_run]
  exact targetRun



/-- Initialize the real global slots, then run the lowered body. -/
def globalStructInitializedProgram : ProgHOL 64 :=
  .seq (nestedSeqHOL (compileDecsExactHOL globalStructStart
    (fpermDecsHOL (ofString "main") (newMainNameHOL globalStructProgram)
      (resortDeclsHOL globalStructProgram))).1)
    (compileProgExactHOL globalStructContext (progToHOL globalStructWitness))

def globalStructCrepProgram : CrepProgHOL 64 :=
  compileProgExactHOLW globalStructCrepContext globalStructInitializedProgram

def globalStructCrepState : CrepSemHOLState 64 Unit := concreteDeclCrepState globalStructTarget []

theorem globalStruct_initialized_frontend : FrontendProgram globalStructCrepContext globalStructInitializedProgram :=
  .seq (globalStruct_initializer_frontend globalStructStart) globalStruct_frontend

def globalStructCrepLimit : Nat := SteppedFlapjack.CrepSteps.statementWeight globalStructCrepProgram

theorem globalStruct_crep_visits : SteppedFlapjack.CrepSteps.steps globalStructCrepProgram globalStructCrepState ≤ globalStructCrepLimit := by
  apply SteppedFlapjack.CrepSteps.staticProgram_statementWeight
  apply frontendLoopFree_static globalStruct_initialized_frontend
  unfold globalStructInitializedProgram
  rw [globalStruct_actual_initializer_eq,globalStructWitness_lowering]
  rfl

/-- Initialization and the global-pair body reach Crep at a code-derived visit bound. -/
theorem globalStruct_crep_run : ∃ sourcePost targetPost crepPost,
    globalStructHOL.evaluateHOLFiniteState (progToHOL globalStructWitness) =
      (some (.returned (.val (.word (8 : BitVec 64)))),sourcePost) ∧
    globalStructTarget.evaluateHOLFiniteState (compileProgExactHOL globalStructContext (progToHOL globalStructWitness)) =
      (some (.returned (.val (.word (8 : BitVec 64)))),targetPost) ∧
    evalCrepSemHOLProgExact globalStructCrepState globalStructCrepProgram =
        (some (.return [.word 8]),crepPost) ∧ panToCrepStateRelFiniteExact targetPost crepPost ∧
      SteppedFlapjack.CrepSteps.steps globalStructCrepProgram globalStructCrepState ≤ globalStructCrepLimit := by
  obtain ⟨sourcePost,targetPost,sourceRun,targetRun,_⟩ := globalStruct_lowered_run
  have initialized : globalStructTarget.evaluateHOLFiniteState globalStructInitializedProgram =
      (some (.returned (.val (.word (8 : BitVec 64)))),targetPost) := by
    unfold globalStructInitializedProgram
    rw [evaluateHOLFiniteState_seq_line780,globalStruct_initializer_run]
    exact targetRun
  have stateRel : panToCrepStateRelFiniteExact globalStructTarget globalStructCrepState := by
    exact concreteDecl_panCrep_stateRel globalStructTarget [] rfl rfl
  have codeRel : codeRelExactHOLW globalStructCrepContext globalStructTarget.code globalStructCrepState.code := by
    simp [codeRelExactHOLW,globalStructTarget,sourceTemplate,HolFiniteMapExact.lookup_empty]
  have excpRel : panToCrepExcpRelFiniteExact globalStructCrepContext.eids globalStructTarget.eshapes := by
    simpa [globalStructCrepContext,mkCtxtExactHOL,globalStructTarget,sourceTemplate] using (empty_panCrep_exceptions (width := 64))
  have localsRel : panToCrepLocalsRelFiniteExact globalStructCrepContext globalStructTarget.locals globalStructCrepState.locals := by
    apply empty_panCrep_locals
    rfl
  obtain ⟨result,crepPost,crepRun,postState,_,_,resultRel⟩ := pcCompileCorrect
    globalStructInitializedProgram globalStructTarget
    (some (.returned (.val (.word (8 : BitVec 64))))) targetPost globalStructCrepState globalStructCrepContext
    ⟨initialized,by simp,stateRel,codeRel,excpRel,localsRel,frontendProgram_localised globalStruct_initialized_frontend⟩
  have resultEq : result = some (.return [.word 8]) := by simpa [pcCompileCorrectResultRel,flattenHOL] using resultRel
  subst result
  refine ⟨sourcePost,targetPost,crepPost,sourceRun,targetRun,?_,postState,globalStruct_crep_visits⟩
  simpa [globalStructCrepProgram,flattenHOL] using crepRun

theorem globalStruct_noInline :
    (functionsHOL ((compileTopExactHOL globalStructProgram (ofString "main")).filter inlinableHOL)).map Prod.fst = [] := by
  rw [compileTop_noInline globalStructProgram (by simp [globalStructProgram,globalStructDecl,inlinableHOL])]
  rfl

theorem globalStruct_initializer_branch (ctxt : PanToCrepContextExact 64) :
    SteppedFlapjack.CrepToLoopSteps.BranchProgram (compileProgExactHOLW ctxt
      (nestedSeqHOL (compileDecsExactHOL globalStructStart
        (fpermDecsHOL (ofString "main") (newMainNameHOL globalStructProgram)
          (resortDeclsHOL globalStructProgram))).1)) := by
  rw [globalStruct_actual_initializer_eq]
  simp [compileProgExactHOLW,compileStoreExactHOLW,compileExpExactHOLW,
    compileExpExactHOLWList,sizeOfShapeHOL,sizeOfShapesHOL,nestedDecsHOL,cexpHeads]
  simp [List.range_succ,List.range_zero,nestedDecsHOL,crepNestedSeqHOL,storesHOL,Function.comp_def]
  repeat' first | apply SteppedFlapjack.CrepToLoopSteps.BranchProgram.seq | apply SteppedFlapjack.CrepToLoopSteps.BranchProgram.dec | apply SteppedFlapjack.CrepToLoopSteps.BranchProgram.expr
                | apply ExprProgram.store | apply ExprProgram.leaf | apply DirectExpression.op
                | apply DirectExpression.topAddr | apply DirectExpression.const | apply DirectExpression.var | constructor

theorem globalStruct_initialContext :
    let renamed := fpermDecsHOL (ofString "main") (newMainNameHOL globalStructProgram) (resortDeclsHOL globalStructProgram)
    ({globals := HolFiniteMapExact.empty, globalsSize := 0,
      maxGlobalsSize := cakeBytesInWord 64 * BitVec.ofNat 64 ((decShapesHOL renamed).map sizeOfShapeHOL).sum} : PanGlobalsContextExact 64) = globalStructStart := by
  simp only [globalStructProgram,globalStructDecl,resortDeclsHOL,isNameHOL,isExnDeclHOL,
    isDeclHOL,isFunctionHOL,List.filter_cons,List.filter_nil,if_true,if_false,Bool.false_eq_true,List.nil_append,
    List.cons_append,List.append_nil,fpermDecsHOL,decShapesHOL,List.map_cons,List.map_nil,
    List.sum_cons,List.sum_nil,sizeOfShapeHOL,sizeOfShapesHOL,globalStructStart,cakeBytesInWord]
  rfl

theorem globalStruct_function_found : (functionsHOL globalStructProgram).lookup (ofString "main") =
    some ([],progToHOL globalStructWitness,.one) := by
  simp [globalStructProgram,globalStructDecl,functionsHOL]


/-- The actual compiler retains the global initializer followed by a tail call. -/
theorem globalStruct_actualCrep_entry :
    let lowered := compileTopExactHOL globalStructProgram (ofString "main")
    let ctxt := mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
      (makeFuncsExactHOL (functionsHOL lowered)) (sizeOfShapeHOL (.comb [])-1)
      (getEidsFromDeclsHOL lowered)
    let init := compileProgExactHOLW ctxt (nestedSeqHOL (compileDecsExactHOL globalStructStart
      (fpermDecsHOL (ofString "main") (newMainNameHOL globalStructProgram) (resortDeclsHOL globalStructProgram))).1)
    ∃ h : 0 < (compileProgDeclsHOLW lowered).length,
      (compileProgDeclsHOLW lowered)[0]'h =
        (ofString "main",[],.seq init (.call none (newMainNameHOL globalStructProgram) [])) := by
  obtain ⟨inits,funs,exns,ctx,compiled,top⟩ := compileTop_entry_wrapper globalStructProgram (ofString "main") []
    (progToHOL globalStructWitness) .one globalStruct_function_found
  have actual := compiled
  rw [globalStruct_initialContext] at actual
  have initsEq : (compileDecsExactHOL globalStructStart
      (fpermDecsHOL (ofString "main") (newMainNameHOL globalStructProgram) (resortDeclsHOL globalStructProgram))).1 = inits := by
    rw [actual]
  let ctxt := mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
    (makeFuncsExactHOL (functionsHOL (compileTopExactHOL globalStructProgram (ofString "main"))))
    (sizeOfShapeHOL (.comb [])-1) (getEidsFromDeclsHOL (compileTopExactHOL globalStructProgram (ofString "main")))
  have shape : SteppedFlapjack.CrepToLoopSteps.BranchProgram (compileProgExactHOLW ctxt (nestedSeqHOL inits)) := by
    rw [← initsEq]
    exact globalStruct_initializer_branch ctxt
  have notInline : newMainNameHOL globalStructProgram ∉
      (functionsHOL ((compileTopExactHOL globalStructProgram (ofString "main")).filter inlinableHOL)).map Prod.fst := by
    rw [globalStruct_noInline]
    simp
  obtain ⟨h,eq,_⟩ := globalEntry_nonInline_preserved globalStructProgram (ofString "main") inits .one
    (progToHOL globalStructWitness) globalStruct_function_found funs exns ctx compiled shape notInline globalStructCrepState
  refine ⟨h,?_⟩
  simpa only [initsEq] using eq



end SteppedFlapjack.Concrete
