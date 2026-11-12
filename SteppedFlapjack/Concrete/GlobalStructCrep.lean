import SteppedFlapjack.Concrete.GlobalStructWitness
import SteppedFlapjack.PanToCrepSteps.ConcreteDeclInitial
import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Assembly
import SteppedFlapjack.CrepSteps.BranchStatic
import SteppedFlapjack.CrepToLoopSteps.ScalarProgram
import SteppedFlapjack.PanToCrepSteps.GlobalFrontend
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

/-- The witness is an instance of the general source globals fragment. -/
theorem globalStruct_sourceFrontend : GlobalFrontend globalStructContext globalStructCrepContext
    (progToHOL globalStructWitness) := by
  simp only [globalStructWitness,progToHOL,expToHOL]
  apply GlobalFrontend.seq
  · apply GlobalFrontend.assignGlobalStruct
    · simpa using globalStruct_pairLookup
    · intro e member
      simp [expToHOL] at member
      rcases member with rfl | rfl <;> exact .local (.const _)
  · exact .ret (.globalField (ofString "pair") 16 1 2 (by decide) globalStruct_pairLookup)

/-- The actual globals pass lowers the source fragment to the shared frontend. -/
theorem globalStruct_frontend : FrontendProgram globalStructCrepContext
    (compileProgExactHOL globalStructContext (progToHOL globalStructWitness)) :=
  globalFrontend_compiled globalStruct_sourceFrontend

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
theorem globalStruct_initializer_run_clock (clock : Nat) :
    ({globalStructTarget with clock := clock}).evaluateHOLFiniteState
      (nestedSeqHOL (compileDecsExactHOL globalStructStart
        (fpermDecsHOL (ofString "main") (newMainNameHOL globalStructProgram)
          (resortDeclsHOL globalStructProgram))).1) = (none,{globalStructTarget with clock := clock}) := by
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
    (progToHOL globalStructWitness) globalStruct_function_found funs exns ctx compiled shape notInline (concreteDeclCrepState globalStructTarget [])
  refine ⟨h,?_⟩
  simpa only [initsEq] using eq



end SteppedFlapjack.Concrete
