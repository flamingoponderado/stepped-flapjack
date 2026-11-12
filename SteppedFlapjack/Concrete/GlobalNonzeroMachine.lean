import SteppedFlapjack.Concrete.GlobalNonzeroNativeFacts
import SteppedFlapjack.Concrete.FunctionSource
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.StackRemove SteppedFlapjack.PanToCrepSteps
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private def funName : String := "main" ++ String.singleton (Char.ofNat 39)
private def prog : Prog (RiscV.Word 64) := .return (.var .global "x")
private def fs : List (FunDeclOf 64) := [⟨funName,false,false,[],prog,.one⟩]
private def slot : BitVec 64 := heapTop - 8
private def domain (a : BitVec 64) : Prop := ordinaryAddress a ∧ a ≠ slot
private instance (a : BitVec 64) : Decidable (domain a) := by unfold domain; infer_instance
private def holBase : PanSemStateFiniteExact 64 Unit :=
  {functionSourceExact fs 1 2 with topAddr := slot, memaddrs := domain}
private def hol := setGlobalHOLFinite (ofString "x") (panValueToHOL (.word 3)) holBase
private def shapes (name : VarName) := if name = "x" then some ShapeHOL.one else none
private theorem supported : Supported shapes prog := by
  refine ⟨.ret (.global (.global "x" .one (by decide) ?_)), ?_⟩
  · simp [shapes]
  · simp [prog,ProgByteRanged,ExpByteRanged]
private def decl : DeclHOL 64 := .decl .one (ofString "x") (.const 3)
private def globals : PanGlobalsContextExact 64 :=
  {globals := HolFiniteMapExact.empty.updateEq (ofString "x",(.one,8)), globalsSize := 8, maxGlobalsSize := 8}
private def entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) :=
  [(ofString funName,[],progToHOL prog,.one)]
private def target := globalEntryTarget nonzeroScalarProgram 2 globals entries
private def before := beforeGlobals target 8 1
private def post := setGlobalHOLFinite (ofString "x") (panValueToHOL (.word 3)) before
private theorem addressSlot (a : BitVec 64) : addresses slot 1 a ↔ a = slot := by
  rw [mem_addresses]
  constructor
  · rintro ⟨i,hi,eq⟩
    have : i = 0 := by omega
    subst i
    simpa [bytesInWord] using eq
  · intro eq
    subst a
    exact ⟨0,by decide,by simp [bytesInWord]⟩
private theorem sourceEq : callEntryStateHOLFinite (installSourceFunctions post entries) HolFiniteMapExact.empty = hol := by
  have domainEq : (fun a => ordinaryAddress a ∧ ¬ addresses slot 1 a) = domain := by
    funext a
    apply propext
    simp [domain,addressSlot]
  unfold hol holBase post before target globalEntryTarget globalEntryTemplate
  rw [nonzeroScalar_bitmap]
  simp only [List.length_cons,List.length_nil]
  simp [callEntryStateHOLFinite,installSourceFunctions,installTargetFunctions,beforeGlobals,
    setGlobalHOLFinite,functionSourceExact,sourceTemplateFor,sourceTemplate,fs,entries,funDeclToHOL,functionsHOL,
    shapeToHOL,slot]
  exact domainEq


private def panCtxt : PanToCrepContextExact 64 := mkCtxtExactHOL HolFiniteMapExact.empty
  (HolFiniteMapExact.empty.update (ofString funName,([],ShapeHOL.one))) 0 HolFiniteMapExact.empty
private def inits : List (ProgHOL 64) := [.store (.op .sub [.topAddr,.const 8]) (.const 3)]
private theorem declEval : @evaluateDeclsHOLFinite 64 Unit _
    (beforeGlobals target (panBytesInWord 64 * BitVec.ofNat 64 ((decShapesHOL [decl]).map sizeOfShapeHOL).sum)
      ((decShapesHOL [decl]).map sizeOfShapeHOL).sum) (fun _a => Classical.propDecidable _) [decl] = some post := by
  with_unfolding_all rfl
private theorem compiled : compileDecsExactHOL
    (beforeGlobalsContext (panBytesInWord 64 * BitVec.ofNat 64 ((decShapesHOL [decl]).map sizeOfShapeHOL).sum)) [decl] =
    (inits,[],[],globals) := by
  simp [beforeGlobalsContext,decl,decShapesHOL,sizeOfShapeHOL,panBytesInWord,cakeBytesInWord,
    compileDecsExactHOL,compileDecsGlobalAddressExact_eq,compileExpExactHOL,inits,globals]
private theorem allocated : ∀ a, addresses ((globalEntryTemplate nonzeroScalarProgram 2).topAddr - panBytesInWord 64 *
    BitVec.ofNat 64 ((decShapesHOL [decl]).map sizeOfShapeHOL).sum)
    ((decShapesHOL [decl]).map sizeOfShapeHOL).sum a → (globalEntryTemplate nonzeroScalarProgram 2).memaddrs a := by
  intro a present
  change addresses slot 1 a at present
  have eq := (addressSlot a).mp present
  subst a
  change ordinaryAddress slot
  unfold slot heapTop fixtureHeapEnd heapEnd stackStart ramEnd ramStart ramSize stackSize globalsWords ordinaryAddress sourceBase
  decide
private theorem layout : GlobalLayout shapes globals := by
  intro name sh found
  by_cases same : name = "x"
  · subst name
    simp [shapes] at found
    subst sh
    exact ⟨8,by simp [globals,HolFiniteMapExact.lookup_updateEq,FUPDATE_HOL]⟩
  · simp [shapes,same] at found
private theorem initShape : ∀ sh n e, DeclHOL.decl sh n e ∈ [decl] → FrontendValue panCtxt e := by
  intro sh n e member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  cases member
  exact .scalar (.const 3)

private theorem bodyShape : GlobalCallFrontend globals panCtxt (progToHOL prog) :=
  globalCallSupported_frontend layout supported.1 panCtxt (by intro n member; simp at member)
private theorem targetTable : CallFrontendCode panCtxt target.code := by
  intro name params body ret found
  simp only [target,globalEntryTarget,installTargetFunctions,entries,List.map,List.reverse_cons,List.reverse_nil,
    List.nil_append,HolFiniteMapExact.lookup_updateList,FUPDATE_LIST,List.foldl_cons,List.foldl_nil,FUPDATE] at found
  split at found
  · simp only [Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨rfl,rfl,rfl⟩ := found
    apply globalCallFrontend_compiled
    exact globalCallSupported_frontend layout supported.1 _ (by intro n member; simp at member)
  · simp [HolFiniteMapExact.lookup_empty] at found
private theorem panCode : codeRelExactHOLW panCtxt target.code (globalEntryCrep nonzeroScalarProgram 2 globals entries).code := by
  intro name params body ret found
  simp only [target,globalEntryTarget,installTargetFunctions,entries,List.map,List.reverse_cons,List.reverse_nil,
    List.nil_append,HolFiniteMapExact.lookup_updateList,FUPDATE_LIST,List.foldl_cons,List.foldl_nil,FUPDATE] at found
  split at found
  · rename_i equal
    have keyEq : ofString funName = name := beq_iff_eq.mp equal
    subst name
    simp only [Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨rfl,rfl,rfl⟩ := found
    have shape := targetTable (ofString funName) [] (compileProgExactHOL globals (progToHOL prog)) .one
      (by simp [target,globalEntryTarget,installTargetFunctions,entries,HolFiniteMapExact.lookup_updateList,FUPDATE_LIST,FUPDATE])
    refine ⟨callFrontend_localised shape,?_,?_⟩
    · simp [panCtxt,mkCtxtExactHOL,HolFiniteMapExact.lookup_update,FUPDATE]
    · simp only [List.map_nil,sizeOfShapeHOL,sizeOfShapesHOL,List.range_zero]
      rw [show (globalEntryCrep nonzeroScalarProgram 2 globals entries).code = alistToFmapCodeExact nonzeroScalarCrep from congrArg alistToFmapCodeExact nonzeroScalar_crep]
      simp [nonzeroScalarCrep,alistToFmapCodeExact,prog,progToHOL,expToHOL,globals,compileProgExactHOL,
        compileExpExactHOL,compileReturnExactHOLW,compileProgExactHOLW,
        panCtxt,mkCtxtExactHOL,ctxtFcExactHOL,funName,ofString]
      with_unfolding_all rfl
  · simp [HolFiniteMapExact.lookup_empty] at found

open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopLiveSteps SteppedFlapjack.WordSimpSteps SteppedFlapjack.StackSteps
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordToStack.Native
private def entryBody : CrepProgHOL 64 := (nonzeroScalarCrep[0]'(by decide)).2.2
private theorem compiledEntry : compileProgExactHOLW panCtxt (.seq (nestedSeqHOL inits) (.call none (ofString funName) [])) = entryBody := by
  simp [entryBody,nonzeroScalarCrep,inits,compileProgExactHOLW,compileCallNoReturnExactHOLW,compileStoreExactHOLW,
    compileExpExactHOLW,compileExpExactHOLWList,panCtxt,mkCtxtExactHOL,cexpHeads,nestedDecsHOL,crepNestedSeqHOL,storesHOL,
    funName,ofString,nestedSeqHOL]
private theorem entryFixed : crepSimpProgHOL entryBody = entryBody := by
  obtain ⟨ctx,q,eq,shape⟩ := nonzeroScalar_sources (nonzeroScalarCrep[0]'(by decide)) (by rw [nonzeroScalar_crep]; simp [nonzeroScalarCrep])
  change entryBody = compileProgExactHOLW ctx q at eq
  rw [eq]
  exact callFrontend_simp_fixed shape
private theorem loopCodeRel : let ctxt := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (globalSourcePrograms nonzeroScalarProgram)) 0
    crepToLoopCodeRelExact ctxt (globalEntryCrep nonzeroScalarProgram 2 globals entries).code
      (sptFromAList (compileProgHOLExact riscvConfig.isa (globalSourcePrograms nonzeroScalarProgram))) := by
  apply wholeCrep_fixed_executable_codeRel _ _ (ofString "main") entryBody
  · rw [nonzeroScalar_crep]
    decide
  · rw [nonzeroScalar_crep]
    with_unfolding_all rfl
  · intro name params body member
    obtain ⟨ctx,q,eq,shape⟩ := nonzeroScalar_sources (name,params,body) member
    simp only at eq
    rw [eq]
    exact callFrontend_simp_fixed shape
private theorem loopEntry : let ctxt := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (globalSourcePrograms nonzeroScalarProgram)) 0
    let body := compileProgExactHOLW panCtxt (.seq (nestedSeqHOL inits) (.call none (ofString funName) []))
    (64,[],optimiseHOL (compileHOLExact ctxt .ln body)) ∈ compileProgHOLExact riscvConfig.isa (globalSourcePrograms nonzeroScalarProgram) := by
  dsimp only
  rw [compiledEntry]
  have first : globalSourcePrograms nonzeroScalarProgram = (ofString "main",[],entryBody) :: [nonzeroScalarCrep[1]'(by decide)] := by
    rw [nonzeroScalar_crep]
    with_unfolding_all rfl
  have result := firstCrep_loopEntry riscvConfig.isa (ofString "main") entryBody [nonzeroScalarCrep[1]'(by decide)] entryFixed
  rw [← first] at result
  obtain ⟨tail,eq⟩ := result
  rw [eq]
  simp [firstLoopName]

private instance : DecidablePred post.memaddrs := by
  have h := congrArg (fun (s : PanSemStateFiniteExact 64 Unit) => s.memaddrs) sourceEq
  change post.memaddrs = domain at h
  rw [h]
  infer_instance
private instance : DecidablePred post.shMemaddrs := by
  change DecidablePred sharedAddress
  infer_instance
private theorem canonicalShapeX : globalEntryShapes post entries "x" = some .one := by
  unfold globalEntryShapes globalEntrySource
  rw [sourceEq]
  simp [hol,holBase,functionSourceExact,sourceTemplateFor,sourceTemplate,setGlobalHOLFinite,
    HolFiniteMapExact.lookup_update,FUPDATE,shapeOfHOLExact]
private theorem canonicalSupported : Supported (globalEntryShapes post entries) prog := by
  refine ⟨.ret (.global (.global "x" .one (by decide) canonicalShapeX)), ?_⟩
  simp [prog,ProgByteRanged,ExpByteRanged]
private theorem canonicalTable : ∀ name params body ret, entries.lookup name = some (params,body,ret) →
    ∃ scope, GlobalCallSupportedIn (globalEntryShapes post entries) scope (progOfHOL body) := by
  intro name params body ret found
  simp only [entries,List.lookup] at found
  split at found
  · simp only [Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨rfl,rfl,rfl⟩ := found
    refine ⟨[],?_⟩
    rw [progOfHOL_progToHOL prog supported.2]
    exact canonicalSupported.1
  · simp at found
private theorem canonicalRun : evalPanValueFfiProgSteps (riscv64PanValueFfiContext (fun _ => false))
    (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) (globalEntryProduction post entries).structs
    (countedFunctionsOfCode (globalEntryProduction post entries).code)
    (globalEntryProduction post entries).baseAddress (globalEntryProduction post entries).topAddress
    panSemBitVec64BytesInWord 5 (globalEntryProduction post entries).locals (globalEntryProduction post entries).globals
    (globalEntryProduction post entries).memory (globalEntryProduction post entries).ffi prog
    (memoryAccess := some (panSemBitVec64MemoryAccess (globalEntryProduction post entries)))
    (contracts := some (countedContractsOfCode (globalEntryProduction post entries).code [])) =
      some (.returned (globalEntryProduction post entries).locals (globalEntryProduction post entries).globals
        (globalEntryProduction post entries).memory (globalEntryProduction post entries).ffi [.word 3],2) := by
  with_unfolding_all rfl

private theorem sourceGood : pancakeGoodCodeHOL nonzeroScalarProgram = true := by with_unfolding_all decide
private theorem unique : ((functionsHOL nonzeroScalarProgram).map Prod.fst).Nodup := by with_unfolding_all decide
private theorem budget : 2 ≤ (callEntryStateHOLFinite (installSourceFunctions post entries) HolFiniteMapExact.empty).clock := by
  rw [sourceEq]
  decide
private theorem bitmapFits : 0xa0020018 + (globalSourceBitmaps nonzeroScalarProgram).length*8 ≤ 0xa0410000 := by
  rw [nonzeroScalar_bitmap]
  decide
private noncomputable def nonzeroScalarTicks : Nat :=
  let code := globalSourceCode nonzeroScalarProgram
  let bs := globalSourceBitmaps nonzeroScalarProgram
  let words := globalSourceWords nonzeroScalarProgram
  let crep := globalEntryCrep nonzeroScalarProgram 2 globals entries
  let ctxt := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (globalSourcePrograms nonzeroScalarProgram)) 0
  let body := .seq (nestedSeqHOL inits) (.call none (ofString funName) [])
  let visitLimit := 2*[decl].length+(callEntryStateHOLFinite (installSourceFunctions post entries) HolFiniteMapExact.empty).clock+3
  let opt := loweredProgramOptLimit panCtxt body crep (globalSourcePrograms nonzeroScalarProgram) visitLimit ctxt ctxt .ln
  let allowance := (max 1 (wordCodeWeight (sptFromAList words)) + 1) * (6*opt+1) + 1
  let n := 1 + max 1 (stackCodeWeight (sptFromAList code)) * (6*opt+1 + allowance)
  948 * StackToLabSteps.stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset
    bs code (fixtureStackOracle (fixtureCompilerConfig code)) n

/-- A nonzero global initializer runs on the actual compiled RISC-V machine. -/
private theorem nonzeroScalar_machine : ∃ finalMachine finalFfi compilerFinal,
    Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig nonzeroScalarProgram =
      some (fixtureCodeBytes (globalSourceCode nonzeroScalarProgram),globalSourceBitmaps nonzeroScalarProgram,compilerFinal) ∧
    evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart (globalSourceCode nonzeroScalarProgram))) sourceFfi
      nonzeroScalarTicks (configuredMachineState (globalSourceCode nonzeroScalarProgram) (globalSourceBitmaps nonzeroScalarProgram)) =
      (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFfi.ioEvents := by
  have all := initializedGlobal_counted_machine nonzeroScalarProgram unique sourceGood 2 [decl] post inits [] [] globals
    entries (ofString funName) prog canonicalSupported panCtxt 3
    (by intro d hd; simp at hd; subst d; rfl) initShape declEval compiled allocated (by decide)
    (by simp [entries]) canonicalTable
    (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) [] 5 2
    (globalEntryProduction post entries).locals (globalEntryProduction post entries).globals
    (globalEntryProduction post entries).memory (globalEntryProduction post entries).ffi canonicalRun budget
    targetTable panCode rfl rfl nonzeroScalar_sources loopCodeRel loopEntry bitmapFits
    nonzeroScalar_safe nonzeroScalar_facts nonzeroScalar_capacity
  obtain ⟨sourceFinal,machine,ffi,compilerFinal,compiledOutput,machineRun,events,ffiRel⟩ := all
  have sourceEvents : sourceFinal.ffi.ioEvents = [] := by
    have h := ffiRel.2.1
    simp only [globalEntryProduction,panSemExecStateOfHOLWithKeys,panSemStateOfExactWithKeys,sourceFfiState,sourceFfi,List.map_nil] at h
    cases heq : sourceFinal.ffi.ioEvents with
    | nil => rfl
    | cons e es => simp [heq,FfiEventListRel] at h
  refine ⟨machine,ffi,compilerFinal,compiledOutput,machineRun,?_⟩
  simpa [sourceFfi,sourceEvents] using events

def nonzeroScalarSourceBase : PanSemStateFiniteExact 64 Unit :=
  {sourceTemplate with topAddr := slot, memaddrs := domain}
private def declared : PanSemStateFiniteExact 64 Unit :=
  {setGlobalHOLFinite (ofString "x") (panValueToHOL (.word 3)) nonzeroScalarSourceBase with
    code := HolFiniteMapExact.empty.update (ofString "main",([],progToHOL prog,.one))}
private instance : DecidablePred nonzeroScalarSourceBase.memaddrs := by
  change DecidablePred domain
  infer_instance
private theorem declsRun : evaluateDeclsHOLFinite nonzeroScalarSourceBase nonzeroScalarProgram = some declared := by
  with_unfolding_all rfl
private theorem declaredRun : declared.evaluateHOLFiniteState (progToHOL prog) =
    (some (.returned (.val (.word 3))),emptyLocalsHOLFinite declared) := by
  simp [declared,nonzeroScalarSourceBase,sourceTemplate,prog,progToHOL,expToHOL,setGlobalHOLFinite,
    evaluateHOLFiniteState_return,evalHOLExact,emptyLocalsHOLFinite,shapeOfHOLExact,FUPDATE]

/-- The original source declarations initialize x to three and terminate successfully. -/
private theorem nonzeroScalar_source_semantics : semanticsDecls nonzeroScalarSourceBase (ofString "main") nonzeroScalarProgram =
    .terminate .success sourceFfi.ioEvents := by
  have code : declared.code.lookup (ofString "main") = some ([],progToHOL prog,.one) := by
    simp [declared,HolFiniteMapExact.lookup_update,FUPDATE]
  have lookup : lookupCodeHOLFinite declared.code.lookup (ofString "main") [] =
      some (progToHOL prog,HolFiniteMapExact.empty,.one) := by
    apply SemInitSupport.lookup_init
    exact code
  have entry : callEntryStateHOLFinite {declared with clock := declared.clock+1} HolFiniteMapExact.empty = declared := by
    simp [callEntryStateHOLFinite,declared,nonzeroScalarSourceBase,sourceTemplate,setGlobalHOLFinite]
  have callRun : evaluateHOLFiniteState {declared with clock := declared.clock+1} (.call none (ofString "main") []) =
      (some (.returned (.val (.word 3))),emptyLocalsHOLFinite (emptyLocalsHOLFinite declared)) := by
    rw [evaluateHOLFiniteState_call]
    simp only [evalListHOLFinite,evalListHOLExact,lookup,show declared.clock+1 ≠ 0 by omega,↓reduceIte,entry,declaredRun]
    simp [shapeOfHOLExact,shapeEqHOL,emptyLocalsHOLFinite]
  have behavior := source_semantics_of_return declared (emptyLocalsHOLFinite (emptyLocalsHOLFinite declared))
    (ofString "main") (declared.clock+1) (.val (.word 3)) callRun
  have declarations : semanticsDecls nonzeroScalarSourceBase (ofString "main") nonzeroScalarProgram = semantics declared (ofString "main") := by
    have names : decsStcnamesHOLExact [] nonzeroScalarProgram = some [] := by
      simp [nonzeroScalarProgram,decsStcnamesHOLExact]
    unfold semanticsDecls
    rw [names]
    simp only
    have initialEq : {nonzeroScalarSourceBase with structs := []} = nonzeroScalarSourceBase := by rfl
    rw [initialEq]
    have classicalRun : @evaluateDeclsHOLFinite 64 Unit _ nonzeroScalarSourceBase
        (fun a => Classical.propDecidable (nonzeroScalarSourceBase.memaddrs a)) nonzeroScalarProgram = some declared := by
      have decEq : (fun a => Classical.propDecidable (nonzeroScalarSourceBase.memaddrs a)) =
          (inferInstance : DecidablePred nonzeroScalarSourceBase.memaddrs) := by
        funext a
        exact Subsingleton.elim _ _
      rw [decEq]
      exact declsRun
    rw [classicalRun]
  rw [declarations]
  simpa [emptyLocalsHOLFinite,declared,nonzeroScalarSourceBase,sourceTemplate,setGlobalHOLFinite] using behavior

private theorem sourceClock : (callEntryStateHOLFinite (installSourceFunctions post entries) HolFiniteMapExact.empty).clock = 2 := by
  rw [sourceEq]
  rfl
private theorem crepClock : (globalEntryCrep nonzeroScalarProgram 2 globals entries).clock = 3 := rfl
private theorem entryWeight : CrepSteps.statementWeight entryBody = 9 := by
  simp [entryBody,nonzeroScalarCrep,CrepSteps.statementWeight]
private theorem tableWeight : CrepSteps.codeWeight (globalSourcePrograms nonzeroScalarProgram) = 9 := by
  rw [nonzeroScalar_crep]
  simp [nonzeroScalarCrep,CrepSteps.codeWeight,CrepSteps.statementWeight]
private theorem syntaxWeight (ctx : CrepToLoopContextExact) : callSyntaxCost ctx entryBody = 21 := by
  simp [entryBody,nonzeroScalarCrep,callSyntaxCost,callExpressionCost,callArgumentsCost,
    compileExpHOLExact,compileExpsHOLExact,loopNestedSeqHOL,LoopSteps.structuralWeight]
private theorem callFactor (ctx : CrepToLoopContextExact) (clock : Nat) :
    callClockFactor ctx ((globalSourcePrograms nonzeroScalarProgram).map (fun row => (row.2.1,row.2.2))) clock entryBody = 270 := by
  rw [nonzeroScalar_crep]
  simp [entryBody,nonzeroScalarCrep,callClockFactor,callTableCost,callSyntaxCost,callExpressionCost,callArgumentsCost,
    compileExpHOLExact,compileExpsHOLExact,loopNestedSeqHOL,LoopSteps.structuralWeight]
private theorem optWeight :
    let ctxt := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (globalSourcePrograms nonzeroScalarProgram)) 0
    loopVisitWeight (optimiseHOL (compileHOLExact ctxt .ln entryBody)) = 42 := by
  have first : globalSourcePrograms nonzeroScalarProgram = (ofString "main",[],entryBody) :: [nonzeroScalarCrep[1]'(by decide)] := by
    rw [nonzeroScalar_crep]
    with_unfolding_all rfl
  have result := firstCrep_loopEntry riscvConfig.isa (ofString "main") entryBody [nonzeroScalarCrep[1]'(by decide)] entryFixed
  rw [← first] at result
  obtain ⟨tail,eq⟩ := result
  rw [nonzeroScalar_loop] at eq
  have h := congrArg (fun (rows : List (Nat × List Nat × HolLoopProg 64)) => rows[0]?) eq
  simp only [nonzeroScalarLoop,List.getElem?_cons,↓reduceIte,Option.some.injEq,Prod.mk.injEq] at h
  dsimp only
  rw [← h.2.2]
  decide +kernel
private theorem optLimitNumeric :
    let crep := globalEntryCrep nonzeroScalarProgram 2 globals entries
    let ctxt := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (globalSourcePrograms nonzeroScalarProgram)) 0
    loweredProgramOptLimit panCtxt (.seq (nestedSeqHOL inits) (.call none (ofString funName) [])) crep
      (globalSourcePrograms nonzeroScalarProgram) (2*[decl].length+(callEntryStateHOLFinite (installSourceFunctions post entries) HolFiniteMapExact.empty).clock+3) ctxt ctxt .ln = 66921666 := by
  unfold loweredProgramOptLimit
  rw [compiledEntry,sourceClock]
  simp only [crepClock,List.length_cons,List.length_nil]
  rw [entryWeight,tableWeight,callFactor,syntaxWeight,nonzeroScalar_loopWeight,optWeight]
  decide

open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open SteppedFlapjack.StackRemoveSteps.CompCorrect SteppedFlapjack.StackRemoveSteps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics SteppedFlapjack.StackToLabSteps SteppedFlapjack.StackAllocSteps
private theorem numericBackend (code : List (Nat × HolProg 64))
    (factor : costFromFields riscvConfig.addrOffset 0 (.call none (.inl Flapjack.Compiler.Backend.BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf code)) [4] (fixtureStackOracle (fixtureCompilerConfig code)) = 1950) :
    948 * stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset [4] code
      (fixtureStackOracle (fixtureCompilerConfig code))
      (1 + 23 * (6*66921666+1 + ((19+1)*(6*66921666+1)+1))) = 20435390013946508748 := by
  have uniform : uniformFactor (width := 64) countdownRiscVBackend.dataConf = 19 := by decide +kernel
  have init : loopOnlyCost 0 (initCode (Flapjack.Compiler.Backend.StackToLab.isGenGc countdownRiscVBackend.dataConf.gcKind) (2^53-1) 24 : HolProg 64) = 361 := by decide +kernel
  unfold fixtureStackOracle
  rw [stackLabTickLimit_emptyOracle]
  dsimp only
  unfold fixtureStackOracle at factor
  rw [factor,uniform,init]
  simp [flattenStepFactor]
private theorem numericFromInputs (code : List (Nat × HolProg 64)) (bs : List (BitVec 64)) (opt ww sw : Nat)
    (bitmap : bs = [4]) (optEq : opt = 66921666) (wordEq : ww = 19) (stackEq : sw = 23)
    (factor : costFromFields riscvConfig.addrOffset 0 (.call none (.inl Flapjack.Compiler.Backend.BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf code)) [4] (fixtureStackOracle (fixtureCompilerConfig code)) = 1950) :
    948 * stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset bs code
      (fixtureStackOracle (fixtureCompilerConfig code))
      (1 + max 1 sw * (6*opt+1 + ((max 1 ww+1)*(6*opt+1)+1))) = 20435390013946508748 := by
  subst bs; subst opt; subst ww; subst sw
  exact numericBackend code factor
private theorem nonzeroClock_numeric : nonzeroScalarTicks = 20435390013946508748 := by
  unfold nonzeroScalarTicks
  dsimp only
  apply numericFromInputs
  case bitmap => exact nonzeroScalar_bitmap
  case optEq => exact optLimitNumeric
  case wordEq => exact nonzeroScalar_wordWeight
  case stackEq => exact nonzeroScalar_stackWeight
  case factor => exact nonzeroScalar_tickFactor _

/-- The nonzero source declarations and their actual compiled machine agree. -/
theorem nonzeroScalar_source_machine : ∃ sourceDeclared sourceAfter finalMachine finalFfi compilerFinal,
    evaluateDeclsHOLFinite nonzeroScalarSourceBase nonzeroScalarProgram = some sourceDeclared ∧
    sourceDeclared.evaluateHOLFiniteState (.return (.var .global (ofString "x"))) =
      (some (.returned (.val (.word 3))),sourceAfter) ∧
    Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig nonzeroScalarProgram =
      some (fixtureCodeBytes (globalSourceCode nonzeroScalarProgram),globalSourceBitmaps nonzeroScalarProgram,compilerFinal) ∧
    evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart (globalSourceCode nonzeroScalarProgram))) sourceFfi
      20435390013946508748 (configuredMachineState (globalSourceCode nonzeroScalarProgram) (globalSourceBitmaps nonzeroScalarProgram)) =
      (.halt .success,finalMachine,finalFfi) ∧
    semanticsDecls nonzeroScalarSourceBase (ofString "main") nonzeroScalarProgram = .terminate .success finalFfi.ioEvents := by
  obtain ⟨machine,ffi,compilerFinal,compiled,run,events⟩ := nonzeroScalar_machine
  have runSource : declared.evaluateHOLFiniteState (.return (.var .global (ofString "x"))) =
      (some (.returned (.val (.word 3))),emptyLocalsHOLFinite declared) := by
    simpa [prog,progToHOL,expToHOL] using declaredRun
  refine ⟨declared,emptyLocalsHOLFinite declared,machine,ffi,compilerFinal,declsRun,runSource,compiled,?_,?_⟩
  · rw [← nonzeroClock_numeric]
    exact run
  · rw [events]
    exact nonzeroScalar_source_semantics
end SteppedFlapjack.Concrete
