import SteppedFlapjack.Concrete.GlobalStructEntry
import SteppedFlapjack.Concrete.GlobalCountedMachine
import SteppedFlapjack.Concrete.GlobalStructConfiguredWord
import SteppedFlapjack.Concrete.GlobalNamedStruct
import SteppedFlapjack.Concrete.GlobalStructInitializer
/-! The initialized global-pair wrapper meets the counted machine theorem. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.StackRemove Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString SteppedFlapjack.PanToCrepSteps

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def pairCrepContext : PanToCrepContextExact 64 := globalCompilerContext globalStructProgram

theorem pairSourcePrograms : globalSourcePrograms globalStructProgram = globalStructCallPrograms := by
  unfold globalSourcePrograms globalStructCallPrograms
  rw [globalStruct_simp_fixed,globalStruct_structs_fixed]

theorem pairEntry_actualCompiled : compileProgExactHOLW pairCrepContext
    (compileProgExactHOL globalStructContext (progToHOL pairWrapper)) = globalStructActualEntryCrep := by
  rw [pairWrapper_lowered]
  unfold globalStructActualEntryCrep
  have init := globalStruct_initializer_context pairCrepContext (by simp [pairCrepContext,globalCompilerContext,mkCtxtExactHOL])
  rw [globalStruct_actual_initializer_eq] at init
  simp only [compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,List.flatMap_nil]
  congr 1
  unfold globalStructActualInit
  rw [globalStruct_actual_initializer_eq]
  simp [compileProgExactHOLW,compileStoreExactHOLW,compileExpExactHOLW,compileExpExactHOLWList,
    sizeOfShapeHOL,sizeOfShapesHOL,nestedDecsHOL,pairCrepContext,globalCompilerContext,globalStructCrepContext,mkCtxtExactHOL]


open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.WordDepth.Executable Flapjack.Compiler.Backend.BackendProps

theorem pairRawWords : globalSourceRaw globalStructProgram = globalStructActualWordPrograms := by
  unfold globalSourceRaw globalStructActualWordPrograms
  rw [pairSourcePrograms]

theorem pairAllocator : compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig
    (globalSourceRaw globalStructProgram) = compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig globalStructActualWordPrograms := by
  exact congrArg (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig) pairRawWords

/-- The named source compiles to the same raw Word table used by the witness. -/
theorem pairNamed_rawWords : panToWordCompileProgHOL riscvConfig.isa namedGlobalStructProgram =
    globalSourceRaw globalStructProgram := by
  rw [pairRawWords]
  unfold panToWordCompileProgHOL globalStructActualWordPrograms globalStructCallPrograms
  dsimp only
  rw [namedGlobalStruct_pipeline]

theorem pairSourceWords : globalSourceWords globalStructProgram = globalStructOptimizedWords := by
  exact congrArg Prod.snd pairAllocator

theorem pairSourceNative : globalSourceNative globalStructProgram = compileNative riscvConfig false globalStructOptimizedWords := by
  exact congrArg (compileNative riscvConfig false) pairSourceWords

theorem pairSourceCode : globalSourceCode globalStructProgram = globalStructNativeCode := by
  exact congrArg (fun p => p.2.2.2) pairSourceNative

theorem pairSourceBitmaps : globalSourceBitmaps globalStructProgram = globalStructNativeBitmaps := by
  exact congrArg Prod.fst pairSourceNative


theorem pairSourceFrame : globalSourceFrame globalStructProgram = globalStructNativeEntryFrame := by
  unfold globalSourceFrame globalStructNativeEntryFrame globalSourceEntry globalStructNativeEntry
  exact congrArg (fun words => (compileProgNative riscvConfig false
    (((sptLookup 64 (sptFromAList words)).getD (1,.skip)).2) 1
    (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1) pairSourceWords

theorem pairSourceFrames : globalSourceFrames globalStructProgram = globalStructNativeFrameSizes := by
  unfold globalSourceFrames globalStructNativeFrameSizes
  exact congrArg (fun words => sptMapi (fun _ (argc,body) => (compileProgNative riscvConfig false body argc
    (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1) (sptFromAList words)) pairSourceWords

open SteppedFlapjack.LoopLiveSteps SteppedFlapjack.WordSimpSteps SteppedFlapjack.StackSteps
private def entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) := [(newMainNameHOL globalStructProgram,[],progToHOL globalStructWitness,ShapeHOL.one)]
private def post := {globalStructHOL with clock := 9}
private theorem template_eq : globalEntryTemplate globalStructProgram 8 = {globalStructTarget with clock := 9} := by
  rw [globalEntryTemplate,pairSourceBitmaps]
  have bm : globalStructNativeBitmaps = [4] := globalStruct_nativeBitmap
  rw [bm]
  rfl
private theorem before_eq : beforeGlobals (globalEntryTarget globalStructProgram 8 globalStructContext entries) 16 2 = {globalStructBase with clock := 9} := by
  have old := congrArg (fun s : PanSemStateFiniteExact 64 Unit => {s with clock := 9}) pairBefore_eq
  simpa [globalEntryTarget,installTargetFunctions,beforeGlobals,template_eq,globalStructTarget,sourceTemplate,globalStructBase] using old
private theorem declEval : @evaluateDeclsHOLFinite 64 Unit _
    (beforeGlobals (globalEntryTarget globalStructProgram 8 globalStructContext entries)
      (panBytesInWord 64 * BitVec.ofNat 64 ((decShapesHOL [globalStructDecl]).map sizeOfShapeHOL).sum)
      ((decShapesHOL [globalStructDecl]).map sizeOfShapeHOL).sum)
    (fun _ => Classical.propDecidable _) [globalStructDecl] = some post := by
  change @evaluateDeclsHOLFinite 64 Unit _
    (beforeGlobals (globalEntryTarget globalStructProgram 8 globalStructContext entries) 16 2)
    (fun _ => Classical.propDecidable _) [globalStructDecl] = some post
  have evalEq := congrArg (fun s : PanSemStateFiniteExact 64 Unit =>
    @evaluateDeclsHOLFinite 64 Unit _ s (fun _ => Classical.propDecidable _) [globalStructDecl]) before_eq
  rw [evalEq]
  with_unfolding_all rfl
private def inits : List (ProgHOL 64) := (compileDecsExactHOL globalStructStart [globalStructDecl]).1
private theorem compiled : compileDecsExactHOL
    (beforeGlobalsContext (panBytesInWord 64 * BitVec.ofNat 64 ((decShapesHOL [globalStructDecl]).map sizeOfShapeHOL).sum)) [globalStructDecl] =
    (inits,[],[],globalStructContext) := by
  simp [inits,beforeGlobalsContext,globalStructStart,globalStructContext,globalStructDecl,decShapesHOL,
    sizeOfShapeHOL,sizeOfShapesHOL,panBytesInWord,cakeBytesInWord,compileDecsExactHOL,compileDecsGlobalAddressExact_eq]
private theorem initShape : ∀ sh n e, DeclHOL.decl sh n e ∈ [globalStructDecl] → FrontendValue pairCrepContext e := by
  intro sh n e member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  cases member
  apply FrontendValue.tuple
  intro e member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> exact .scalar (.const _)
private theorem allocated : ∀ a, addresses ((globalEntryTemplate globalStructProgram 8).topAddr - panBytesInWord 64 *
    BitVec.ofNat 64 ((decShapesHOL [globalStructDecl]).map sizeOfShapeHOL).sum)
    ((decShapesHOL [globalStructDecl]).map sizeOfShapeHOL).sum a → (globalEntryTemplate globalStructProgram 8).memaddrs a := by
  simpa [template_eq,globalStructDecl,decShapesHOL,sizeOfShapeHOL,sizeOfShapesHOL,cakeBytesInWord,panBytesInWord] using globalStructSlots_allocated
private theorem compiledEntry : compileProgExactHOLW pairCrepContext
    (.seq (nestedSeqHOL inits) (.call none (newMainNameHOL globalStructProgram) [])) = globalStructActualEntryCrep := by
  rw [← pairEntry_actualCompiled,pairWrapper_lowered]
  congr 2
  simp [inits,globalStructDecl,globalStructStart,compileDecsExactHOL,compileDecsGlobalAddressExact_eq,
    sizeOfShapeHOL,sizeOfShapesHOL,cakeBytesInWord,nestedSeqHOL,compileExpExactHOL,compileExpExactHOLList]
private theorem declEq : globalCompilerDecls globalStructProgram = compileTopExactHOL globalStructProgram (ofString "main") := by
  unfold globalCompilerDecls
  rw [globalStruct_simp_fixed,globalStruct_structs_fixed]
private theorem allRows : functionsHOL (globalCompilerDecls globalStructProgram) =
    (ofString "main",[],.seq (nestedSeqHOL inits) (.call none (newMainNameHOL globalStructProgram) []),.one) ::
      entries.map (fun e => (e.1,e.2.1,compileProgExactHOL globalStructContext e.2.2.1,e.2.2.2)) := by
  rw [declEq,globalStruct_compileTop]
  simp [functionsHOL,entries,inits,globalStructStart,globalStructDecl,compileDecsExactHOL,
    compileDecsGlobalAddressExact_eq,sizeOfShapeHOL,sizeOfShapesHOL,cakeBytesInWord,nestedSeqHOL,
    compileExpExactHOL,compileExpExactHOLList]
private theorem noInline : (functionsHOL ((globalCompilerDecls globalStructProgram).filter inlinableHOL)).map Prod.fst = [] := by
  rw [declEq]
  exact globalStruct_noInline
private theorem exceptionsEmpty : pairCrepContext.eids = HolFiniteMapExact.empty := by
  unfold pairCrepContext globalCompilerContext
  rw [declEq,globalStruct_compileTop]
  with_unfolding_all rfl

private instance : DecidablePred post.memaddrs := by
  change DecidablePred globalStructSourceDomain
  infer_instance
private instance : DecidablePred post.shMemaddrs := by
  change DecidablePred sharedAddress
  infer_instance
private theorem shapePair : globalEntryShapes post entries "pair" = some (.comb [.one,.one]) := by
  simp [globalEntryShapes,globalEntrySource,installSourceFunctions,callEntryStateHOLFinite,post,globalStructHOL,setGlobalHOLFinite,
    HolFiniteMapExact.lookup_update,FUPDATE,shapeOfHOLExact]
private theorem supportedPair : Supported (globalEntryShapes post entries) globalStructWitness := by
  constructor
  · unfold globalStructWitness
    refine .seq (.assignGlobalStruct "pair" [.one,.one] shapePair ?_) ?_
    · intro e member
      simp at member
      rcases member with rfl | rfl <;> exact .scalar (.local (.const _))
    · exact .ret (.global (.field (.global "pair" (.comb [.one,.one]) (by decide) shapePair) 1 .one rfl))
  · exact globalStructWitness_ranged
private theorem tablePair : GlobalSupportedEntries (globalEntryShapes post entries) entries := by
  intro name params body ret found
  simp only [entries,List.lookup] at found
  split at found
  · simp only [Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨rfl,rfl,rfl⟩ := found
    exact ⟨[],globalStructWitness,rfl,rfl,supportedPair.1,supportedPair.2⟩
  · simp at found
private theorem canonicalRun : evalPanValueFfiProgSteps (riscv64PanValueFfiContext (fun _ => false))
    (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) (globalEntryProduction post entries).structs
    (countedFunctionsOfCode (globalEntryProduction post entries).code)
    (globalEntryProduction post entries).baseAddress (globalEntryProduction post entries).topAddress
    panSemBitVec64BytesInWord 10 (globalEntryProduction post entries).locals (globalEntryProduction post entries).globals
    (globalEntryProduction post entries).memory (globalEntryProduction post entries).ffi globalStructWitness
    (memoryAccess := some (panSemBitVec64MemoryAccess (globalEntryProduction post entries)))
    (contracts := some (countedContractsOfCode (globalEntryProduction post entries).code [])) =
      some (.returned (globalEntryProduction post entries).locals
        (updatePanValueMap (globalEntryProduction post entries).globals "pair" (.rStruct [.word 7,.word 8]))
        (globalEntryProduction post entries).memory (globalEntryProduction post entries).ffi [.word 8],8) := by
  with_unfolding_all rfl
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.WordDepth.Executable Flapjack.Compiler.Backend.BackendProps
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopLiveSteps SteppedFlapjack.WordSimpSteps SteppedFlapjack.StackSteps
noncomputable def pairUnifiedTicks : Nat :=
  let code := globalSourceCode globalStructProgram
  let bs := globalSourceBitmaps globalStructProgram
  let words := globalSourceWords globalStructProgram
  let crep := globalEntryCrep globalStructProgram 8 globalStructContext entries
  let ctxt := mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (globalSourcePrograms globalStructProgram)) 0
  let body := .seq (nestedSeqHOL inits) (.call none (newMainNameHOL globalStructProgram) [])
  let visitLimit := 2*[globalStructDecl].length+(callEntryStateHOLFinite (installSourceFunctions post entries) HolFiniteMapExact.empty).clock+3
  let opt := loweredProgramOptLimit pairCrepContext body crep (globalSourcePrograms globalStructProgram) visitLimit ctxt ctxt .ln
  let allowance := (max 1 (wordCodeWeight (sptFromAList words)) + 1) * (6*opt+1) + 1
  let n := 1 + max 1 (stackCodeWeight (sptFromAList code)) * (6*opt+1 + allowance)
  948 * StackToLabSteps.stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset
    bs code (fixtureStackOracle (fixtureCompilerConfig code)) n
private theorem pairUnified_machine : ∃ finalMachine finalFfi compilerFinal,
    Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig globalStructProgram =
      some (fixtureCodeBytes (globalSourceCode globalStructProgram),globalSourceBitmaps globalStructProgram,compilerFinal) ∧
    evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart (globalSourceCode globalStructProgram))) sourceFfi
      pairUnifiedTicks (configuredMachineState (globalSourceCode globalStructProgram) (globalSourceBitmaps globalStructProgram)) =
      (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFfi.ioEvents := by
  have good : pancakeGoodCodeHOL globalStructProgram = true := by with_unfolding_all decide
  have bits : 0xa0020018 + (globalSourceBitmaps globalStructProgram).length*8 ≤ 0xa0410000 := by
    rw [pairSourceBitmaps]
    have h : globalStructNativeBitmaps = [4] := globalStruct_nativeBitmap
    rw [h]
    decide
  have safety : fixtureStackSafe (globalSourceCode globalStructProgram) = true := by
    rw [pairSourceCode]
    exact globalStruct_nativeSafe
  have facts : (fixtureRemoveLabels (globalSourceCode globalStructProgram)).isSome = true ∧
      (fixtureCodeBytes (globalSourceCode globalStructProgram)).length ≤ 0xecc ∧
      (fixtureCodeBytes (globalSourceCode globalStructProgram)).length % 4 = 0 := by
    rw [pairSourceCode]
    exact globalStruct_nativeCompilerFacts
  have capacity : optionLe (optionMap₂ max (some (max 1 (1+globalSourceFrame globalStructProgram)))
      (optionMap₂ (· + ·) (some 1) (fullCallGraphDepth (globalSourceFrames globalStructProgram) 64
        (sptFromAList (globalSourceWords globalStructProgram))))) (some 2097172) := by
    rw [pairSourceFrame,pairSourceFrames,pairSourceWords]
    exact globalStruct_nativeCapacity
  have all := initializedGlobal_counted_machine globalStructProgram globalStruct_sourceUnique good 8 [globalStructDecl] post inits [] [] globalStructContext
    entries (newMainNameHOL globalStructProgram) globalStructWitness supportedPair 8
    (by intro d hd; simp at hd; subst d; rfl) initShape declEval compiled allocated (by decide)
    (by simp [entries]) tablePair
    (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) [] 10 8
    (globalEntryProduction post entries).locals
    (updatePanValueMap (globalEntryProduction post entries).globals "pair" (.rStruct [.word 7,.word 8]))
    (globalEntryProduction post entries).memory (globalEntryProduction post entries).ffi canonicalRun (by decide)
    allRows noInline exceptionsEmpty
    bits safety facts capacity
  obtain ⟨sourceFinal,machine,ffi,compilerFinal,compiledOutput,machineRun,events,ffiRel⟩ := all
  have sourceEvents : sourceFinal.ffi.ioEvents = [] := by
    have h := ffiRel.2.1
    simp only [globalEntryProduction,panSemExecStateOfHOLWithKeys,panSemStateOfExactWithKeys,sourceFfiState,sourceFfi,List.map_nil] at h
    cases heq : sourceFinal.ffi.ioEvents with
    | nil => rfl
    | cons e es => simp [heq,FfiEventListRel] at h
  refine ⟨machine,ffi,compilerFinal,compiledOutput,machineRun,?_⟩
  simpa [sourceFfi,sourceEvents] using events

private theorem pairStatementWeight : CrepSteps.statementWeight globalStructActualEntryCrep = 12 := by
  unfold globalStructActualEntryCrep globalStructActualInit
  rw [globalStruct_actual_initializer_eq]
  simp [CrepSteps.statementWeight,compileProgExactHOLW,compileStoreExactHOLW,compileExpExactHOLW,
    compileExpExactHOLWList,sizeOfShapeHOL,sizeOfShapesHOL,nestedDecsHOL,globalStructCrepContext,mkCtxtExactHOL]
  with_unfolding_all rfl
private theorem pairTableWeight : CrepSteps.codeWeight globalStructCallPrograms = 12 := by
  rw [globalStruct_actualPrograms_eq]
  unfold globalStructActualBody
  rw [globalStructWitness_lowering]
  simp [CrepSteps.codeWeight,CrepSteps.statementWeight,globalStructActualInit,globalStruct_actual_initializer_eq,
    compileProgExactHOLW,compileStoreExactHOLW,compileReturnExactHOLW,compileExpExactHOLW,compileExpExactHOLWList,
    sizeOfShapeHOL,sizeOfShapesHOL,loadShapeBytesHOLW,nestedDecsHOL,globalStructCrepContext,mkCtxtExactHOL]
  with_unfolding_all rfl
private theorem pairSyntaxWeight : callSyntaxCost globalStructActualLoopContext globalStructActualEntryCrep = 31 := by
  unfold globalStructActualEntryCrep globalStructActualInit
  rw [globalStruct_actual_initializer_eq]
  simp [compileProgExactHOLW,compileStoreExactHOLW,compileExpExactHOLW,compileExpExactHOLWList,
    sizeOfShapeHOL,sizeOfShapesHOL,nestedDecsHOL,globalStructCrepContext,mkCtxtExactHOL]
  with_unfolding_all rfl
private theorem pairCallFactor : callClockFactor globalStructActualLoopContext (globalStructCallPrograms.map (fun row => (row.2.1,row.2.2))) 9 globalStructActualEntryCrep = 390 := by
  rw [globalStruct_actualPrograms_eq]
  unfold globalStructActualBody globalStructActualEntryCrep globalStructActualInit
  rw [globalStruct_actual_initializer_eq,globalStructWitness_lowering]
  simp [compileProgExactHOLW,compileStoreExactHOLW,compileReturnExactHOLW,compileExpExactHOLW,compileExpExactHOLWList,
    sizeOfShapeHOL,sizeOfShapesHOL,loadShapeBytesHOLW,nestedDecsHOL,globalStructCrepContext,mkCtxtExactHOL]
  with_unfolding_all rfl

private theorem pairUnifiedOpt : loweredProgramOptLimit pairCrepContext
    (.seq (nestedSeqHOL inits) (.call none (newMainNameHOL globalStructProgram) []))
    (globalEntryCrep globalStructProgram 8 globalStructContext entries) (globalSourcePrograms globalStructProgram)
    (2*[globalStructDecl].length+(callEntryStateHOLFinite (installSourceFunctions post entries) HolFiniteMapExact.empty).clock+3)
    globalStructActualLoopContext globalStructActualLoopContext .ln = 501673918 := by
  unfold loweredProgramOptLimit
  rw [compiledEntry,pairSourcePrograms]
  have sourceClock : (callEntryStateHOLFinite (installSourceFunctions post entries) HolFiniteMapExact.empty).clock = 8 := rfl
  have crepClock : (globalEntryCrep globalStructProgram 8 globalStructContext entries).clock = 9 := rfl
  simp only [sourceClock,crepClock,List.length_cons,List.length_nil]
  rw [pairStatementWeight,pairTableWeight,pairCallFactor,pairSyntaxWeight,globalStruct_loopCodeWeight]
  change loopVisitWeight (optimiseHOL globalStructActualEntryLoop) + max (loopVisitWeight (optimiseHOL globalStructActualEntryLoop)) (62+2) * (2 * (31 + max 31 (62+2) * (9 + 390 * (max 12 12 * 13 + 1)))) = 501673918
  rw [globalStruct_loopEntryWeight]
  decide
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open SteppedFlapjack.StackRemoveSteps.CompCorrect SteppedFlapjack.StackRemoveSteps SteppedFlapjack.StackAllocSteps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics SteppedFlapjack.StackToLabSteps
private theorem numericBackend (code : List (Nat × HolProg 64))
    (factor : costFromFields riscvConfig.addrOffset 0 (.call none (.inl Flapjack.Compiler.Backend.BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf code)) [4] (fixtureStackOracle (fixtureCompilerConfig code)) = 1950) :
    948 * stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset [4] code
      (fixtureStackOracle (fixtureCompilerConfig code))
      (1 + 31 * (6*501673918+1 + ((29+1)*(6*501673918+1)+1))) = 304799299979875449948 := by
  have uniform : uniformFactor (width := 64) countdownRiscVBackend.dataConf = 19 := by decide +kernel
  have init : loopOnlyCost 0 (initCode (StackToLab.isGenGc countdownRiscVBackend.dataConf.gcKind) (2^53-1) 24 : HolProg 64) = 361 := by decide +kernel
  unfold fixtureStackOracle
  rw [stackLabTickLimit_emptyOracle]
  dsimp only
  unfold fixtureStackOracle at factor
  rw [factor,uniform,init]
  simp [flattenStepFactor]
private theorem numericFromInputs (code : List (Nat × HolProg 64)) (bs : List (BitVec 64)) (opt ww sw : Nat)
    (bitmap : bs = [4]) (optEq : opt = 501673918) (wordEq : ww = 29) (stackEq : sw = 31)
    (factor : costFromFields riscvConfig.addrOffset 0 (.call none (.inl Flapjack.Compiler.Backend.BvlToBvi.initGlobalsLocation) none : HolProg 64)
      (sptFromAList (code1 countdownRiscVBackend.dataConf code)) [4] (fixtureStackOracle (fixtureCompilerConfig code)) = 1950) :
    948 * stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset bs code
      (fixtureStackOracle (fixtureCompilerConfig code))
      (1 + max 1 sw * (6*opt+1 + ((max 1 ww+1)*(6*opt+1)+1))) = 304799299979875449948 := by
  subst bs; subst opt; subst ww; subst sw
  exact numericBackend code factor
theorem pairUnified_clock_numeric : pairUnifiedTicks = 304799299979875449948 := by
  unfold pairUnifiedTicks
  dsimp only
  apply numericFromInputs
  case bitmap => rw [pairSourceBitmaps]; exact globalStruct_nativeBitmap
  case optEq =>
    have contextEq : mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable (globalSourcePrograms globalStructProgram)) 0 = globalStructActualLoopContext := by
      rw [pairSourcePrograms]
      rfl
    rw [contextEq]
    exact pairUnifiedOpt
  case wordEq => rw [pairSourceWords]; exact globalStruct_wordCodeWeight
  case stackEq => rw [pairSourceCode]; exact globalStruct_stackCodeWeight
  case factor => rw [pairSourceCode]; exact globalStruct_tickFactor _
theorem pairGeneral_namedSource : ∃ finalMachine finalFfi,
    evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart (globalSourceCode globalStructProgram))) sourceFfi
      pairUnifiedTicks (configuredMachineState (globalSourceCode globalStructProgram) (globalSourceBitmaps globalStructProgram)) =
        (.halt .success,finalMachine,finalFfi) ∧
    semanticsDecls globalStructBase (ofString "main") namedGlobalStructProgram = .terminate .success finalFfi.ioEvents := by
  obtain ⟨machine,ffi,_,_,run,events⟩ := pairUnified_machine
  refine ⟨machine,ffi,run,?_⟩
  rw [events]
  exact namedGlobalStruct_semantics

end SteppedFlapjack.Concrete
