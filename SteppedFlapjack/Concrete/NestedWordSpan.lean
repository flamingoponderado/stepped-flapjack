import SteppedFlapjack.Concrete.NestedLoopRun
import SteppedFlapjack.Concrete.WordSpan
import SteppedFlapjack.Concrete.SourceState
import SteppedFlapjack.Concrete.FixtureWordStarter
import SteppedFlapjack.Concrete.CountdownWordSpan
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Compiler.Backend Flapjack.LoopSemStateFiniteExact Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.LoopLiveSteps SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps
open SteppedFlapjack.WordSimpSteps
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 100000 in
set_option linter.unusedSimpArgs false in
/-- The counted nested source reaches the native initialized Word state. -/
theorem nested_configured_optimized_start (code : List (Nat × StackLang.HolProg 64))
    (cfg : LabToTarget.Config) (bs : List (BitVec 64))
    (fits : 0xa0020018 + bs.length*8 ≤ sourceBase)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) (frame : Nat)
    (frameLookup : let loops := compileProgHOLExact riscvConfig.isa nestedCallCrepPrograms
      let words := (compile phase3WordConfig riscvConfig (loopToWordCompileHOL loops)).2
      sptLookup 64 (configuredWord code words cfg bs).stackSize = some frame) :
    let loops := compileProgHOLExact riscvConfig.isa nestedCallCrepPrograms
    let rawWords := loopToWordCompileHOL loops
    let words := (compile phase3WordConfig riscvConfig rawWords).2
    let state := {(configuredWord code words cfg bs) with clock := 6*nestedOptimizedLoopBound+1}
    ∃ post, WordSemStateFiniteExact.evaluate (.call none (some 64) [0] none) state =
      (some (.result (.loc 1 0) [.word 7]),post) ∧ post.ffi = sourceFfi ∧
      WordSteps.steps (.call none (some 64) [0] none) state ≤
        1 + max 1 (wordCodeWeight (sptFromAList (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig rawWords).2)) * (6*nestedOptimizedLoopBound+1) := by
  let n := bs.length
  let source := {nestedSourceState n with clock := 6}
  let memory : BitVec 64 → Option (PanValue (RiscV.Word 64)) := fun a => some (.word (initialWordFor n a))
  let production := {nestedCountedProduction with clock := 6, memory := memory}
  let _ : DecidablePred source.memaddrs := by
    change DecidablePred ordinaryAddress
    infer_instance
  have related : PanSemStateRelExec production source.toExact := by
    obtain ⟨a,b,c,d,e,f,g,h,_,j,k,l,m⟩ := nestedCounted_related_bitmaps n
    exact ⟨a,b,c,d,e,f,g,h,rfl,j,k,l,m⟩
  have shape : CallSupportedIn [] nestedCallEntry :=
    .call "answer" "middle" [] (by simp) (.base (.ret (.local "answer" (by simp))))
  have ranged : PanSemStateRelExecRanged production := by
    simp [production,nestedCountedProduction,sourceProduction,PanSemStateRelExecRanged,StructContextByteRanged,StructContext.toHOL]
  have words : WordLocals production.locals := by
    simpa [production,nestedCountedProduction,sourceProduction] using wordLocals_empty
  have codeRanged : ∀ name entry, panSemCodeLookup production.code name = some entry → PanLangEntryByteRanged entry := by
    simpa [production,nestedCountedProduction,PanSemCodeRanged] using
      panSemCodeRanged_of_functionEntries sourceProduction nestedCallDeclarations nestedCall_declarations_ranged
  have outside : ¬ source.memaddrs source.topAddr := by
    simp [source,nestedSourceState,sourceTemplateFor,sourceTemplate,ordinaryAddress,heapTop,fixtureHeapEnd,heapEnd,
      stackStart,ramEnd,ramStart,ramSize,stackSize,globalsWords,sourceBase]
  have aligned : panGlobalsByteAlignedHOL source.topAddr := by
    change panGlobalsByteAlignedHOL heapTop
    change BitVec.ofNat 64 ((heapTop.toNat / 8) * 8) = heapTop
    decide
  have sourceCode : source.code = HolFiniteMapExact.empty.updateList (functionsHOL (nestedCallDeclarations.map declToHOL)).reverse := by
    exact nestedEntryCode
  have sourceCodeRel : PanSimp.CodeRel source.code source.code := nestedEntryCodeRel
  have sourceRun := nestedCounted_run memory (riscv64PanValueFfiContext (fun _ => false))
    (fun _ _ => none) (fun _ _ _ _ _ _ _ => none)
  have span := countedCalls_initializedWord shape production source related ranged words
    (by simp [nestedCallEntry,ProgByteRanged,ExpByteRanged,ShapeByteRanged,NameRanged])
    codeRanged (by simpa [production] using nestedCounted_shapes) source.code sourceCodeRel
    (functionsHOL (nestedCallDeclarations.map declToHOL)) sourceCode nestedEntryShapes
    nestedHOLFunctions (Flapjack.Basis.Pure.MlString.ofString "main")
    (by simpa only [nestedHOLDeclarations] using sourceCode)
    (by rw [nestedHOLDeclarations]; simp [nestedCallDeclarations,declToHOL,funDeclToHOL,functionsHOL,nestedCallEntry,panSimpProg,retToTail,seqAssoc,smartSeq,panSimpCompileHOL,seqAssocHOL,smartSeqHOL,retToTailHOL,progToHOL,expToHOL,shapeToHOL])
    (by simp [source,nestedSourceState,sourceTemplateFor,sourceTemplate,HolFiniteMapExact.lookup_update,FUPDATE,ofString,MlString.explode_implode])
    rfl rfl rfl rfl
    (by rw [nestedHOLDeclarations]; simp [nestedCallDeclarations,declToHOL,funDeclToHOL,functionsHOL,shapeToHOL]; decide)
    nestedHOLFunctionShapes
    (by simpa only [nestedHOLDeclarations] using nestedCall_inline_selection_empty)
    outside aligned (riscv64PanValueFfiContext (fun _ => false)) (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) [] 8 6
    _ _ _ _ 7 (by simpa [production,panSemBitVec64MemoryAccess] using sourceRun) (by rfl)
    code cfg bs frame fits good rfl rfl rfl rfl rfl rfl (by intro a ha; rfl)
    (by simpa only [nestedHOLDeclarations,nestedCallCrepPrograms] using frameLookup)
  obtain ⟨sourceFinal,post,sourceResult,wordRun,wordBound,wordFfi,ffiRel⟩ := span
  have leafMiddle : (ofString "leaf" == ofString "middle") = false := by decide
  have leafMain : (ofString "leaf" == ofString "main") = false := by decide
  have middleMain : (ofString "middle" == ofString "main") = false := by decide
  have actual : ∃ final, source.evaluateHOLFiniteState (progToHOL nestedCallEntry) =
      (some (.returned (.val (.word 7))),final) ∧ final.ffi = sourceFfi := by
    simp [source,leafMain,middleMain,leafMiddle,evaluateHOLFiniteState_call,nestedSourceState,sourceTemplateFor,nestedCallEntry,progToHOL,
      expToHOL,shapeToHOL,sourceTemplate,evalListHOLFinite,evalListHOLExact,
      PanSemStateFiniteExact.lookupCodeHOLFinite,lookupCodeHOLExact,HolFiniteMapExact.lookup_update,FUPDATE,
      evaluateHOLFiniteState_decCall_fixClockRewrite,evaluateHOLFiniteState_return,callEntryStateHOLFinite,
      evalHOLExact,shapeOfHOLExact,shapeEqHOL,setVarHOLFinite,emptyLocalsHOLFinite]
  obtain ⟨actualFinal,actualRun,actualFfi⟩ := actual
  have finalEq : sourceFinal = actualFinal := (Prod.mk.inj (sourceResult.symm.trans actualRun)).2
  have outputFfi : post.ffi = sourceFfi := by rw [wordFfi,finalEq,actualFfi]
  rw [nestedHOLDeclarations] at wordRun wordBound
  have codeWeight : CrepSteps.codeWeight (compileProgDeclsHOLW
      (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main"))) = 4 := by
    rw [nestedCall_crep_code]
    rfl
  simp only [compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,
    CrepSteps.statementWeight,codeWeight,show max 3 4 = 4 by decide] at wordRun wordBound
  refine ⟨post,?_,outputFfi,?_⟩
  · simpa [nestedHOLDeclarations,nestedCallCrepPrograms,nestedOptimizedLoopBound,nestedOptimizedLoopBody,nestedLoopBound,
      nestedLoopBudget,nestedCrepLimit,nestedSourceEntryLimit,nestedLoopContext,nestedCrepBody,nestedPanContext,
      production,source,nestedSourceState,sourceTemplateFor,sourceTemplate,concreteDeclCrepState,noGlobalsLoweredPreCall,
      concreteDeclLoopState,newMainNameHOL,nestedCallDeclarations,declToHOL,funDeclToHOL,functionsHOL,freshNameMlS,mlstrAppend,
      ofString,MlString.explode_implode,compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,
      Nat.add_assoc,firstLoopName] using wordRun
  · simpa [nestedHOLDeclarations,nestedCallCrepPrograms,nestedOptimizedLoopBound,nestedOptimizedLoopBody,nestedLoopBound,
      nestedLoopBudget,nestedCrepLimit,nestedSourceEntryLimit,nestedLoopContext,nestedCrepBody,nestedPanContext,
      production,source,nestedSourceState,sourceTemplateFor,sourceTemplate,concreteDeclCrepState,noGlobalsLoweredPreCall,
      concreteDeclLoopState,newMainNameHOL,nestedCallDeclarations,declToHOL,funDeclToHOL,functionsHOL,freshNameMlS,mlstrAppend,
      ofString,MlString.explode_implode,compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,
      Nat.add_assoc,firstLoopName] using wordBound
end SteppedFlapjack.Concrete
