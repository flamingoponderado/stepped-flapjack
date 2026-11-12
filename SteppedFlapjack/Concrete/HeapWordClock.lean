import SteppedFlapjack.Concrete.HeapWordClockInputs
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackRemove SteppedFlapjack.StackRemoveSteps.CompCorrect SteppedFlapjack.StackRemoveSteps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics SteppedFlapjack.StackToLabSteps SteppedFlapjack.StackAllocSteps
open SteppedFlapjack.LoopLiveSteps SteppedFlapjack.WordSimpSteps SteppedFlapjack.StackSteps SteppedFlapjack.CrepToLoopSteps
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString SteppedFlapjack.PanToCrepSteps
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private theorem heapPrograms : compileProgDeclsHOLW (compileTopExactHOL (heapSimpFunctions.map DeclHOL.function) (ofString "main")) = crepPrograms (progToHOL (panSimpProg heapWordWitness)) := by
  rw [heap_simpDeclarations]
  rfl
private theorem heapMain : newMainNameHOL (heapSimpFunctions.map DeclHOL.function) = entryName (progToHOL (panSimpProg heapWordWitness)) := by
  rw [heap_simpDeclarations]
  rfl
private theorem heapEntrySyntax (ctx : CrepToLoopContextExact) (name : MlString) :
    callSyntaxCost ctx (.seq .skip (.call none name []) : CrepProgHOL 64) = 5 := by
  simp [callSyntaxCost,callArgumentsCost,compileExpsHOLExact,loopNestedSeqHOL,LoopSteps.structuralWeight]
private theorem heapEntryOpt (ctx : CrepToLoopContextExact) (name : MlString) :
    loopVisitWeight (optimiseHOL (compileHOLExact ctx .ln (.seq .skip (.call none name []) : CrepProgHOL 64))) = 10 := by
  have generic (lab : Nat) : loopVisitWeight (optimiseHOL
      (.seq .skip (.seq (.call none (some lab) [] none) .skip) : HolLoopProg 64)) = 10 := by
    simp [optimiseHOL,loopCallCompHOL,Flapjack.compHOL,shrinkHOL,markAllHOL,loopVisitWeight]
  simpa [compileHOLExact,compileExpsHOLExact,genTemps,loopNestedSeqHOL] using generic (findLabExact ctx name)

private theorem heapRawLoopWeight : loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa
    (compileProgDeclsHOLW (compileTopExactHOL (heapSimpFunctions.map DeclHOL.function) (ofString "main"))))) = 42 := by
  exact (congrArg (fun programs => loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa programs)) = 42) heapPrograms).mpr heapClock_staticWeights.2.2.2.1

private theorem heapFactors (ctx : CrepToLoopContextExact) (name : MlString)
    (programs : List (MlString × List Nat × CrepProgHOL 64))
    (h : loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa programs)) = 42) :
    max (callSyntaxCost ctx (.seq .skip (.call none name []) : CrepProgHOL 64))
      (loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa programs))+2) = 44 := by
  rw [heapEntrySyntax,h]
  decide
private theorem heapOptFactors (ctx : CrepToLoopContextExact) (name : MlString)
    (programs : List (MlString × List Nat × CrepProgHOL 64))
    (h : loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa programs)) = 42) :
    max (loopVisitWeight (optimiseHOL (compileHOLExact ctx .ln (.seq .skip (.call none name []) : CrepProgHOL 64))))
      (loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa programs))+2) = 44 := by
  rw [heapEntryOpt,h]
  decide

private theorem heapBackendNumeric (code : List (Nat × HolProg 64)) (hfactor : costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64) (sptFromAList (code1 countdownRiscVBackend.dataConf code)) [4] (fixtureStackOracle (fixtureCompilerConfig code)) = 1950) : callPipelineTicks code [4] 7 4 3 174 8 5 44 10 44 15 17 7 = 29426197640928697548 := by
  have uniform : uniformFactor (width := 64) countdownRiscVBackend.dataConf = 19 := by decide +kernel
  have init : loopOnlyCost 0 (initCode (StackToLab.isGenGc countdownRiscVBackend.dataConf.gcKind) (2^53-1) 24 : HolProg 64) = 361 := by decide +kernel
  unfold callPipelineTicks fixtureStackOracle
  dsimp only
  rw [stackLabTickLimit_emptyOracle]
  dsimp only
  unfold fixtureStackOracle at hfactor
  rw [hfactor,uniform,init]
  simp [flattenStepFactor]

private theorem heapClock_fromInputs (code : List (Nat × HolProg 64)) (bitmap : List (BitVec 64))
  (cw tw pw cf i sw lf ow ofac ww stackw count : Nat)
  (a : code = (supportedNative heapWordWitness).2.2.2) (b : bitmap = [4])
  (c : cw = 7) (d : tw = 4) (e : pw = 3) (f : cf = 174) (g : i = 8)
  (h : sw = 5) (j : lf = 44) (k : ow = 10) (l : ofac = 44) (m : ww = 15) (n : stackw = 17) (o : count = 7) :
  callPipelineTicks code bitmap cw tw pw cf i sw lf ow ofac ww stackw count = 29426197640928697548 := by
  subst code; subst bitmap; subst cw; subst tw; subst pw; subst cf; subst i; subst sw; subst lf; subst ow; subst ofac; subst ww; subst stackw; subst count
  exact heapBackendNumeric _ (heapClock_targetFactor _)

/-- The heap witness clock, evaluated from its actual program and fixture. -/
theorem heapClock_numeric : heapTicks = 29426197640928697548 := by
  unfold heapTicks
  apply heapClock_fromInputs
  case a => exact congrArg (fun n => n.2.2.2) heapNative_same
  case b =>
    have hs : CallFreeSupported heapWordWitness := ⟨.seq (.store (.const _) (.const _)) (.ret (.load (.const _))), heapWordWitness_ranged⟩
    exact (congrArg Prod.fst heapNative_same).trans (supported_native_bitmap heapWordWitness hs)
  case c =>
    simp only [heapPrograms,compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,List.flatMap_nil]
    rw [heapClock_staticWeights.2.2.1]
    simp [CrepSteps.statementWeight]
  case j =>
    let programs := compileProgDeclsHOLW (compileTopExactHOL (heapSimpFunctions.map DeclHOL.function) (ofString "main"))
    change max (callSyntaxCost _ _) (loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa programs))+2) = 44
    conv_lhs => arg 1; arg 2; simp only [compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,List.flatMap_nil]
    exact heapFactors (mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0) (newMainNameHOL (heapSimpFunctions.map DeclHOL.function)) programs heapRawLoopWeight
  case l =>
    let programs := compileProgDeclsHOLW (compileTopExactHOL (heapSimpFunctions.map DeclHOL.function) (ofString "main"))
    change max (loopVisitWeight (optimiseHOL (compileHOLExact _ .ln _))) (loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa programs))+2) = 44
    conv_lhs => arg 1; arg 1; arg 1; arg 3; simp only [compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,List.flatMap_nil]
    exact heapOptFactors (mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable programs) 0) (newMainNameHOL (heapSimpFunctions.map DeclHOL.function)) programs heapRawLoopWeight
  case d => exact heapClock_staticWeights.1
  case e => exact heapClock_staticWeights.2.1
  case g => rfl
  case h =>
    simp only [compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,List.flatMap_nil]
    exact heapEntrySyntax _ _
  case k =>
    simp only [compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,List.flatMap_nil]
    exact heapEntryOpt _ _
  case f =>
    simp only [heapPrograms,heapMain,compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,List.flatMap_nil]
    exact heapClock_callFactor _ _
  case m =>
    have eq := congrArg (fun p => max 1 (wordCodeWeight (sptFromAList p.2))) heapAllocator_same
    exact eq.trans (by rw [heapClock_staticWeights.2.2.2.2.1]; decide)
  case n =>
    have eq := congrArg (fun p => max 1 (stackCodeWeight (sptFromAList p.2.2.2))) heapNative_same
    exact eq.trans (by rw [heapClock_staticWeights.2.2.2.2.2]; decide)
  case o => rfl

/-- The heap store/load program halts at its kernel-checked numeric clock. -/
theorem heapFixture_machine_numeric :
    let native := (compileNative riscvConfig false
    (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig
      (loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa
       (compileProgDeclsHOLW (compileTopExactHOL (heapSimpFunctions.map DeclHOL.function) (ofString "main")))))).2)
    ∃ compilerFinal, Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      (heapHOLFunctions.map DeclHOL.function) = some (fixtureCodeBytes native.2.2.2,native.1,compilerFinal) ∧
    ∃ machine ffi, evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart native.2.2.2)) sourceFfi
      29426197640928697548 (configuredMachineState native.2.2.2 native.1) = (.halt .success,machine,ffi) ∧
      ffi.ioEvents = sourceFfi.ioEvents ∧
      Flapjack.PanSemStateFiniteExact.semanticsDecls {sourceTemplate with clock := 0} (ofString "main")
        (heapHOLFunctions.map DeclHOL.function) = .terminate .success ffi.ioEvents := by
  simpa only [heapClock_numeric] using heapFixture_machine

end SteppedFlapjack.Concrete
