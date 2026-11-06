import SteppedFlapjack.PanToCrepSteps.CountedAssignLoopEntry
import SteppedFlapjack.PanToCrepSteps.NativeTailClockOutcome
import SteppedFlapjack.CrepToLoopSteps.NativeTailFrontendSetup
import SteppedFlapjack.PanToCrepSteps.GlobalTailWord
import SteppedFlapjack.PanToCrepSteps.GlobalPanCodeRel

/-! Native initialization for the counted assignment-loop entry. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.LabToTargetSteps

/-- Whole-compiler and native-machine inputs for a zero-argument Loop entry.
The frame, Word state, code relations, and resource outcome are derived. -/
structure AssignLoopCompilerInputs {F : Type}
    (declarations : List (DeclHOL 64)) (start : MlString) (caller : PanToCrepContextExact 64)
    (loopCtxt : CrepToLoopContextExact) (entry : HolLoopProg 64) (limit : Nat)
    (loop : LoopSemStateFiniteExact 64 F) where
  arch : AsmArchitecture
  crepPrograms : List (MlString × List Nat × CrepProgHOL 64)
  programsEq : crepPrograms = compileProgDeclsHOLW (compileTopExactHOL declarations start)
  callerEq : caller = mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
    (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start))) (sizeOfShapeHOL (.comb [])-1)
    (getEidsFromDeclsHOL (compileTopExactHOL declarations start))
  loopContextEq : loopCtxt = mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable crepPrograms) 0
  wc : Flapjack.Compiler.Backend.WordToWord.Config
  ac : AsmConfigExact 64
  loopCode : loop.code = sptFromAList (compileProgHOLExact arch crepPrograms)
  stack : StackSemStateFiniteExact 64 LabToTarget.Config F
  coracle : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64))
  codeEq : stack.code = sptFromAList (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
    (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))).2).2.2.2
  bitmapsPrefix : (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
    (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))).2).1.IsPrefix stack.bitmaps
  ok : Flapjack.WordToStackProofs.InitializationStateRel.initStateOk ac (ac.regCount-(5+ac.avoidRegs.length)) stack coracle
  data : LoopWordDataRel loop
    {callEnv [(.loc 1 0 : WordLocW 64)] (some 0)
      (Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit ac (ac.regCount-(5+ac.avoidRegs.length)) stack
        (sptFromAList (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))).2) coracle)
      with code := sptFromAList (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))}

/-- Compiler inputs together with the direct-entry machine setup. -/
structure AssignLoopNativeInputs {F : Type}
    (declarations : List (DeclHOL 64)) (start : MlString) (caller : PanToCrepContextExact 64)
    (loopCtxt : CrepToLoopContextExact) (entry : HolLoopProg 64) (limit : Nat)
    (loop : LoopSemStateFiniteExact 64 F)
    extends AssignLoopCompilerInputs declarations start caller loopCtxt entry limit loop where
  backend : NativeTailMachineSetup stack firstLoopName (tailStackReplayLimit ac 1 firstLoopName wc.regAlg
    (ac.regCount-(5+ac.avoidRegs.length)) (entryColour wc (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms)) firstLoopName)
    entry (assignLoopEntryWordContext entry) (firstLoopName,2)
    (sptFromAList (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))).2) limit)

/-- Derive the source/Crep/Loop code relations and selected Word entry once
for any supported source main body. -/
theorem AssignLoopCompilerInputs.frontendFacts {σ : Type}
    (declarations : List (DeclHOL 64)) (start : MlString) (initializers : List (ProgHOL 64))
    (globals : PanGlobalsContextExact 64) (caller : PanToCrepContextExact 64)
    (loopCtxt : CrepToLoopContextExact) (entry : HolLoopProg 64) (limit : Nat)
    (pan : PanSemStateFiniteExact 64 σ) (crep : CrepSemHOLState 64 σ) (target : LoopSemStateFiniteExact 64 σ)
    (native : AssignLoopCompilerInputs declarations start caller loopCtxt entry limit target)
    (entryDef : entry = assignLoopEntryProgram declarations initializers caller loopCtxt .ln)
    (original : ProgHOL 64) (returnShape : ShapeHOL)
    (globalFound : (functionsHOL declarations).lookup start = some ([],original,returnShape))
    (funs exns : List (DeclHOL 64))
    (globalCompiled : globalLoweredDecs declarations start = (initializers,funs,exns,globals))
    (panCode : pan.code = HolFiniteMapExact.empty.updateList (functionsHOL (compileTopExactHOL declarations start)).reverse)
    (crepCode : crep.code = alistToFmapCodeExact (compileProgDeclsHOLW (compileTopExactHOL declarations start)))
    (unique : ((compileProgDeclsHOLW (compileTopExactHOL declarations start)).map Prod.fst).Nodup)
    (localised : ∀ e ∈ functionsHOL (compileTopExactHOL declarations start), localisedProgHOL e.2.2.1 = true)
    (preShapes : ∀ n ps p, (n,ps,p) ∈ compileToCrepExactHOLW (compileTopExactHOL declarations start) → SupportedCodeBody p)
    (noTail : ∀ n ps init callee, (n,ps,.seq init (.call none callee [])) ∈
      compileToCrepExactHOLW (compileTopExactHOL declarations start) →
      callee ∉ (functionsHOL ((compileTopExactHOL declarations start).filter inlinableHOL)).map Prod.fst)
    (initShape : BranchProgram caller (nestedSeqHOL initializers)) :
    codeRelExactHOLW caller pan.code crep.code ∧
    (∀ n ps body, (n,ps,body) ∈ native.crepPrograms → SupportedCodeBody body) ∧
    crepToLoopCodeRelExact loopCtxt crep.code target.code ∧
    (firstLoopName,1,(LoopToWord.compHOL (assignLoopEntryWordContext entry) entry (firstLoopName,2)).1) ∈
      loopToWordCompileHOL (compileProgHOLExact native.arch native.crepPrograms) := by
  obtain ⟨panCodeRelCanonical,programShapesCanonical⟩ := global_supported_panCrep_codeAndShapes
    declarations start pan crep panCode crepCode unique localised preShapes noTail
  have panCodeRel : codeRelExactHOLW caller pan.code crep.code := by
    simpa only [native.callerEq] using panCodeRelCanonical
  have programShapes : ∀ n ps body, (n,ps,body) ∈ native.crepPrograms → SupportedCodeBody body := by
    simpa only [native.programsEq] using programShapesCanonical
  obtain ⟨preInitializers,preRest,preEntry⟩ := globalEntry_preInline declarations start
    original returnShape globalFound
  have preMember : (start,[],.seq (compileProgExactHOLW
      (mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
        (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start))) (sizeOfShapeHOL (.comb [])-1)
        (getEidsFromDeclsHOL (compileTopExactHOL declarations start))) (nestedSeqHOL preInitializers))
      (.call none (newMainNameHOL declarations) [])) ∈
      compileToCrepExactHOLW (compileTopExactHOL declarations start) := by
    rw [preEntry]
    simp
  have notInline : newMainNameHOL declarations ∉
      (functionsHOL ((compileTopExactHOL declarations start).filter inlinableHOL)).map Prod.fst :=
    noTail start [] _ (newMainNameHOL declarations) preMember
  have compiledInitShape : CrepToLoopSteps.BranchProgram (compileProgExactHOLW
      (mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
        (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start))) (sizeOfShapeHOL (.comb [])-1)
        (getEidsFromDeclsHOL (compileTopExactHOL declarations start))) (nestedSeqHOL initializers)) := by
    rw [← native.callerEq]
    exact branch_compile initShape
  have actualLookup := globalEntry_nonInline_crep_lookup declarations start initializers returnShape original globalFound funs exns globals (by simpa [globalLoweredDecs] using globalCompiled)
    compiledInitShape notInline crep
  have nativeLookup : holAlookup native.crepPrograms start = some ([],
      .seq (compileProgExactHOLW caller (nestedSeqHOL initializers)) (.call none (newMainNameHOL declarations) [])) := by
    simpa only [native.programsEq,native.callerEq] using actualLookup
  have nativeUnique : (native.crepPrograms.map Prod.fst).Nodup := by
    simpa only [native.programsEq] using unique
  have compiledCodeRel := wholeCrep_supported_executable_codeRel native.arch native.crepPrograms start
    (.seq (compileProgExactHOLW caller (nestedSeqHOL initializers)) (.call none (newMainNameHOL declarations) []))
    nativeUnique nativeLookup programShapes
  have codeRel : crepToLoopCodeRelExact loopCtxt crep.code target.code := by
    simpa only [native.loopContextEq,crepCode,← native.programsEq,native.loopCode] using compiledCodeRel
  have actualMember := globalEntry_nonInline_word_member native.arch declarations start initializers returnShape original globalFound funs exns globals (by simpa [globalLoweredDecs] using globalCompiled)
    compiledInitShape notInline crep
  have entryMember : (firstLoopName,1,(LoopToWord.compHOL (assignLoopEntryWordContext entry) entry (firstLoopName,2)).1) ∈
      loopToWordCompileHOL (compileProgHOLExact native.arch native.crepPrograms) := by
    simpa [entryDef,assignLoopEntryProgram,assignLoopEntryWordContext,native.programsEq,native.loopContextEq,native.callerEq,
      compFuncHOLExact,listToNumSetHOLExact] using actualMember
  exact ⟨panCodeRel,programShapes,codeRel,entryMember⟩

/-- Compose a proved source-return simulation with compiler-selected native
initialization, covering successful entry and frame resource failure. -/
theorem AssignLoopNativeInputs.machineBound {σ : Type}
    (declarations : List (DeclHOL 64)) (start : MlString) (caller : PanToCrepContextExact 64)
    (loopCtxt : CrepToLoopContextExact) (entry : HolLoopProg 64) (limit : Nat)
    (target : LoopSemStateFiniteExact 64 σ)
    (native : AssignLoopNativeInputs declarations start caller loopCtxt entry limit target)
    (programShapes : ∀ n ps body, (n,ps,body) ∈ native.crepPrograms → SupportedCodeBody body)
    (entryMember : (firstLoopName,1,(LoopToWord.compHOL (assignLoopEntryWordContext entry) entry (firstLoopName,2)).1) ∈
      loopToWordCompileHOL (compileProgHOLExact native.arch native.crepPrograms))
    (sourceFinal : PanSemStateFiniteExact 64 σ)
    (ready : ∀ word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) σ,
      loopToWordStateRelHOLExact {target with locals := .ln} word →
      ∃ extra, NativeReturnedReady entry {target with locals := .ln, clock := target.clock+extra}
        {word with clock := word.clock+extra} limit sourceFinal) :
    ∃ outcome ticks finalMachine finalFfi,
      ticks ≤ max (native.backend.successTickLimit native.wc native.ac
        (loopToWordCompileHOL (compileProgHOLExact native.arch native.crepPrograms))
        entry (assignLoopEntryWordContext entry) (firstLoopName,2)) native.backend.resourceTickLimit ∧
      evaluateTargetHOL native.backend.mc native.backend.lab.ffi ticks native.backend.machine =
        (.halt outcome,finalMachine,finalFfi) ∧
      ((outcome = .success ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents) ∨
        (outcome = .resourceLimitHit ∧
          (finalFfi.ioEvents <+: sourceFinal.ffi.ioEvents ∨ finalFfi.ioEvents = native.stack.ffi.ioEvents))) := by
  let initial := {target with locals := .ln}
  rcases wholeNativeTail_frontend_setup_or_resource native.arch native.crepPrograms programShapes
      native.wc native.ac entry (assignLoopEntryWordContext entry) (firstLoopName,2) firstLoopName entryMember
      initial (by simpa [initial] using native.loopCode) native.stack native.coracle native.codeEq native.bitmapsPrefix native.ok limit
      (by simpa [initial,LoopWordDataRel] using native.data) native.backend with success | resource
  · obtain ⟨word,setup,contextEq,machineEq,mcEq,labEq,tickEq,wordRel,base,frameSize,wordLocals⟩ := success
    obtain ⟨extra,nativeReady⟩ := ready word wordRel
    obtain ⟨outcome,ticks,finalMachine,finalFfi,bound,run,correspondence⟩ :=
      NativeReturnedReady.run_shifted (loop := initial) (sourceFinal := sourceFinal) extra nativeReady setup base frameSize (by rfl) (by simpa [assignLoopEntryWordContext] using contextEq) wordLocals
    refine ⟨outcome,ticks,finalMachine,finalFfi,?_,?_,?_⟩
    · rw [tickEq] at bound
      exact bound.trans (Nat.le_max_left _ _)
    · simpa only [mcEq,labEq,machineEq] using run
    · rcases correspondence with success | ⟨resource,events⟩
      · exact Or.inl success
      · exact Or.inr ⟨resource,Or.inl events⟩
  · obtain ⟨ticks,finalMachine,finalFfi,bound,run,events⟩ := resource
    exact ⟨.resourceLimitHit,ticks,finalMachine,finalFfi,bound.trans (Nat.le_max_right _ _),run,
      Or.inr ⟨rfl,Or.inr events⟩⟩

/-- A bounded counted assignment-loop program yields an actual bounded native
RISC-V run, including the entry-frame resource case. -/
theorem counted_assignLoop_native_riscv {σ : Type}
    (declarations : List (DeclHOL 64)) (start : MlString) (initializers : List (ProgHOL 64))
    (globals : PanGlobalsContextExact 64) (caller : PanToCrepContextExact 64)
    (condition assignment : Exp (RiscV.Word 64)) (name : VarName)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64)))
    (conditionRanged : ExpByteRanged condition) (assignmentRanged : ExpByteRanged assignment)
    (nameRanged : NameRanged name) (fuel : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source pan middle : PanSemStateFiniteExact 64 σ) (crep : CrepSemHOLState 64 σ)
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (finalLocals : VarName → Option (PanValue (RiscV.Word 64))) (loopCost budget : Nat) (returned : BitVec 64)
    (clock : loopCost ≤ source.clock*(panValueExpStepCost condition+panValueExpStepCost assignment+2) +
      (panValueExpStepCost condition+1))
    (budgetBound : loopCost+5 ≤ budget)
    (loopExec : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
      production.locals production.globals production.memory production.ffi (.while condition (.assign .local name assignment))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal finalLocals production.globals production.memory production.ffi,loopCost))
    (conditionShape : ScalarExpression (ctxtFcExactHOL caller.funcs caller.eids [] [] []) (expToHOL condition))
    (bodyShape : BranchProgram (ctxtFcExactHOL caller.funcs caller.eids [] [] [])
      (.assign .local (ofString name) (expToHOL assignment)))
    (panCode : pan.code = HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse)
    (initRun : pan.evaluateHOLFiniteState (nestedSeqHOL initializers) = (none,middle))
    (sourceFound : source.code.lookup (newMainNameHOL declarations) = some ([],
      .seq .skip (.seq (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment)))
        (.return (.const returned))),.one))
    (entryClock : middle.clock ≠ 0)
    (globalFound : (functionsHOL declarations).lookup start = some ([],
      .seq .skip (.seq (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment)))
        (.return (.const returned))),.one))
    (funs exns : List (DeclHOL 64))
    (globalCompiled : globalLoweredDecs declarations start = (initializers,funs,exns,globals))
    (globalRel : panGlobalsStateRelHOLExact true globals source (callEntryStateHOLFinite middle HolFiniteMapExact.empty))
    (panStateRel : panToCrepStateRelFiniteExact pan crep)
    (crepCode : crep.code = alistToFmapCodeExact (compileProgDeclsHOLW (compileTopExactHOL declarations start)))
    (unique : ((compileProgDeclsHOLW (compileTopExactHOL declarations start)).map Prod.fst).Nodup)
    (localised : ∀ entry ∈ functionsHOL (compileTopExactHOL declarations start), localisedProgHOL entry.2.2.1 = true)
    (preShapes : ∀ n ps p, (n,ps,p) ∈ compileToCrepExactHOLW (compileTopExactHOL declarations start) → SupportedCodeBody p)
    (noTail : ∀ n ps init callee, (n,ps,.seq init (.call none callee [])) ∈
      compileToCrepExactHOLW (compileTopExactHOL declarations start) →
      callee ∉ (functionsHOL ((compileTopExactHOL declarations start).filter inlinableHOL)).map Prod.fst)
    (panExcpRel : panToCrepExcpRelFiniteExact caller.eids pan.eshapes)
    (panLocalsRel : panToCrepLocalsRelFiniteExact caller pan.locals crep.locals)
    (initLocalised : localisedProgHOL (nestedSeqHOL initializers) = true)
    (initShape : BranchProgram caller (nestedSeqHOL initializers))
    (loopCtxt : CrepToLoopContextExact) (target : LoopSemStateFiniteExact 64 σ)
    (crepRel : crepToLoopStateRelExact crep target)
    (memRel : crepToLoopMemRelHOLExact crep.memory target.memory crep.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact crep.globals target.globals)
    (localsRel : crepToLoopLocalsRelExact loopCtxt .ln crep.locals target.locals)
    (native : AssignLoopNativeInputs declarations start caller loopCtxt (assignLoopEntryProgram declarations initializers caller loopCtxt .ln)
      (assignLoopEntryLimit declarations initializers globals caller condition assignment name returned pan budget loopCtxt .ln) target) :
    let entry := assignLoopEntryProgram declarations initializers caller loopCtxt .ln
    ∃ sourceResult sourceFinal,
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+3)
        production.locals production.globals production.memory production.ffi
        (.seq .skip (.seq (.while condition (.assign .local name assignment)) (.return (.const returned))))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (sourceResult,loopCost+5) ∧
      source.evaluateHOLFiniteState (.seq .skip (.seq (.while (expToHOL condition)
        (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned)))) =
          (some (.returned (.val (.word returned))),sourceFinal) ∧
      ∃ outcome ticks finalMachine finalFfi,
        ticks ≤ max (native.backend.successTickLimit native.wc native.ac
          (loopToWordCompileHOL (compileProgHOLExact native.arch native.crepPrograms))
          entry (assignLoopEntryWordContext entry) (firstLoopName,2)) native.backend.resourceTickLimit ∧
        evaluateTargetHOL native.backend.mc native.backend.lab.ffi ticks native.backend.machine =
          (.halt outcome,finalMachine,finalFfi) ∧
        ((outcome = .success ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents) ∨
          (outcome = .resourceLimitHit ∧
            (finalFfi.ioEvents <+: sourceFinal.ffi.ioEvents ∨ finalFfi.ioEvents = native.stack.ffi.ioEvents))) := by
  let entry := assignLoopEntryProgram declarations initializers caller loopCtxt .ln
  let limit := assignLoopEntryLimit declarations initializers globals caller condition assignment name returned pan budget loopCtxt .ln
  obtain ⟨sourceResult,sourceFinal,sourceExec,sourceRun,_⟩ :=
    counted_assignLoop_with_return condition assignment name context primitive handler functions
      conditionRanged assignmentRanged nameRanged fuel production source rel ranged finalLocals loopCost returned clock loopExec
  refine ⟨sourceResult,sourceFinal,sourceExec,sourceRun,?_⟩
  obtain ⟨panCodeRel,programShapes,codeRel,entryMember⟩ := native.toAssignLoopCompilerInputs.frontendFacts declarations start initializers globals caller
    loopCtxt entry limit pan crep target rfl
    (.seq .skip (.seq (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment)))
      (.return (.const returned)))) .one globalFound funs exns globalCompiled panCode crepCode unique localised preShapes noTail initShape
  let initial := {target with locals := .ln}
  have normalized := emptyLive_initial_relations loopCtxt crep target _ crepRel memRel globalsRel localsRel native.data
  apply native.machineBound declarations start caller loopCtxt entry limit target programShapes entryMember sourceFinal
  intro word wordRel
  obtain ⟨_,sourceFinal',_,_,_,_,_,sourceRun',_,_,_,_,_,_,_,_,_,extra,loopPost,_,_,_,_,_,_,_,_,_,_,_,nativeReady⟩ :=
    counted_assignLoop_globalEntry_riscv declarations start initializers globals caller condition assignment name context primitive handler
      functions conditionRanged assignmentRanged nameRanged fuel production source pan middle crep rel ranged finalLocals loopCost budget
      returned clock budgetBound loopExec conditionShape bodyShape panCode initRun sourceFound entryClock globalRel panStateRel panCodeRel
      panExcpRel panLocalsRel initLocalised initShape loopCtxt .ln initial word normalized.1 normalized.2.1 normalized.2.2.1
      (by simpa [initial] using codeRel) normalized.2.2.2.1 wordRel
  have finalEq : sourceFinal = sourceFinal' := (Prod.mk.inj (sourceRun.symm.trans sourceRun')).2
  subst sourceFinal'
  exact ⟨extra,nativeReady⟩

end SteppedFlapjack.PanToCrepSteps
