import SteppedFlapjack.PanToCrepSteps.CountedAssignLoopEntry
import SteppedFlapjack.PanToCrepSteps.NativeTailClockOutcome
import SteppedFlapjack.CrepToLoopSteps.NativeTailFrontendSetup

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
structure AssignLoopNativeInputs {F : Type}
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
  programShapes : ∀ name params body, (name,params,body) ∈ crepPrograms → SupportedCodeBody body
  wc : Flapjack.Compiler.Backend.WordToWord.Config
  ac : AsmConfigExact 64
  member : (firstLoopName,1,(LoopToWord.compHOL (assignLoopEntryWordContext entry) entry (firstLoopName,2)).1) ∈
    loopToWordCompileHOL (compileProgHOLExact arch crepPrograms)
  loopCode : loop.code = sptFromAList (compileProgHOLExact arch crepPrograms)
  loopEmpty : loop.locals = .ln
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
  backend : NativeTailMachineSetup stack firstLoopName (tailStackReplayLimit ac 1 firstLoopName wc.regAlg
    (ac.regCount-(5+ac.avoidRegs.length)) (entryColour wc (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms)) firstLoopName)
    entry (assignLoopEntryWordContext entry) (firstLoopName,2)
    (sptFromAList (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))).2) limit)

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
    (clock : fuel+1 ≤ source.clock+1)
    (finalLocals : VarName → Option (PanValue (RiscV.Word 64))) (loopCost budget : Nat) (returned : BitVec 64)
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
    (globalRel : panGlobalsStateRelHOLExact true globals source (callEntryStateHOLFinite middle HolFiniteMapExact.empty))
    (panStateRel : panToCrepStateRelFiniteExact pan crep)
    (panCodeRel : codeRelExactHOLW caller pan.code crep.code)
    (panExcpRel : panToCrepExcpRelFiniteExact caller.eids pan.eshapes)
    (panLocalsRel : panToCrepLocalsRelFiniteExact caller pan.locals crep.locals)
    (initLocalised : localisedProgHOL (nestedSeqHOL initializers) = true)
    (initShape : BranchProgram caller (nestedSeqHOL initializers))
    (loopCtxt : CrepToLoopContextExact) (target : LoopSemStateFiniteExact 64 σ)
    (crepRel : crepToLoopStateRelExact crep target)
    (memRel : crepToLoopMemRelHOLExact crep.memory target.memory crep.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact crep.globals target.globals)
    (codeRel : crepToLoopCodeRelExact loopCtxt crep.code target.code)
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
      conditionRanged assignmentRanged nameRanged fuel production source rel ranged clock finalLocals loopCost returned loopExec
  refine ⟨sourceResult,sourceFinal,sourceExec,sourceRun,?_⟩
  rcases wholeNativeTail_frontend_setup_or_resource native.arch native.crepPrograms native.programShapes
      native.wc native.ac entry (assignLoopEntryWordContext entry) (firstLoopName,2) firstLoopName native.member
      target native.loopCode native.stack native.coracle native.codeEq native.bitmapsPrefix native.ok limit native.data native.backend with
    success | resource
  · obtain ⟨word,setup,contextEq,machineEq,mcEq,labEq,tickEq,wordRel,base,frameSize,wordLocals⟩ := success
    obtain ⟨_,sourceFinal',_,_,_,_,_,sourceRun',_,_,_,_,_,_,_,_,_,extra,loopPost,_,_,_,_,_,_,_,_,_,_,_,nativeReady⟩ :=
      counted_assignLoop_globalEntry_riscv declarations start initializers globals caller condition assignment name context primitive handler
        functions conditionRanged assignmentRanged nameRanged fuel production source pan middle crep rel ranged clock finalLocals loopCost budget
        returned budgetBound loopExec conditionShape bodyShape panCode initRun sourceFound entryClock globalRel panStateRel panCodeRel
        panExcpRel panLocalsRel initLocalised initShape loopCtxt .ln target word crepRel memRel globalsRel codeRel localsRel wordRel
    have finalEq : sourceFinal = sourceFinal' := (Prod.mk.inj (sourceRun.symm.trans sourceRun')).2
    subst sourceFinal'
    obtain ⟨outcome,ticks,finalMachine,finalFfi,bound,run,correspondence⟩ :=
      nativeReady.run_shifted extra setup base frameSize native.loopEmpty (by simpa [assignLoopEntryWordContext] using contextEq) wordLocals
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

end SteppedFlapjack.PanToCrepSteps
