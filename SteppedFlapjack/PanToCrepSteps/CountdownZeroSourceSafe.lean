import SteppedFlapjack.PanToCrepSteps.DeclWhileSourceRiscV
import SteppedFlapjack.PanToCrepSteps.CountdownZeroMachineSafe

/-! Source-bounded zero-count execution with a successful machine outcome. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open Flapjack.LoopSemStateFiniteExact Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.LabToTargetSteps

/-- A source-bounded return for the concrete zero-count compilation reaches
successful machine termination within the fitting-frame bound. -/
theorem countdownZero_source_fullInit_success {σ : Type}
    (declarations : List (DeclHOL 64)) (start : MlString) (initializers : List (ProgHOL 64))
    (globals : PanGlobalsContextExact 64) (caller : PanToCrepContextExact 64)
    (name : MlS) (initializer condition : ExpHOL 64) (body : ProgHOL 64) (returned : BitVec 64)
    (source sourceFinal pan middle : PanSemStateFiniteExact 64 σ) (crep : CrepSemHOLState 64 σ)
    (budget : Nat)
    (run : source.evaluateHOLFiniteState (.dec name .one initializer (.seq (.while condition body) (.return (.const returned)))) =
      (some (.returned (.val (.word returned))),sourceFinal))
    (sourceBound : controlSteps (.dec name .one initializer (.seq (.while condition body) (.return (.const returned)))) source ≤ budget)
    (initializerShape : ScalarExpression (ctxtFcExactHOL caller.funcs caller.eids [] [] []) initializer)
    (conditionShape : ScalarExpression (scalarDeclContext (ctxtFcExactHOL caller.funcs caller.eids [] [] []) name) condition)
    (bodyShape : BranchProgram (scalarDeclContext (ctxtFcExactHOL caller.funcs caller.eids [] [] []) name) body)
    (panCode : pan.code = HolFiniteMapExact.empty.updateList (functionsHOL (compileTopExactHOL declarations start)).reverse)
    (initRun : pan.evaluateHOLFiniteState (nestedSeqHOL initializers) = (none,middle))
    (sourceFound : source.code.lookup (newMainNameHOL declarations) = some ([],
      .dec name .one initializer (.seq (.while condition body) (.return (.const returned))),.one))
    (entryClock : middle.clock ≠ 0)
    (globalRel : panGlobalsStateRelHOLExact true globals source (callEntryStateHOLFinite middle HolFiniteMapExact.empty))
    (panStateRel : panToCrepStateRelFiniteExact pan crep)
    (globalFound : (functionsHOL declarations).lookup start = some ([],
      .dec name .one initializer (.seq (.while condition body) (.return (.const returned))),.one))
    (funs exns : List (DeclHOL 64))
    (globalCompiled : globalLoweredDecs declarations start = (initializers,funs,exns,globals))
    (crepCode : crep.code = alistToFmapCodeExact (compileProgDeclsHOLW (compileTopExactHOL declarations start)))
    (unique : ((compileProgDeclsHOLW (compileTopExactHOL declarations start)).map Prod.fst).Nodup)
    (localised : ∀ e ∈ functionsHOL (compileTopExactHOL declarations start), localisedProgHOL e.2.2.1 = true)
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
    (native : FullInitAssignLoopInputs declarations start caller loopCtxt
      (assignLoopEntryProgram declarations initializers caller loopCtxt .ln)
      (declWhileSourceLoopLimit declarations initializers globals caller name initializer condition body
        (.return (.const returned)) budget pan loopCtxt .ln) target)
    (acEq : native.ac = riscvConfig)
    (declarationsEq : declarations = singleEntryProgram (ofString "main")
      (.dec (ofString "x") .one (.const (0 : BitVec 64))
        (.seq (.while (.var .local (ofString "x"))
          (.assign .local (ofString "x") (.op .sub [.var .local (ofString "x"),.const 1])))
          (.return (.const (0 : BitVec 64))))))
    (startEq : start = ofString "main") (archEq : native.arch = riscvConfig.isa)
    (wcEq : native.wc = countdownRiscVBackend.wordToWordConf) :
    let entry := assignLoopEntryProgram declarations initializers caller loopCtxt .ln
    let limit := declWhileSourceLoopLimit declarations initializers globals caller name initializer condition body
      (.return (.const returned)) budget pan loopCtxt .ln
    ∃ ticks finalMachine finalFfi,
      ticks ≤ native.backend.successTickLimit native.wc riscvConfig
        (loopToWordCompileHOL (compileProgHOLExact native.arch native.crepPrograms))
        entry (assignLoopEntryWordContext entry) (firstLoopName,2) limit ∧
      evaluateTargetHOL native.backend.mc native.backend.lab.ffi ticks native.backend.machine =
        (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents := by
  let entry := assignLoopEntryProgram declarations initializers caller loopCtxt .ln
  let limit := declWhileSourceLoopLimit declarations initializers globals caller name initializer condition body
    (.return (.const returned)) budget pan loopCtxt .ln
  obtain ⟨panCodeRel,programShapes,codeRel,entryMember⟩ := native.toAssignLoopCompilerInputs.frontendFacts
    declarations start initializers globals caller loopCtxt entry limit pan crep target rfl
    (.dec name .one initializer (.seq (.while condition body) (.return (.const returned)))) .one
    globalFound funs exns globalCompiled panCode crepCode unique localised preShapes noTail initShape
  let initialLoop := {target with locals := .ln}
  have normalized := emptyLive_initial_relations loopCtxt crep target _ crepRel memRel globalsRel localsRel native.data
  apply native.countdownZero_machineBound_safe declarations start caller loopCtxt entry limit target
    programShapes entryMember sourceFinal ?_ acEq declarationsEq startEq archEq wcEq
  intro word wordRel
  obtain ⟨extra,ready⟩ := declWhile_source_loop_ready declarations start initializers globals caller
    name initializer condition body returned source sourceFinal pan middle crep budget run sourceBound
    initializerShape conditionShape bodyShape panCode initRun sourceFound entryClock globalRel panStateRel panCodeRel
    panExcpRel panLocalsRel initLocalised initShape loopCtxt .ln initialLoop word
    normalized.1 normalized.2.1 normalized.2.2.1 (by simpa [initialLoop] using codeRel)
    normalized.2.2.2.1 wordRel
  exact ⟨extra,by simpa [entry,limit,assignLoopEntryProgram,initialLoop] using ready⟩


/-- Build the empty-globals frontend and retain the successful machine result. -/
theorem countdownZero_noGlobals_source_success {σ : Type}
    (declarations : List (DeclHOL 64)) (start : MlString) (initializers : List (ProgHOL 64))
    (globals : PanGlobalsContextExact 64) (caller : PanToCrepContextExact 64)
    (name : MlS) (initializer condition : ExpHOL 64) (body : ProgHOL 64) (returned : BitVec 64)
    (source sourceFinal pan middle : PanSemStateFiniteExact 64 σ) (crep : CrepSemHOLState 64 σ)
    (budget : Nat)
    (run : source.evaluateHOLFiniteState (.dec name .one initializer (.seq (.while condition body) (.return (.const returned)))) =
      (some (.returned (.val (.word returned))),sourceFinal))
    (sourceBound : controlSteps (.dec name .one initializer (.seq (.while condition body) (.return (.const returned)))) source ≤ budget)
    (initializerShape : ScalarExpression (ctxtFcExactHOL caller.funcs caller.eids [] [] []) initializer)
    (conditionShape : ScalarExpression (scalarDeclContext (ctxtFcExactHOL caller.funcs caller.eids [] [] []) name) condition)
    (bodyShape : BranchProgram (scalarDeclContext (ctxtFcExactHOL caller.funcs caller.eids [] [] []) name) body)
    (sourceFound : source.code.lookup (newMainNameHOL declarations) = some ([],
      .dec name .one initializer (.seq (.while condition body) (.return (.const returned))),.one))
    (globalFound : (functionsHOL declarations).lookup start = some ([],
      .dec name .one initializer (.seq (.while condition body) (.return (.const returned))),.one))
    (funs exns : List (DeclHOL 64))
    (globalCompiled : globalLoweredDecs declarations start = (initializers,funs,exns,globals))
    (unique : ((compileProgDeclsHOLW (compileTopExactHOL declarations start)).map Prod.fst).Nodup)
    (localised : ∀ entry ∈ functionsHOL (compileTopExactHOL declarations start), localisedProgHOL entry.2.2.1 = true)
    (preShapes : ∀ n ps p, (n,ps,p) ∈ compileToCrepExactHOLW (compileTopExactHOL declarations start) → SupportedCodeBody p)
    (noTail : ∀ n ps init callee, (n,ps,.seq init (.call none callee [])) ∈
      compileToCrepExactHOLW (compileTopExactHOL declarations start) →
      callee ∉ (functionsHOL ((compileTopExactHOL declarations start).filter inlinableHOL)).map Prod.fst)
    (loopCtxt : CrepToLoopContextExact) (target : LoopSemStateFiniteExact 64 σ)
    (arch : AsmArchitecture)
    (initializersEmpty : initializers = []) (globalsEmpty : globals = emptyGlobalsContext)
    (sourceLocals : source.locals = HolFiniteMapExact.empty)
    (sourceGlobals : source.globals = HolFiniteMapExact.empty)
    (sourceExceptions : source.eshapes = HolFiniteMapExact.empty)
    (sourceStructs : source.structs = [])
    (topOutside : ¬ source.memaddrs source.topAddr)
    (aligned : panGlobalsByteAlignedHOL source.topAddr)
    (callerExceptions : caller.eids = HolFiniteMapExact.empty)
    (codeCompiled : ∀ function parameters program returnShape,
      source.code.lookup function = some (parameters,program,returnShape) →
      (HolFiniteMapExact.empty.updateList (functionsHOL (compileTopExactHOL declarations start)).reverse).lookup function =
        some (parameters,compileProgExactHOL emptyGlobalsContext program,returnShape))
    (panDef : pan = noGlobalsLoweredPreCall source (HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse))
    (middleDef : middle = pan)
    (crepDef : crep = concreteDeclCrepState pan (compileProgDeclsHOLW (compileTopExactHOL declarations start)))
    (targetDef : target = {concreteDeclLoopState arch crep (compileProgDeclsHOLW (compileTopExactHOL declarations start)) with memory := target.memory})
    (memoryRel : crepToLoopMemRelHOLExact crep.memory target.memory crep.memaddrs)
    (native : FullInitAssignLoopInputs declarations start caller loopCtxt (assignLoopEntryProgram declarations initializers caller loopCtxt .ln)
      (declWhileSourceLoopLimit declarations initializers globals caller name initializer condition body (.return (.const returned)) budget pan loopCtxt .ln) target)
    (acEq : native.ac = riscvConfig)
    (declarationsEq : declarations = singleEntryProgram (ofString "main")
      (.dec (ofString "x") .one (.const (0 : BitVec 64))
        (.seq (.while (.var .local (ofString "x"))
          (.assign .local (ofString "x") (.op .sub [.var .local (ofString "x"),.const 1])))
          (.return (.const (0 : BitVec 64))))))
    (startEq : start = ofString "main") (archEq : native.arch = riscvConfig.isa)
    (wcEq : native.wc = countdownRiscVBackend.wordToWordConf) :
    let entry := assignLoopEntryProgram declarations initializers caller loopCtxt .ln
    ∃ ticks finalMachine finalFfi,
      ticks ≤ native.backend.successTickLimit native.wc riscvConfig
        (loopToWordCompileHOL (compileProgHOLExact native.arch native.crepPrograms))
        entry (assignLoopEntryWordContext entry) (firstLoopName,2)
        (declWhileSourceLoopLimit declarations initializers globals caller name initializer condition body
          (.return (.const returned)) budget pan loopCtxt .ln) ∧
      evaluateTargetHOL native.backend.mc native.backend.lab.ffi ticks native.backend.machine =
        (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents := by
  have callerVars : caller.vars = HolFiniteMapExact.empty := by
    apply HolFiniteMapExact.ext_lookup
    intro key
    simp [native.callerEq,mkCtxtExactHOL,panToCrepMakeVmapHOLExact,HolFiniteMapExact.lookup_updateList,FUPDATE_LIST]
  have loopVars : loopCtxt.vars = HolFiniteMapExact.empty := by
    simp [native.loopContextEq,mkCtxtExact,makeVmapExact,HolFiniteMapExact.updateListEq]
  have initLocalised : localisedProgHOL (nestedSeqHOL initializers) = true := by
    simp [initializersEmpty,localisedProgHOL]
  have initShape : BranchProgram caller (nestedSeqHOL initializers) := by
    simpa [initializersEmpty,nestedSeqHOL] using (BranchProgram.skip (context := caller))
  have frontend := noGlobals_source_frontend source
    (HolFiniteMapExact.empty.updateList (functionsHOL (compileTopExactHOL declarations start)).reverse)
    (compileProgDeclsHOLW (compileTopExactHOL declarations start)) arch caller loopCtxt
    sourceLocals sourceGlobals sourceExceptions sourceStructs topOutside aligned callerVars callerExceptions loopVars codeCompiled
  dsimp only at frontend
  rw [← panDef, ← crepDef] at frontend
  obtain ⟨initRun,entryClock,globalRel,panStateRel,crepCode,panExcpRel,panLocalsRel,
    baseRel,_,baseGlobals,baseLocals,_⟩ := frontend
  have crepRel : crepToLoopStateRelExact crep target := by
    rw [targetDef]
    simpa [crepToLoopStateRelExact] using baseRel
  have globalsRel : crepToLoopGlobalsRelHOLExact crep.globals target.globals := by
    rw [targetDef]
    simpa using baseGlobals
  have localsRel : crepToLoopLocalsRelExact loopCtxt .ln crep.locals target.locals := by
    rw [targetDef]
    simpa using baseLocals
  have panCode : pan.code = HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse := by
    simp [panDef,noGlobalsLoweredPreCall]
  have initRun' : pan.evaluateHOLFiniteState (nestedSeqHOL initializers) = (none,middle) := by
    simp [initializersEmpty,middleDef,evaluateHOLFiniteState_skip]
  have globalRel' : panGlobalsStateRelHOLExact true globals source
      (callEntryStateHOLFinite middle HolFiniteMapExact.empty) := by
    simpa [globalsEmpty,middleDef] using globalRel
  exact countdownZero_source_fullInit_success declarations start initializers globals caller name initializer condition body returned
    source sourceFinal pan middle crep budget run sourceBound initializerShape conditionShape bodyShape
    panCode initRun' sourceFound (by simpa [middleDef] using entryClock) globalRel' panStateRel globalFound
    funs exns globalCompiled crepCode unique localised preShapes noTail panExcpRel panLocalsRel initLocalised initShape
    loopCtxt target crepRel memoryRel globalsRel localsRel native acEq declarationsEq startEq archEq wcEq

end SteppedFlapjack.PanToCrepSteps
