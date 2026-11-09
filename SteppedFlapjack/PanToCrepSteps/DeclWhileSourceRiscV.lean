import SteppedFlapjack.PanToCrepSteps.FullInitTailOutcome
import SteppedFlapjack.PanToCrepSteps.CountedDeclaredAssignLoopEntry
import SteppedFlapjack.CrepToLoopSteps.DeclRiscVInputs
import SteppedFlapjack.LoopToWordSteps.TailRiscVSetup
import SteppedFlapjack.WordToStackSteps.TailEntryFrame
import SteppedFlapjack.PanToCrepSteps.GlobalSourceEntry
import SteppedFlapjack.PanToCrepSteps.CountedAssignLoopReturn
import SteppedFlapjack.PanToCrepSteps.TailEntryCrepBound
import SteppedFlapjack.PanToCrepSteps.TailEntryRelations
import SteppedFlapjack.CrepToLoopSteps.RiscVInputs
import SteppedFlapjack.PanToCrepSteps.GlobalDecl
import SteppedFlapjack.PanToCrepSteps.CountedDeclaredAssignLoopNative
import SteppedFlapjack.PanToCrepSteps.FullInitAssignLoopInputs
import SteppedFlapjack.PanToCrepSteps.SourceInitialFrontend

/-! Source-bounded unprefixed declarations through the optimized Loop entry. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open Flapjack.LoopSemStateFiniteExact Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.LabToTargetSteps

/-- The Loop budget for a declaration, loop, and return, computed from the
source budget and compiler inputs without inspecting source state. -/
noncomputable def declWhileSourceLoopLimit
    (declarations : List (DeclHOL 64)) (initializers : List (ProgHOL 64))
    (globals : PanGlobalsContextExact 64) (caller : PanToCrepContextExact 64)
    (name : MlS) (initializer condition : ExpHOL 64) (body tail : ProgHOL 64)
    (sourceBudget : Nat)
    (loopCtxt : CrepToLoopContextExact) (live : NumSet) : Nat :=
  let callee := ctxtFcExactHOL caller.funcs caller.eids [] [] []
  let inner := scalarDeclContext callee name
  let crepInit := compileProgExactHOLW caller (nestedSeqHOL initializers)
  let globalLimit := sizeOf (nestedSeqHOL initializers) +
    (3 + sizeOf (compileProgExactHOL globals body) + sizeOf (compileProgExactHOL globals tail)) * sourceBudget + 2
  let crepLimit := sizeOf crepInit + 2 +
    (3 + sizeOf (compileProgExactHOLW inner (compileProgExactHOL globals body)) +
      sizeOf (compileProgExactHOLW inner (compileProgExactHOL globals tail))) * globalLimit
  let value := (compileExpExactHOLW callee (compileExpExactHOL globals initializer)).1.headD (.const 0)
  let test := (compileExpExactHOLW inner (compileExpExactHOL globals condition)).1.headD (.const 0)
  branchTailDeclWhileLoopLimit loopCtxt live (newMainNameHOL declarations) crepInit (callee.vmax+1) value test
    (compileProgExactHOLW inner (compileProgExactHOL globals body))
    (compileProgExactHOLW inner (compileProgExactHOL globals tail)) crepLimit

/-- A separately bounded source execution reaches the actual optimized Loop
entry with a bound depending on the source and compiler syntax. -/
theorem declWhile_source_loop_ready {σ : Type}
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
    (panCodeRel : codeRelExactHOLW caller pan.code crep.code)
    (panExcpRel : panToCrepExcpRelFiniteExact caller.eids pan.eshapes)
    (panLocalsRel : panToCrepLocalsRelFiniteExact caller pan.locals crep.locals)
    (initLocalised : localisedProgHOL (nestedSeqHOL initializers) = true)
    (initShape : BranchProgram caller (nestedSeqHOL initializers))
    (loopCtxt : CrepToLoopContextExact) (live : NumSet)
    (target : LoopSemStateFiniteExact 64 σ) (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) σ)
    (crepRel : crepToLoopStateRelExact crep target)
    (memRel : crepToLoopMemRelHOLExact crep.memory target.memory crep.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact crep.globals target.globals)
    (codeRel : crepToLoopCodeRelExact loopCtxt crep.code target.code)
    (localsRel : crepToLoopLocalsRelExact loopCtxt live crep.locals target.locals)
    (loopWordRel : loopToWordStateRelHOLExact target word) :
    let entry := optimiseHOL (compileHOLExact loopCtxt live
      (.seq (compileProgExactHOLW caller (nestedSeqHOL initializers)) (.call none (newMainNameHOL declarations) [])))
    let limit := declWhileSourceLoopLimit declarations initializers globals caller name initializer condition body
      (.return (.const returned)) budget loopCtxt live
    ∃ extra,
      FullInitReturnedReady entry {target with clock := target.clock+extra}
        {word with clock := word.clock+extra} limit sourceFinal := by
  let calleeContext := ctxtFcExactHOL caller.funcs caller.eids [] [] []
  let inner := scalarDeclContext calleeContext name
  let originalBody : ProgHOL 64 := .dec name .one initializer (.seq (.while condition body) (.return (.const returned)))
  let loweredBody := compileProgExactHOL globals originalBody
  let crepInit := compileProgExactHOLW caller (nestedSeqHOL initializers)
  obtain ⟨panPost,_,panRun,postRel,globalBound⟩ := globalEntry_originalDeclWhile_with_steps
    declarations start initializers globals inner name initializer condition body (.return (.const returned))
    bodyShape (.return (.const _)) pan middle source sourceFinal _ .one panCode initRun sourceFound entryClock run (by simp) globalRel
  have found := globalEntry_lowered_callee_lookup declarations start (nestedSeqHOL initializers) globals pan middle source
    originalBody .one panCode initRun sourceFound globalRel
  have lookup := global_lowered_lookup_after_init declarations start (newMainNameHOL declarations) pan middle
    (nestedSeqHOL initializers) loweredBody .one panCode initRun found
  obtain ⟨crepMiddle,crepPost,crepResult,crepInitRun,crepFound,crepClock,calleeLocalised,calleeStateRel,calleeCodeRel,
    calleeExcpRel,calleeLocalsRel,crepRun,complete,finalRel,resultRel⟩ :=
    tailEntry_compiled_execution pan middle panPost crep caller (nestedSeqHOL initializers) loweredBody
      (newMainNameHOL declarations) HolFiniteMapExact.empty .one (some (.returned (.val (.word returned)))) (.return _)
      initRun lookup entryClock panRun panStateRel panCodeRel panExcpRel panLocalsRel initLocalised
  have crepBound := tailEntry_declWhile_crep_bound (nestedSeqHOL initializers) (newMainNameHOL declarations) calleeContext
    name (compileExpExactHOL globals initializer) (compileExpExactHOL globals condition)
    (compileProgExactHOL globals body) (compileProgExactHOL globals (.return (.const returned)))
    (globalCompile_scalar_shape globals initializerShape) (globalCompile_scalar_shape globals conditionShape)
    (globalCompile_branch_shape globals bodyShape) (globalCompile_branch_shape globals (.return (.const _)))
    pan middle panPost (some (.returned (.val (.word returned)))) HolFiniteMapExact.empty .one crep crepMiddle crepInit
    (branch_compile initShape) initRun (by simpa [loweredBody,originalBody,compileProgExactHOL] using lookup) entryClock
    (by simpa [loweredBody,originalBody,compileProgExactHOL] using panRun) (by simp) crepInitRun
    (by simpa [loweredBody,originalBody,compileProgExactHOL] using crepFound) crepClock calleeStateRel calleeCodeRel
    calleeExcpRel calleeLocalsRel (by simpa [loweredBody,originalBody,compileProgExactHOL] using calleeLocalised)
  obtain ⟨value,test,valueEq,valueShape,testEq,testShape,bodyCrepShape,tailCrepShape,compiledEq⟩ :=
    scalarDeclWhile_compiled_shapes calleeContext name (compileExpExactHOL globals initializer)
      (compileExpExactHOL globals condition) (compileProgExactHOL globals body) (compileProgExactHOL globals (.return (.const returned)))
      (globalCompile_scalar_shape globals initializerShape) (globalCompile_scalar_shape globals conditionShape)
      (globalCompile_branch_shape globals bodyShape) (globalCompile_branch_shape globals (.return (.const _)))
  have crepLimitBound : CrepSteps.steps (.seq crepInit (.call none (newMainNameHOL declarations) [])) crep ≤
      sizeOf crepInit + 2 + (3 + sizeOf (compileProgExactHOLW inner (compileProgExactHOL globals body)) +
        sizeOf (compileProgExactHOLW inner (compileProgExactHOL globals (.return (.const returned))))) *
        (sizeOf (nestedSeqHOL initializers) + (3 + sizeOf (compileProgExactHOL globals body) +
          sizeOf (compileProgExactHOL globals (.return (.const returned)))) * budget + 2) := by
    have initBound := branch_control_static initShape pan
    have scaled := Nat.mul_le_mul_left (3 + sizeOf (compileProgExactHOLW inner (compileProgExactHOL globals body)) +
      sizeOf (compileProgExactHOLW inner (compileProgExactHOL globals (.return (.const returned))))) globalBound
    have scaledSource := Nat.mul_le_mul_left (3 + sizeOf (compileProgExactHOL globals body) +
      sizeOf (compileProgExactHOL globals (.return (.const returned)))) sourceBound
    have scaledBudget := Nat.mul_le_mul_left (3 + sizeOf (compileProgExactHOLW inner (compileProgExactHOL globals body)) +
      sizeOf (compileProgExactHOLW inner (compileProgExactHOL globals (.return (.const returned))))) (by dsimp only [originalBody]; omega :
      controlSteps (nestedSeqHOL initializers) pan + (3 + sizeOf (compileProgExactHOL globals body) +
        sizeOf (compileProgExactHOL globals (.return (.const returned)))) *
        controlSteps originalBody source + 2 ≤
      sizeOf (nestedSeqHOL initializers) + (3 + sizeOf (compileProgExactHOL globals body) +
        sizeOf (compileProgExactHOL globals (.return (.const returned)))) * budget + 2)
    dsimp only [inner,originalBody] at scaled scaledBudget ⊢
    omega
  have found' := crepFound
  have run' := crepRun
  simp only [loweredBody,originalBody,compileProgExactHOL] at found' run' compiledEq
  rw [compiledEq] at found' run'
  obtain ⟨extra,loopPost,entryShape,calleeShape,calleeLookup,loopRun,notError,loopComplete,shiftedRel,postLoopRel,loopBound⟩ :=
    branchTailDeclWhile_riscv_inputs loopCtxt live (newMainNameHOL declarations) crepInit (branch_compile initShape)
      (calleeContext.vmax+1) value valueShape test (compileProgExactHOLW inner (compileProgExactHOL globals body))
      (compileProgExactHOLW inner (compileProgExactHOL globals (.return (.const returned))))
      testShape bodyCrepShape tailCrepShape crep crepMiddle crepPost crepResult target word _
      crepInitRun (by simpa only [compileProgExactHOL] using found') crepClock
      (by simpa only [compileProgExactHOL] using run') complete crepRel memRel globalsRel codeRel localsRel loopWordRel crepLimitBound
  have ready := fullInitTailReady_of_loop _ loopPost _ _ _ entryShape calleeShape calleeLookup
    loopRun notError shiftedRel loopComplete loopBound
  have selectedValue : value = (compileExpExactHOLW calleeContext (compileExpExactHOL globals initializer)).1.headD (.const 0) := by rw [valueEq]; rfl
  have selectedTest : test = (compileExpExactHOLW inner (compileExpExactHOL globals condition)).1.headD (.const 0) := by rw [testEq]; rfl
  subst value
  subst test
  refine ⟨extra,?_⟩
  apply fullInitReturnedReady_of_return globals calleeContext sourceFinal panPost crepPost _ loopPost crepResult returned
    postRel finalRel resultRel postLoopRel _ _ _
  simpa [declWhileSourceLoopLimit,calleeContext,inner,crepInit] using ready

/-- A separately bounded source execution yields a RISC-V halt bound for the
actual global-compiler output, including entry-frame resource exhaustion. -/
theorem declWhile_source_fullInit_riscv {σ : Type}
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
        (.return (.const returned)) budget loopCtxt .ln) target) :
    let entry := assignLoopEntryProgram declarations initializers caller loopCtxt .ln
    let limit := declWhileSourceLoopLimit declarations initializers globals caller name initializer condition body
      (.return (.const returned)) budget loopCtxt .ln
    ∃ outcome ticks finalMachine finalFfi,
      ticks ≤ max (native.backend.successTickLimit native.wc native.ac
        (loopToWordCompileHOL (compileProgHOLExact native.arch native.crepPrograms))
        entry (assignLoopEntryWordContext entry) (firstLoopName,2) limit) native.backend.resourceTickLimit ∧
      evaluateTargetHOL native.backend.mc native.backend.lab.ffi ticks native.backend.machine =
        (.halt outcome,finalMachine,finalFfi) ∧
      ((outcome = .success ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents) ∨
        (outcome = .resourceLimitHit ∧
          (finalFfi.ioEvents <+: sourceFinal.ffi.ioEvents ∨ finalFfi.ioEvents = native.stack.ffi.ioEvents))) := by
  let entry := assignLoopEntryProgram declarations initializers caller loopCtxt .ln
  let limit := declWhileSourceLoopLimit declarations initializers globals caller name initializer condition body
    (.return (.const returned)) budget loopCtxt .ln
  obtain ⟨panCodeRel,programShapes,codeRel,entryMember⟩ := native.toAssignLoopCompilerInputs.frontendFacts
    declarations start initializers globals caller loopCtxt entry limit pan crep target rfl
    (.dec name .one initializer (.seq (.while condition body) (.return (.const returned)))) .one
    globalFound funs exns globalCompiled panCode crepCode unique localised preShapes noTail initShape
  let initialLoop := {target with locals := .ln}
  have normalized := emptyLive_initial_relations loopCtxt crep target _ crepRel memRel globalsRel localsRel native.data
  apply native.machineBound declarations start caller loopCtxt entry limit target programShapes entryMember sourceFinal
  intro word wordRel
  obtain ⟨extra,ready⟩ := declWhile_source_loop_ready declarations start initializers globals caller
    name initializer condition body returned source sourceFinal pan middle crep budget run sourceBound
    initializerShape conditionShape bodyShape panCode initRun sourceFound entryClock globalRel panStateRel panCodeRel
    panExcpRel panLocalsRel initLocalised initShape loopCtxt .ln initialLoop word
    normalized.1 normalized.2.1 normalized.2.2.1 (by simpa [initialLoop] using codeRel)
    normalized.2.2.2.1 wordRel
  exact ⟨extra,by simpa [entry,limit,assignLoopEntryProgram,initialLoop] using ready⟩

/-- Construct the no-globals frontend from the original source state and
apply the source-budgeted RISC-V bound. -/
theorem declWhile_noGlobals_source_fullInit_riscv {σ : Type}
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
      (declWhileSourceLoopLimit declarations initializers globals caller name initializer condition body (.return (.const returned)) budget loopCtxt .ln) target) :
    let entry := assignLoopEntryProgram declarations initializers caller loopCtxt .ln
    ∃ outcome ticks finalMachine finalFfi,
      ticks ≤ max (native.backend.successTickLimit native.wc native.ac
          (loopToWordCompileHOL (compileProgHOLExact native.arch native.crepPrograms))
          entry (assignLoopEntryWordContext entry) (firstLoopName,2)
          (declWhileSourceLoopLimit declarations initializers globals caller name initializer condition body (.return (.const returned)) budget loopCtxt .ln)) native.backend.resourceTickLimit ∧
      evaluateTargetHOL native.backend.mc native.backend.lab.ffi ticks native.backend.machine =
          (.halt outcome,finalMachine,finalFfi) ∧
      ((outcome = .success ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents) ∨
          (outcome = .resourceLimitHit ∧
            (finalFfi.ioEvents <+: sourceFinal.ffi.ioEvents ∨ finalFfi.ioEvents = native.stack.ffi.ioEvents))) := by
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
  exact declWhile_source_fullInit_riscv declarations start initializers globals caller name initializer condition body returned
    source sourceFinal pan middle crep budget run sourceBound initializerShape conditionShape bodyShape
    panCode initRun' sourceFound (by simpa [middleDef] using entryClock) globalRel' panStateRel globalFound
    funs exns globalCompiled crepCode unique localised preShapes noTail panExcpRel panLocalsRel initLocalised initShape
    loopCtxt target crepRel memoryRel globalsRel localsRel native

end SteppedFlapjack.PanToCrepSteps
