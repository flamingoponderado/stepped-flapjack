import SteppedFlapjack.PanToCrepSteps.CountdownZeroSourceSafe
import SteppedFlapjack.PanToCrepSteps.DeclWhileSingleEntry

/-! Successful execution for the concrete single-entry countdown. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.LabToTargetSteps

/-- A bounded source run for the zero-count program has a successful
full-initialization RISC-V run. -/
theorem countdownZero_singleEntry_source_success {σ : Type}
    (declarations : List (DeclHOL 64)) (start : MlString) (initializers : List (ProgHOL 64))
    (globals : PanGlobalsContextExact 64) (caller : PanToCrepContextExact 64)
    (name : MlString) (initial returned : BitVec 64) (condition assignment : ExpHOL 64)
    (source sourceFinal pan middle : PanSemStateFiniteExact 64 σ) (crep : CrepSemHOLState 64 σ)
    (budget : Nat)
    (run : source.evaluateHOLFiniteState (.dec name .one (.const initial) (.seq (.while condition (.assign .local name assignment)) (.return (.const returned)))) =
      (some (.returned (.val (.word returned))),sourceFinal))
    (sourceBound : controlSteps (.dec name .one (.const initial) (.seq (.while condition (.assign .local name assignment)) (.return (.const returned)))) source ≤ budget)
    (conditionShape : ScalarExpression (scalarDeclContext (ctxtFcExactHOL caller.funcs caller.eids [] [] []) name) condition)
    (bodyShape : BranchProgram (scalarDeclContext (ctxtFcExactHOL caller.funcs caller.eids [] [] []) name) (.assign .local name assignment))
    (loopCtxt : CrepToLoopContextExact) (target : LoopSemStateFiniteExact 64 σ)
    (arch : AsmArchitecture)
    (initializersEmpty : initializers = []) (globalsEmpty : globals = emptyGlobalsContext)
    (sourceLocals : source.locals = HolFiniteMapExact.empty)
    (sourceGlobals : source.globals = HolFiniteMapExact.empty)
    (sourceExceptions : source.eshapes = HolFiniteMapExact.empty)
    (sourceStructs : source.structs = [])
    (topOutside : ¬ source.memaddrs source.topAddr)
    (aligned : panGlobalsByteAlignedHOL source.topAddr)
    (singleDef : declarations = singleEntryProgram start (.dec name .one (.const initial)
      (.seq (.while condition (.assign .local name assignment)) (.return (.const returned)))))
    (sourceCode : source.code = HolFiniteMapExact.empty.update (newMainNameHOL declarations,
      ([],.dec name .one (.const initial) (.seq (.while condition (.assign .local name assignment))
        (.return (.const returned))),.one)))
    (panDef : pan = noGlobalsLoweredPreCall source (HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse))
    (middleDef : middle = pan)
    (crepDef : crep = concreteDeclCrepState pan (compileProgDeclsHOLW (compileTopExactHOL declarations start)))
    (targetDef : target = {concreteDeclLoopState arch crep (compileProgDeclsHOLW (compileTopExactHOL declarations start)) with memory := target.memory})
    (memoryRel : crepToLoopMemRelHOLExact crep.memory target.memory crep.memaddrs)
    (native : FullInitAssignLoopInputs declarations start caller loopCtxt (assignLoopEntryProgram declarations initializers caller loopCtxt .ln)
      (declWhileSourceLoopLimit declarations initializers globals caller name (.const initial) condition (.assign .local name assignment) (.return (.const returned)) budget pan loopCtxt .ln) target)
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
        (declWhileSourceLoopLimit declarations initializers globals caller name (.const initial) condition
          (.assign .local name assignment) (.return (.const returned)) budget pan loopCtxt .ln) ∧
      evaluateTargetHOL native.backend.mc native.backend.lab.ffi ticks native.backend.machine =
        (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents := by
  let body : ProgHOL 64 := (.dec name .one (.const initial) (.seq
        (.while condition (.assign .local name assignment)) (.return (.const returned))))
  have assignmentShape : ScalarExpression
      (scalarDeclContext (ctxtFcExactHOL caller.funcs caller.eids [] [] []) name) assignment := by
    cases bodyShape with
    | assign _ _ _ shape => exact shape
  have localised : ∀ entry ∈ functionsHOL (compileTopExactHOL declarations start),
      localisedProgHOL entry.2.2.1 = true := by
    rw [singleDef]
    exact singleEntry_declaredWhile_localised start name initial returned condition
      assignment _ conditionShape assignmentShape
  have unique : ((compileProgDeclsHOLW (compileTopExactHOL declarations start)).map Prod.fst).Nodup := by
    rw [singleDef]
    exact singleEntry_compiled_names_unique start body
  have noTail : ∀ n ps init callee, (n,ps,.seq init (.call none callee [])) ∈
      compileToCrepExactHOLW (compileTopExactHOL declarations start) →
      callee ∉ (functionsHOL ((compileTopExactHOL declarations start).filter inlinableHOL)).map Prod.fst := by
    rw [singleDef,singleEntry_inline_selection_empty]
    simp
  have preShapes : ∀ n ps p, (n,ps,p) ∈ compileToCrepExactHOLW (compileTopExactHOL declarations start) →
      SupportedCodeBody p := by
    intro n ps p member
    rw [singleDef,singleEntry_compileTop] at member
    simp only [compileToCrepExactHOLW,functionsHOL,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false,
      Prod.mk.injEq] at member
    rcases member with first | second
    · rcases first with ⟨_,_,rfl⟩
      simp only [compFuncExactHOLW,List.map_nil,sizeOfShapeHOL,sizeOfShapesHOL,Nat.zero_sub,
        compileProgExactHOLW,compileCallNoReturnExactHOLW,compileExpExactHOLWList,List.flatMap_nil]
      exact .tail (.expr (.leaf .skip)) _
    · rcases second with ⟨_,_,rfl⟩
      simp only [compFuncExactHOLW,List.map_nil,sizeOfShapeHOL,sizeOfShapesHOL,Nat.zero_sub,
        declaredWhileAssignLoop_fperm,compileProgExactHOL,compileExpExactHOL]
      apply scalarDeclWhile_supported
      · exact .const _
      · apply BranchCondition.scalar
        have shape := globalCompile_scalar_shape emptyGlobalsContext conditionShape
        simpa [native.callerEq,singleDef,singleEntry_compileTop,functionsHOL,declaredWhileAssignLoop_fperm,compileProgExactHOL,compileExpExactHOL,ctxtFcExactHOL,mkCtxtExactHOL,panToCrepMakeVmapHOLExact,maxList] using shape
      · have shape := globalCompile_branch_shape emptyGlobalsContext bodyShape
        simpa [native.callerEq,singleDef,singleEntry_compileTop,functionsHOL,declaredWhileAssignLoop_fperm,compileProgExactHOL,compileExpExactHOL,ctxtFcExactHOL,mkCtxtExactHOL,panToCrepMakeVmapHOLExact,maxList] using shape
      · exact .return (.const _)
  have sourceFound : source.code.lookup (newMainNameHOL declarations) = some ([],body,.one) := by
    simp [sourceCode,HolFiniteMapExact.lookup_update,FUPDATE,body]
  have globalFound : (functionsHOL declarations).lookup start = some ([],body,.one) := by
    simp [singleDef,singleEntryProgram,functionsHOL,body]
  have codeCompiled : ∀ function parameters program returnShape,
      source.code.lookup function = some (parameters,program,returnShape) →
      (HolFiniteMapExact.empty.updateList (functionsHOL (compileTopExactHOL declarations start)).reverse).lookup function =
        some (parameters,compileProgExactHOL emptyGlobalsContext program,returnShape) := by
    rw [singleDef]
    apply singleEntry_compiled_code_lookup
    simpa [singleDef,body,declaredWhileAssignLoop_fperm] using sourceCode
  have callerExceptions : caller.eids = HolFiniteMapExact.empty := by
    rw [native.callerEq]
    simp only [mkCtxtExactHOL]
    rw [singleDef]
    exact singleEntry_compiled_eids_empty start body
  let funs : List (DeclHOL 64) := [.function ⟨newMainNameHOL declarations,false,false,[],
    compileProgExactHOL emptyGlobalsContext (fpermHOL start (newMainNameHOL declarations) body),.one⟩]
  have globalCompiled : globalLoweredDecs declarations start = (initializers,funs,[],globals) := by
    simpa only [singleDef,initializersEmpty,globalsEmpty,funs] using singleEntry_globalLowered start body
  exact countdownZero_noGlobals_source_success declarations start initializers globals caller
    name (.const initial) condition (.assign .local name assignment) returned source sourceFinal pan middle crep budget
    run sourceBound (.const _) conditionShape bodyShape sourceFound globalFound funs [] globalCompiled unique localised preShapes noTail
    loopCtxt target arch initializersEmpty globalsEmpty sourceLocals sourceGlobals sourceExceptions sourceStructs topOutside aligned
    callerExceptions codeCompiled panDef middleDef crepDef targetDef memoryRel native acEq declarationsEq startEq archEq wcEq


/-- Transfer the bound to the original full compiler program. -/
theorem countdownZero_singleEntry_fullCompiler_success {σ : Type}
    (declarations : List (DeclHOL 64)) (start : MlString) (initializers : List (ProgHOL 64))
    (globals : PanGlobalsContextExact 64) (caller : PanToCrepContextExact 64)
    (name : MlString) (initial returned : BitVec 64) (condition assignment : ExpHOL 64)
    (source sourceFinal pan middle : PanSemStateFiniteExact 64 σ) (crep : CrepSemHOLState 64 σ)
    (budget : Nat)
    (run : source.evaluateHOLFiniteState (.dec name .one (.const initial) (.seq .skip (.seq (.while condition (.assign .local name assignment)) (.return (.const returned))))) =
      (some (.returned (.val (.word returned))),sourceFinal))
    (sourceBound : controlSteps (.dec name .one (.const initial) (.seq .skip (.seq (.while condition (.assign .local name assignment)) (.return (.const returned))))) source ≤ budget)
    (conditionShape : ScalarExpression (scalarDeclContext (ctxtFcExactHOL caller.funcs caller.eids [] [] []) name) condition)
    (bodyShape : BranchProgram (scalarDeclContext (ctxtFcExactHOL caller.funcs caller.eids [] [] []) name) (.assign .local name assignment))
    (loopCtxt : CrepToLoopContextExact) (target : LoopSemStateFiniteExact 64 σ)
    (arch : AsmArchitecture)
    (initializersEmpty : initializers = []) (globalsEmpty : globals = emptyGlobalsContext)
    (sourceLocals : source.locals = HolFiniteMapExact.empty)
    (sourceGlobals : source.globals = HolFiniteMapExact.empty)
    (sourceExceptions : source.eshapes = HolFiniteMapExact.empty)
    (sourceStructs : source.structs = [])
    (topOutside : ¬ source.memaddrs source.topAddr)
    (aligned : panGlobalsByteAlignedHOL source.topAddr)
    (startDef : start = ofString "main")
    (singleDef : declarations = singleEntryProgram start (.dec name .one (.const initial)
      (.seq (.while condition (.assign .local name assignment)) (.return (.const returned)))))
    (sourceCode : source.code = HolFiniteMapExact.empty.update (newMainNameHOL declarations,
      ([],.dec name .one (.const initial) (.seq (.while condition (.assign .local name assignment))
        (.return (.const returned))),.one)))
    (panDef : pan = noGlobalsLoweredPreCall source (HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse))
    (middleDef : middle = pan)
    (crepDef : crep = concreteDeclCrepState pan (compileProgDeclsHOLW (compileTopExactHOL declarations start)))
    (targetDef : target = {concreteDeclLoopState arch crep (compileProgDeclsHOLW (compileTopExactHOL declarations start)) with memory := target.memory})
    (memoryRel : crepToLoopMemRelHOLExact crep.memory target.memory crep.memaddrs)
    (native : FullInitAssignLoopInputs declarations start caller loopCtxt (assignLoopEntryProgram declarations initializers caller loopCtxt .ln)
      (declWhileSourceLoopLimit declarations initializers globals caller name (.const initial) condition (.assign .local name assignment) (.return (.const returned)) budget pan loopCtxt .ln) target)
    (acEq : native.ac = riscvConfig)
    (declarationsEq : declarations = singleEntryProgram (ofString "main")
      (.dec (ofString "x") .one (.const (0 : BitVec 64))
        (.seq (.while (.var .local (ofString "x"))
          (.assign .local (ofString "x") (.op .sub [.var .local (ofString "x"),.const 1])))
          (.return (.const (0 : BitVec 64))))))
    (archEq : native.arch = riscvConfig.isa) (wcEq : native.wc = countdownRiscVBackend.wordToWordConf) :
    let entry := assignLoopEntryProgram declarations initializers caller loopCtxt .ln
    ∃ ticks finalMachine finalFfi,
      ticks ≤ native.backend.successTickLimit native.wc riscvConfig
        (panToWordCompileProgHOL native.arch (singleEntryProgram (ofString "main")
          (.dec name .one (.const initial) (.seq .skip
            (.seq (.while condition (.assign .local name assignment)) (.return (.const returned)))))))
        entry (assignLoopEntryWordContext entry) (firstLoopName,2)
        (declWhileSourceLoopLimit declarations initializers globals caller name (.const initial) condition
          (.assign .local name assignment) (.return (.const returned)) budget pan loopCtxt .ln) ∧
      evaluateTargetHOL native.backend.mc native.backend.lab.ffi ticks native.backend.machine =
        (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents := by
  have skipFacts := scalarDecl_skip_execution_steps name initial
    (.seq (.while condition (.assign .local name assignment)) (.return (.const returned))) source
  have simplifiedRun : source.evaluateHOLFiniteState (.dec name .one (.const initial)
      (.seq (.while condition (.assign .local name assignment)) (.return (.const returned)))) =
      (some (.returned (.val (.word returned))),sourceFinal) := by
    rw [← skipFacts.1]
    exact run
  have simplifiedBound : controlSteps (.dec name .one (.const initial)
      (.seq (.while condition (.assign .local name assignment)) (.return (.const returned)))) source ≤ budget := by
    rw [skipFacts.2] at sourceBound
    omega
  obtain ⟨ticks,finalMachine,finalFfi,ticksBound,machineRun,events⟩ :=
    countdownZero_singleEntry_source_success declarations start initializers globals caller name initial returned condition assignment
      source sourceFinal pan middle crep budget simplifiedRun simplifiedBound conditionShape bodyShape loopCtxt target arch
      initializersEmpty globalsEmpty sourceLocals sourceGlobals sourceExceptions sourceStructs topOutside aligned singleDef sourceCode
      panDef middleDef crepDef targetDef memoryRel native acEq declarationsEq startDef archEq wcEq
  have assignmentShape : ScalarExpression
      (scalarDeclContext (ctxtFcExactHOL caller.funcs caller.eids [] [] []) name) assignment := by
    cases bodyShape with
    | assign _ _ _ shape => exact shape
  have compilerEq := singleEntry_declaredWhile_panToWord native.arch name initial returned condition assignment _
    conditionShape assignmentShape
  have programEq : loopToWordCompileHOL (compileProgHOLExact native.arch native.crepPrograms) =
      panToWordCompileProgHOL native.arch (singleEntryProgram (ofString "main")
        (.dec name .one (.const initial) (.seq .skip
          (.seq (.while condition (.assign .local name assignment)) (.return (.const returned)))))) := by
    rw [native.programsEq]
    simpa only [singleDef,startDef] using compilerEq.symm
  exact ⟨ticks,finalMachine,finalFfi,by simpa only [programEq] using ticksBound,machineRun,events⟩

end SteppedFlapjack.PanToCrepSteps
