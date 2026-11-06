import SteppedFlapjack.PanToCrepSteps.DeclWhileSourceRiscV
import SteppedFlapjack.PanToCrepSteps.SingleEntryGlobals

namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.LabToTargetSteps

/-- A singleton unprefixed assignment loop inherits the source-bounded machine theorem. -/
theorem declWhile_singleEntry_source_fullInit_riscv {σ : Type}
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
      (declWhileSourceLoopLimit declarations initializers globals caller name (.const initial) condition (.assign .local name assignment) (.return (.const returned)) budget pan loopCtxt .ln) target) :
    let entry := assignLoopEntryProgram declarations initializers caller loopCtxt .ln
    ∃ outcome ticks finalMachine finalFfi,
      ticks ≤ max (native.backend.successTickLimit native.wc native.ac
          (loopToWordCompileHOL (compileProgHOLExact native.arch native.crepPrograms))
          entry (assignLoopEntryWordContext entry) (firstLoopName,2)
          (declWhileSourceLoopLimit declarations initializers globals caller name (.const initial) condition (.assign .local name assignment) (.return (.const returned)) budget pan loopCtxt .ln)) native.backend.resourceTickLimit ∧
      evaluateTargetHOL native.backend.mc native.backend.lab.ffi ticks native.backend.machine =
          (.halt outcome,finalMachine,finalFfi) ∧
      ((outcome = .success ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents) ∨
          (outcome = .resourceLimitHit ∧
            (finalFfi.ioEvents <+: sourceFinal.ffi.ioEvents ∨ finalFfi.ioEvents = native.stack.ffi.ioEvents))) := by
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
  exact declWhile_noGlobals_source_fullInit_riscv declarations start initializers globals caller
    name (.const initial) condition (.assign .local name assignment) returned source sourceFinal pan middle crep budget
    run sourceBound (.const _) conditionShape bodyShape sourceFound globalFound funs [] globalCompiled unique localised preShapes noTail
    loopCtxt target arch initializersEmpty globalsEmpty sourceLocals sourceGlobals sourceExceptions sourceStructs topOutside aligned
    callerExceptions codeCompiled panDef middleDef crepDef targetDef memoryRel native

end SteppedFlapjack.PanToCrepSteps
