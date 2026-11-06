import SteppedFlapjack.PanToCrepSteps.CountedDeclaredFullInit
import SteppedFlapjack.PanToCrepSteps.SourceInitialFrontend

/-! Source-first full-initialization bound for a declared assignment loop without globals. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.LabToTargetSteps

/-- Derive the no-global frontend relations from the original source state,
then apply the counted source-to-native bound. -/
theorem counted_declared_noGlobals_source_fullInit_riscv {σ : Type}
    (declarations : List (DeclHOL 64)) (start : MlString) (initializers : List (ProgHOL 64))
    (globals : PanGlobalsContextExact 64) (caller : PanToCrepContextExact 64)
    (condition assignment : Exp (RiscV.Word 64)) (name : VarName) (initial : BitVec 64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64)))
    (conditionRanged : ExpByteRanged condition) (assignmentRanged : ExpByteRanged assignment)
    (nameRanged : NameRanged name) (fuel : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source pan middle : PanSemStateFiniteExact 64 σ) (crep : CrepSemHOLState 64 σ)
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (cost budget : Nat) (returned : BitVec 64)
    (clock : cost ≤ source.clock*(panValueExpStepCost condition+panValueExpStepCost assignment+2) +
      (panValueExpStepCost condition+1) + 7)
    (budgetBound : cost ≤ budget)
    (returnLocals returnGlobals : VarName → Option (PanValue (RiscV.Word 64)))
    (returnMemory : BitVec 64 → Option (PanValue (BitVec 64))) (returnFfi : FfiState σ)
    (returnValues : List (PanValue (RiscV.Word 64)))
    (wholeRun : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+4)
      production.locals production.globals production.memory production.ffi
      (.dec name .one (.const initial) (.seq .skip (.seq
        (.while condition (.assign .local name assignment)) (.return (.const returned)))))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.returned returnLocals returnGlobals returnMemory returnFfi returnValues,cost))
    (conditionShape : ScalarExpression (scalarDeclContext (ctxtFcExactHOL caller.funcs caller.eids [] [] []) (ofString name)) (expToHOL condition))
    (bodyShape : BranchProgram (scalarDeclContext (ctxtFcExactHOL caller.funcs caller.eids [] [] []) (ofString name))
      (.assign .local (ofString name) (expToHOL assignment)))
    (sourceFound : source.code.lookup (newMainNameHOL declarations) = some ([],
      .dec (ofString name) .one (.const initial) (.seq .skip (.seq
        (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned)))),.one))
    (globalFound : (functionsHOL declarations).lookup start = some ([],
      .dec (ofString name) .one (.const initial) (.seq .skip (.seq
        (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned)))),.one))
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
      (declaredAssignLoopLimit declarations initializers globals caller condition assignment name initial returned pan budget loopCtxt .ln) target) :
    let entry := assignLoopEntryProgram declarations initializers caller loopCtxt .ln
    ∃ sourceFinal,
      source.evaluateHOLFiniteState (.dec (ofString name) .one (.const initial) (.seq .skip (.seq (.while (expToHOL condition)
        (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned))))) =
          (some (.returned (.val (.word returned))),sourceFinal) ∧
      ∃ outcome ticks finalMachine finalFfi,
        ticks ≤ max (native.backend.successTickLimit native.wc native.ac
          (loopToWordCompileHOL (compileProgHOLExact native.arch native.crepPrograms))
          entry (assignLoopEntryWordContext entry) (firstLoopName,2)
          (declaredAssignLoopLimit declarations initializers globals caller condition assignment name initial returned pan budget loopCtxt .ln)) native.backend.resourceTickLimit ∧
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
  exact counted_declared_assignLoop_whole_fullInit_riscv declarations start initializers globals caller
    condition assignment name initial context primitive handler functions conditionRanged assignmentRanged nameRanged fuel
    production source pan middle crep rel ranged cost budget returned clock budgetBound returnLocals returnGlobals
    returnMemory returnFfi returnValues wholeRun conditionShape bodyShape panCode initRun' sourceFound
    (by simpa [middleDef] using entryClock) globalFound funs exns globalCompiled globalRel' panStateRel crepCode
    unique localised preShapes noTail panExcpRel panLocalsRel initLocalised initShape loopCtxt target
    crepRel memoryRel globalsRel localsRel native

end SteppedFlapjack.PanToCrepSteps
