import SteppedFlapjack.PanToCrepSteps.DeclWhileSingleEntry
import SteppedFlapjack.PanToCrepSteps.CountedDeclaredAssignLoopNative
import SteppedFlapjack.PanToCrepSteps.SingleEntryGlobals

/-! Single-entry instance of the full-initialization source bound. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.LabToTargetSteps

/-- The singleton declaration supplies its globals-pass code lookup and
exception table from actual compilation. -/
theorem counted_singleEntry_declared_fullCompiler_riscv {σ : Type}
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
    (singleDef : declarations = singleEntryProgram start (.dec (ofString name) .one (.const initial)
      (.seq (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned)))))
    (sourceCode : source.code = HolFiniteMapExact.empty.update (newMainNameHOL declarations,
      ([],.dec (ofString name) .one (.const initial)
        (.seq (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned))),.one)))
    (panDef : pan = noGlobalsLoweredPreCall source (HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse))
    (middleDef : middle = pan)
    (crepDef : crep = concreteDeclCrepState pan (compileProgDeclsHOLW (compileTopExactHOL declarations start)))
    (targetDef : target = {concreteDeclLoopState arch crep (compileProgDeclsHOLW (compileTopExactHOL declarations start)) with memory := target.memory})
    (memoryRel : crepToLoopMemRelHOLExact crep.memory target.memory crep.memaddrs)
    (native : FullInitAssignLoopInputs declarations start caller loopCtxt (assignLoopEntryProgram declarations initializers caller loopCtxt .ln)
      (declWhileSourceLoopLimit declarations initializers globals caller (ofString name) (.const initial) (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment)) (.return (.const returned)) budget pan loopCtxt .ln) target) :
    let entry := assignLoopEntryProgram declarations initializers caller loopCtxt .ln
    ∃ sourceFinal,
      source.evaluateHOLFiniteState (.dec (ofString name) .one (.const initial) (.seq .skip (.seq (.while (expToHOL condition)
        (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned))))) =
          (some (.returned (.val (.word returned))),sourceFinal) ∧
      ∃ outcome ticks finalMachine finalFfi,
        ticks ≤ max (native.backend.successTickLimit native.wc native.ac
          (panToWordCompileProgHOL native.arch (singleEntryProgram (ofString "main")
            (.dec (ofString name) .one (.const initial) (.seq .skip
              (.seq (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned)))))))
          entry (assignLoopEntryWordContext entry) (firstLoopName,2)
          (declWhileSourceLoopLimit declarations initializers globals caller (ofString name) (.const initial) (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment)) (.return (.const returned)) budget pan loopCtxt .ln)) native.backend.resourceTickLimit ∧
        evaluateTargetHOL native.backend.mc native.backend.lab.ffi ticks native.backend.machine =
          (.halt outcome,finalMachine,finalFfi) ∧
        ((outcome = .success ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents) ∨
          (outcome = .resourceLimitHit ∧
            (finalFfi.ioEvents <+: sourceFinal.ffi.ioEvents ∨ finalFfi.ioEvents = native.stack.ffi.ioEvents))) := by
  classical
  obtain ⟨finalLocals,loopCost,loopExec,costEq⟩ := counted_declared_assignLoop_whole_invert condition assignment name initial returned
    context primitive handler functions fuel production cost returnLocals returnGlobals returnMemory returnFfi returnValues wholeRun
  have loopClock : loopCost ≤ source.clock*(panValueExpStepCost condition+panValueExpStepCost assignment+2) +
      (panValueExpStepCost condition+1) := by omega
  obtain ⟨sourceResult,sourceFinal,sourceExec,sourceRun,sourceBound,_⟩ :=
    counted_declared_assignLoop_return condition assignment name initial returned context primitive handler functions
      conditionRanged assignmentRanged nameRanged fuel production source rel ranged finalLocals loopCost loopClock loopExec
      (ctxtFcExactHOL caller.funcs caller.eids [] [] []) conditionShape bodyShape
  have bounded : controlSteps (.dec (ofString name) .one (.const initial) (.seq .skip (.seq
      (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned))))) source ≤ budget := by
    omega
  refine ⟨sourceFinal,sourceRun,?_⟩
  exact declWhile_singleEntry_fullCompiler_riscv declarations start initializers globals caller (ofString name) initial returned
    (expToHOL condition) (expToHOL assignment) source sourceFinal pan middle crep budget sourceRun bounded conditionShape bodyShape
    loopCtxt target arch initializersEmpty globalsEmpty sourceLocals sourceGlobals sourceExceptions sourceStructs topOutside aligned
    startDef singleDef sourceCode panDef middleDef crepDef targetDef memoryRel native

end SteppedFlapjack.PanToCrepSteps
