import SteppedFlapjack.PanToCrepSteps.CountedDeclaredAssignLoopRiscV
import SteppedFlapjack.PanToCrepSteps.CountedAssignLoopNative
import SteppedFlapjack.PanToCrepSteps.CountedAssignLoopWhole

/-! Native RISC-V bound for an initialized assignment-loop source entry. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.LabToTargetSteps

/-- Any returned whole loop-and-return body exposes its normal inner loop. -/
theorem counted_assignLoop_anyReturn_invert {σ : Type}
    (condition assignment : Exp (RiscV.Word 64)) (name : VarName) (returned : BitVec 64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (cost : Nat)
    (returnLocals returnGlobals : VarName → Option (PanValue (RiscV.Word 64)))
    (returnMemory : BitVec 64 → Option (PanValue (BitVec 64))) (returnFfi : FfiState σ)
    (returnValues : List (PanValue (RiscV.Word 64)))
    (run : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+3)
      production.locals production.globals production.memory production.ffi
      (.seq .skip (.seq (.while condition (.assign .local name assignment)) (.return (.const returned))))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.returned returnLocals returnGlobals returnMemory returnFfi returnValues,cost)) :
    ∃ finalLocals loopCost,
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
        production.locals production.globals production.memory production.ffi (.while condition (.assign .local name assignment))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
          some (.normal finalLocals production.globals production.memory production.ffi,loopCost) ∧
      cost = loopCost+5 := by
  rw [evalPanValueFfiProgSteps] at run
  rw [evalPanValueFfiProgSteps] at run
  simp only [Bind.bind, Option.bind] at run
  rw [evalPanValueFfiProgSteps] at run
  cases loopRun : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
      production.locals production.globals production.memory production.ffi (.while condition (.assign .local name assignment))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) with
  | none => simp [loopRun] at run
  | some pair =>
    rcases pair with ⟨loopResult,loopCost⟩
    obtain ⟨locals,normal | error⟩ := counted_assignLoop_result_shape condition assignment name context primitive handler
      functions (fuel+1) production loopResult loopCost loopRun
    · subst loopResult
      simp [loopRun,evalPanValueFfiProgSteps,panValueReturnSteps,evalPanValueExpCountedWith,
        evalPanValueExpCounted,evalPanValueExp,panValuePayloadWithinLimit,
        panValuePayloadSizeFuel,panValueExpStepCost] at run
      exact ⟨locals,loopCost,rfl,by omega⟩
    · subst loopResult
      simp [loopRun] at run

/-- A returned whole declaration run exposes the counted loop run after the
local has been initialized; declaration and wrapper cost seven steps. -/
theorem counted_declared_assignLoop_whole_invert {σ : Type}
    (condition assignment : Exp (RiscV.Word 64)) (name : VarName) (initial returned : BitVec 64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (cost : Nat)
    (returnLocals returnGlobals : VarName → Option (PanValue (RiscV.Word 64)))
    (returnMemory : BitVec 64 → Option (PanValue (BitVec 64))) (returnFfi : FfiState σ)
    (returnValues : List (PanValue (RiscV.Word 64)))
    (run : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+4)
      production.locals production.globals production.memory production.ffi
      (.dec name .one (.const initial) (.seq .skip (.seq
        (.while condition (.assign .local name assignment)) (.return (.const returned)))))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.returned returnLocals returnGlobals returnMemory returnFfi returnValues,cost)) :
    ∃ finalLocals loopCost,
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
        (updatePanValueMap production.locals name (.word initial)) production.globals production.memory production.ffi
        (.while condition (.assign .local name assignment))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
          some (.normal finalLocals production.globals production.memory production.ffi,loopCost) ∧
      cost = loopCost+7 := by
  have accepted : panValueDecAccepted production.structs production.baseAddress production.topAddress panSemBitVec64BytesInWord
      production.locals production.globals production.memory (.const initial) (some (panSemBitVec64MemoryAccess production)) .one =
      some (.word initial,1) := by
    simp [panValueDecAccepted,evalPanValueExpCounted,evalPanValueExp,panValueExpStepCost,panValueShape,panShapeMatches]
  rw [evalPanValueFfiProgSteps,accepted] at run
  simp only [Option.elim_some] at run
  let entry := {production with locals := updatePanValueMap production.locals name (.word initial)}
  cases bodyRun : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+3)
      (updatePanValueMap production.locals name (.word initial)) production.globals production.memory production.ffi
      (.seq .skip (.seq (.while condition (.assign .local name assignment)) (.return (.const returned))))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) with
  | none => simp [bodyRun] at run
  | some pair =>
    rcases pair with ⟨bodyResult,bodyCost⟩
    cases bodyResult with
    | returned locals globals memory ffi values =>
      simp [bodyRun,restorePanValueFfiLocal] at run
      have bodyRun' : evalPanValueFfiProgSteps context primitive handler entry.structs functions
          entry.baseAddress entry.topAddress panSemBitVec64BytesInWord (fuel+3)
          entry.locals entry.globals entry.memory entry.ffi
          (.seq .skip (.seq (.while condition (.assign .local name assignment)) (.return (.const returned))))
          (memoryAccess := some (panSemBitVec64MemoryAccess entry)) =
            some (.returned locals globals memory ffi values,bodyCost) := by
        simpa [entry,panSemBitVec64MemoryAccess] using bodyRun
      obtain ⟨finalLocals,loopCost,loopRun,costEq⟩ := counted_assignLoop_anyReturn_invert condition assignment name returned
        context primitive handler functions fuel entry bodyCost locals globals memory ffi values bodyRun'
      refine ⟨finalLocals,loopCost,?_,?_⟩
      · simpa [entry,panSemBitVec64MemoryAccess] using loopRun
      · omega
    | _ => simp [bodyRun,restorePanValueFfiLocal] at run

/-- A counted declared assignment loop yields an actual bounded native RISC-V run. -/
theorem counted_declared_assignLoop_native_riscv {σ : Type}
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
    (finalLocals : VarName → Option (PanValue (RiscV.Word 64))) (loopCost budget : Nat) (returned : BitVec 64)
    (clock : loopCost ≤ source.clock*(panValueExpStepCost condition+panValueExpStepCost assignment+2) +
      (panValueExpStepCost condition+1))
    (budgetBound : loopCost+7 ≤ budget)
    (loopExec : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
      (updatePanValueMap production.locals name (.word initial)) production.globals production.memory production.ffi
      (.while condition (.assign .local name assignment))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal finalLocals production.globals production.memory production.ffi,loopCost))
    (conditionShape : ScalarExpression (scalarDeclContext (ctxtFcExactHOL caller.funcs caller.eids [] [] []) (ofString name)) (expToHOL condition))
    (bodyShape : BranchProgram (scalarDeclContext (ctxtFcExactHOL caller.funcs caller.eids [] [] []) (ofString name))
      (.assign .local (ofString name) (expToHOL assignment)))
    (panCode : pan.code = HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse)
    (initRun : pan.evaluateHOLFiniteState (nestedSeqHOL initializers) = (none,middle))
    (sourceFound : source.code.lookup (newMainNameHOL declarations) = some ([],
      .dec (ofString name) .one (.const initial) (.seq .skip (.seq
        (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned)))),.one))
    (entryClock : middle.clock ≠ 0)
    (globalFound : (functionsHOL declarations).lookup start = some ([],
      .dec (ofString name) .one (.const initial) (.seq .skip (.seq
        (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned)))),.one))
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
      (declaredAssignLoopLimit declarations initializers globals caller condition assignment name initial returned pan budget loopCtxt .ln) target) :
    let entry := assignLoopEntryProgram declarations initializers caller loopCtxt .ln
    ∃ sourceResult sourceFinal,
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+4)
        production.locals production.globals production.memory production.ffi
        (.dec name .one (.const initial) (.seq .skip (.seq (.while condition (.assign .local name assignment)) (.return (.const returned)))))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (sourceResult,loopCost+7) ∧
      source.evaluateHOLFiniteState (.dec (ofString name) .one (.const initial) (.seq .skip (.seq (.while (expToHOL condition)
        (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned))))) =
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
  classical
  let entry := assignLoopEntryProgram declarations initializers caller loopCtxt .ln
  let limit := declaredAssignLoopLimit declarations initializers globals caller condition assignment name initial returned pan budget loopCtxt .ln
  obtain ⟨sourceResult,sourceFinal,sourceExec,sourceRun,_,_⟩ :=
    counted_declared_assignLoop_return condition assignment name initial returned context primitive handler functions
      conditionRanged assignmentRanged nameRanged fuel production source rel ranged finalLocals loopCost clock loopExec
      (ctxtFcExactHOL caller.funcs caller.eids [] [] []) conditionShape bodyShape
  refine ⟨sourceResult,sourceFinal,sourceExec,sourceRun,?_⟩
  obtain ⟨panCodeRel,programShapes,codeRel,entryMember⟩ := native.frontendFacts declarations start initializers globals caller
    loopCtxt entry limit pan crep target rfl
    (.dec (ofString name) .one (.const initial) (.seq .skip (.seq
      (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned)))))
    .one globalFound funs exns globalCompiled panCode crepCode unique localised preShapes noTail initShape
  let initialLoop := {target with locals := .ln}
  have normalized := emptyLive_initial_relations loopCtxt crep target _ crepRel memRel globalsRel localsRel native.data
  apply native.machineBound declarations start caller loopCtxt entry limit target programShapes entryMember sourceFinal
  intro word wordRel
  obtain ⟨_,sourceFinal',_,_,_,_,_,sourceRun',_,_,_,_,_,_,_,_,_,extra,loopPost,_,_,_,_,_,_,_,_,_,_,_,_,nativeReady⟩ :=
    counted_declared_assignLoop_globalEntry_riscv condition assignment initial loopCost budget budgetBound declarations start initializers
      globals caller production source pan middle crep rel ranged name nameRanged returned conditionRanged assignmentRanged clock
      conditionShape bodyShape panCode initRun sourceFound entryClock globalRel panStateRel panCodeRel panExcpRel panLocalsRel
      initLocalised initShape loopCtxt .ln initialLoop word normalized.1 normalized.2.1 normalized.2.2.1
      (by simpa [initialLoop] using codeRel) normalized.2.2.2.1 wordRel context primitive handler functions fuel finalLocals loopExec
  have finalEq : sourceFinal = sourceFinal' := (Prod.mk.inj (sourceRun.symm.trans sourceRun')).2
  subst sourceFinal'
  change NativeReturnedReady entry {initialLoop with clock := initialLoop.clock+extra}
    {word with clock := word.clock+extra} limit sourceFinal at nativeReady
  exact ⟨extra,nativeReady⟩

/-- A successful counted declared-loop source run and an independent source
budget give a bounded native RISC-V run of its whole-compiler output. -/
theorem counted_declared_assignLoop_whole_native_riscv {σ : Type}
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
    (panCode : pan.code = HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse)
    (initRun : pan.evaluateHOLFiniteState (nestedSeqHOL initializers) = (none,middle))
    (sourceFound : source.code.lookup (newMainNameHOL declarations) = some ([],
      .dec (ofString name) .one (.const initial) (.seq .skip (.seq
        (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned)))),.one))
    (entryClock : middle.clock ≠ 0)
    (globalFound : (functionsHOL declarations).lookup start = some ([],
      .dec (ofString name) .one (.const initial) (.seq .skip (.seq
        (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned)))),.one))
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
      (declaredAssignLoopLimit declarations initializers globals caller condition assignment name initial returned pan budget loopCtxt .ln) target) :
    let entry := assignLoopEntryProgram declarations initializers caller loopCtxt .ln
    ∃ sourceFinal,
      source.evaluateHOLFiniteState (.dec (ofString name) .one (.const initial) (.seq .skip (.seq (.while (expToHOL condition)
        (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned))))) =
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
  obtain ⟨finalLocals,loopCost,loopExec,costEq⟩ := counted_declared_assignLoop_whole_invert condition assignment name initial returned
    context primitive handler functions fuel production cost returnLocals returnGlobals returnMemory returnFfi returnValues wholeRun
  have loopClock : loopCost ≤ source.clock*(panValueExpStepCost condition+panValueExpStepCost assignment+2) +
      (panValueExpStepCost condition+1) := by omega
  have loopBudget : loopCost+7 ≤ budget := by omega
  obtain ⟨_,sourceFinal,_,sourceRun,outcome,ticks,finalMachine,finalFfi,bound,machineRun,correspondence⟩ :=
    counted_declared_assignLoop_native_riscv declarations start initializers globals caller condition assignment name initial context primitive handler
      functions conditionRanged assignmentRanged nameRanged fuel production source pan middle crep rel ranged finalLocals loopCost budget
      returned loopClock loopBudget loopExec conditionShape bodyShape panCode initRun sourceFound entryClock globalFound funs exns globalCompiled
      globalRel panStateRel crepCode unique localised preShapes noTail panExcpRel panLocalsRel initLocalised initShape loopCtxt target
      crepRel memRel globalsRel localsRel native
  exact ⟨sourceFinal,sourceRun,outcome,ticks,finalMachine,finalFfi,bound,machineRun,correspondence⟩

end SteppedFlapjack.PanToCrepSteps
