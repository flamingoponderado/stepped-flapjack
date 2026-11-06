import SteppedFlapjack.PanToCrepSteps.CountedDeclaredAssignLoop
import SteppedFlapjack.PanToCrepSteps.TailEntryDeclBound
import SteppedFlapjack.PanToCrepSteps.TailEntryRelations

/-! Declared assignment-loop programs through the generated Crep entry. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open SteppedFlapjack.CrepToLoopSteps

/-- The generated Crep entry for a declared assignment loop is bounded by the source budget. -/
theorem counted_declared_assignLoop_globalEntry_crep {σ : Type}
    (condition assignment : Exp (RiscV.Word 64)) (initial : BitVec 64) (loopCost sourceBudget : Nat)
    (budgetBound : loopCost+7 ≤ sourceBudget)
    (declarations : List (DeclHOL 64)) (start : MlString) (initializers : List (ProgHOL 64))
    (globals : PanGlobalsContextExact 64) (caller : PanToCrepContextExact 64)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source pan middle : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs]
    (crep : CrepSemHOLState 64 σ)
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (name : VarName) (nameRanged : NameRanged name) (returned : BitVec 64)
    (conditionRanged : ExpByteRanged condition) (assignmentRanged : ExpByteRanged assignment)
    (sourceClock : loopCost ≤ source.clock*(panValueExpStepCost condition+panValueExpStepCost assignment+2) +
      (panValueExpStepCost condition+1))
    (conditionShape : ScalarExpression (scalarDeclContext (ctxtFcExactHOL caller.funcs caller.eids [] [] []) (ofString name)) (expToHOL condition))
    (bodyShape : BranchProgram (scalarDeclContext (ctxtFcExactHOL caller.funcs caller.eids [] [] []) (ofString name))
      (.assign .local (ofString name) (expToHOL assignment)))
    (panCode : pan.code = HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse)
    (initRun : pan.evaluateHOLFiniteState (nestedSeqHOL initializers) = (none,middle))
    (sourceFound : source.code.lookup (newMainNameHOL declarations) = some ([],
      .dec (ofString name) .one (.const initial)
        (.seq .skip (.seq (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned)))),.one))
    (entryClock : middle.clock ≠ 0)
    (globalRel : panGlobalsStateRelHOLExact true globals source (callEntryStateHOLFinite middle HolFiniteMapExact.empty))
    (panStateRel : panToCrepStateRelFiniteExact pan crep)
    (panCodeRel : codeRelExactHOLW caller pan.code crep.code)
    (panExcpRel : panToCrepExcpRelFiniteExact caller.eids pan.eshapes)
    (panLocalsRel : panToCrepLocalsRelFiniteExact caller pan.locals crep.locals)
    (initLocalised : localisedProgHOL (nestedSeqHOL initializers) = true)
    (initShape : BranchProgram caller (nestedSeqHOL initializers))
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat)
    (finalLocals : VarName → Option (PanValue (RiscV.Word 64)))
    (loopExec : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
      (updatePanValueMap production.locals name (.word initial)) production.globals production.memory production.ffi
      (.while condition (.assign .local name assignment))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal finalLocals production.globals production.memory production.ffi,loopCost)) :
    let callee := newMainNameHOL declarations
    let originalBody : ProgHOL 64 := .dec (ofString name) .one (.const initial)
      (.seq .skip (.seq (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned))))
    let loweredBody := compileProgExactHOL globals originalBody
    let calleeContext := ctxtFcExactHOL caller.funcs caller.eids [] [] []
    let crepInit := compileProgExactHOLW caller (nestedSeqHOL initializers)
    let inner := scalarDeclContext calleeContext (ofString name)
    let globalLimit := controlSteps (nestedSeqHOL initializers) pan +
      (4 + sizeOf (compileProgExactHOL globals (.skip : ProgHOL 64)) +
        sizeOf (compileProgExactHOL globals (.assign .local (ofString name) (expToHOL assignment))) +
        sizeOf (compileProgExactHOL globals (.return (.const returned)))) * sourceBudget + 2
    let crepLimit := sizeOf crepInit + 2 +
      (4 + sizeOf (compileProgExactHOLW inner (compileProgExactHOL globals (.skip))) +
        sizeOf (compileProgExactHOLW inner (compileProgExactHOL globals (.assign .local (ofString name) (expToHOL assignment)))) +
        sizeOf (compileProgExactHOLW inner (compileProgExactHOL globals (.return (.const returned))))) * globalLimit
    ∃ sourceResult sourceFinal panPost crepMiddle crepPost crepResult,
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+4)
        production.locals production.globals production.memory production.ffi
        (.dec name .one (.const initial)
          (.seq .skip (.seq (.while condition (.assign .local name assignment)) (.return (.const returned)))))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (sourceResult,loopCost+7) ∧
      source.evaluateHOLFiniteState originalBody = (some (.returned (.val (.word returned))),sourceFinal) ∧
      panGlobalsStateRelHOLExact (goodResHOL (some (.returned (.val (.word returned))))) globals sourceFinal panPost ∧
      evalCrepSemHOLProgExact crep crepInit = (none,crepMiddle) ∧
      crepMiddle.code.lookup callee = some ([],compileProgExactHOLW calleeContext loweredBody) ∧
      crepMiddle.clock ≠ 0 ∧
      evalCrepSemHOLProgExact (decClockCrepSemHOL {crepMiddle with locals := HolFiniteMapExact.empty.updateList []})
        (compileProgExactHOLW calleeContext loweredBody) = (crepResult,crepPost) ∧
      CompleteCrepResult crepResult ∧ panToCrepStateRelFiniteExact panPost crepPost ∧
      pcCompileCorrectResultRel calleeContext panPost crepPost (some (.returned (.val (.word returned)))) crepResult ∧
      SteppedFlapjack.CrepSteps.steps (.seq crepInit (.call none callee [])) crep ≤ crepLimit := by
  let originalBody : ProgHOL 64 := .dec (ofString name) .one (.const initial)
    (.seq .skip (.seq (.while (expToHOL condition) (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned))))
  let loweredBody := compileProgExactHOL globals originalBody
  let calleeContext := ctxtFcExactHOL caller.funcs caller.eids [] [] []
  obtain ⟨sourceResult,sourceFinal,panPost,sourceExec,sourceRun,panRun,postRel,globalBound⟩ :=
    counted_declared_assignLoop_globalEntry declarations start initializers globals calleeContext condition assignment name initial returned
      context primitive handler functions conditionRanged assignmentRanged nameRanged fuel production source pan middle rel ranged
      finalLocals loopCost sourceBudget sourceClock budgetBound loopExec conditionShape bodyShape panCode initRun sourceFound entryClock globalRel
  have found := globalEntry_lowered_callee_lookup declarations start (nestedSeqHOL initializers) globals pan middle source
    originalBody .one panCode initRun sourceFound globalRel
  have lookup := global_lowered_lookup_after_init declarations start (newMainNameHOL declarations) pan middle
    (nestedSeqHOL initializers) loweredBody .one panCode initRun found
  obtain ⟨crepMiddle,crepPost,crepResult,crepInitRun,crepFound,crepClock,calleeLocalised,calleeStateRel,calleeCodeRel,
    calleeExcpRel,calleeLocalsRel,crepRun,complete,finalRel,resultRel⟩ :=
    tailEntry_compiled_execution pan middle panPost crep caller (nestedSeqHOL initializers) loweredBody
      (newMainNameHOL declarations) HolFiniteMapExact.empty .one (some (.returned (.val (.word returned)))) (.return _)
      initRun lookup entryClock panRun panStateRel panCodeRel panExcpRel panLocalsRel initLocalised
  have crepBound := tailEntry_decl_crep_bound (nestedSeqHOL initializers) (newMainNameHOL declarations) calleeContext
    (ofString name) (compileExpExactHOL globals (.const initial))
    (compileProgExactHOL globals (.skip)) (compileExpExactHOL globals (expToHOL condition))
    (compileProgExactHOL globals (.assign .local (ofString name) (expToHOL assignment))) (compileProgExactHOL globals (.return (.const returned)))
    (globalCompile_scalar_shape globals (.const _)) (globalCompile_branch_shape globals .skip)
    (globalCompile_scalar_shape globals conditionShape) (globalCompile_branch_shape globals bodyShape)
    (globalCompile_branch_shape globals (.return (.const _))) pan middle panPost (some (.returned (.val (.word returned))))
    HolFiniteMapExact.empty .one crep crepMiddle (compileProgExactHOLW caller (nestedSeqHOL initializers))
    (branch_compile initShape) initRun (by simpa [loweredBody,originalBody,compileProgExactHOL] using lookup) entryClock
    (by simpa [loweredBody,originalBody,compileProgExactHOL] using panRun) (by simp) crepInitRun
    (by simpa [loweredBody,originalBody,compileProgExactHOL] using crepFound) crepClock calleeStateRel calleeCodeRel calleeExcpRel
    calleeLocalsRel (by simpa [loweredBody,originalBody,compileProgExactHOL] using calleeLocalised)
  refine ⟨sourceResult,sourceFinal,panPost,crepMiddle,crepPost,crepResult,sourceExec,sourceRun,postRel,crepInitRun,
    crepFound,crepClock,crepRun,complete,finalRel,resultRel,?_⟩
  have scaled := Nat.mul_le_mul_left
    (4 + sizeOf (compileProgExactHOLW (scalarDeclContext calleeContext (ofString name)) (compileProgExactHOL globals (.skip))) +
      sizeOf (compileProgExactHOLW (scalarDeclContext calleeContext (ofString name)) (compileProgExactHOL globals (.assign .local (ofString name) (expToHOL assignment)))) +
      sizeOf (compileProgExactHOLW (scalarDeclContext calleeContext (ofString name)) (compileProgExactHOL globals (.return (.const returned))))) globalBound
  dsimp only [calleeContext] at scaled crepBound ⊢
  omega


end SteppedFlapjack.PanToCrepSteps
