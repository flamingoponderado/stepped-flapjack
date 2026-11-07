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

/-! Declared assignment-loop entry through the optimized Loop and RISC-V backend. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open Flapjack.LoopSemStateFiniteExact Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend

/-- The compiled initializer selected by the scalar declaration compiler. -/
def declaredAssignLoopValue (globals : PanGlobalsContextExact 64) (caller : PanToCrepContextExact 64)
    (initial : BitVec 64) : CrepExpHOL 64 :=
  (compileExpExactHOLW (ctxtFcExactHOL caller.funcs caller.eids [] [] [])
    (compileExpExactHOL globals (.const initial))).1.headD (.const 0)

/-- The compiled loop condition selected inside the scalar declaration. -/
def declaredAssignLoopCondition (globals : PanGlobalsContextExact 64) (caller : PanToCrepContextExact 64)
    (name : VarName) (condition : Exp (RiscV.Word 64)) : CrepExpHOL 64 :=
  (compileExpExactHOLW (scalarDeclContext (ctxtFcExactHOL caller.funcs caller.eids [] [] []) (ofString name))
    (compileExpExactHOL globals (expToHOL condition))).1.headD (.const 0)

/-- Source-budget-derived Loop limit for a declared assignment-loop entry. -/
noncomputable def declaredAssignLoopLimit {σ : Type}
    (declarations : List (DeclHOL 64)) (initializers : List (ProgHOL 64))
    (globals : PanGlobalsContextExact 64) (caller : PanToCrepContextExact 64)
    (condition assignment : Exp (RiscV.Word 64)) (name : VarName) (initial returned : BitVec 64)
    (pan : PanSemStateFiniteExact 64 σ) (budget : Nat) (loopCtxt : CrepToLoopContextExact) (live : NumSet) : Nat :=
  let body := ProgHOL.assign .local (ofString name) (expToHOL assignment)
  let calleeContext := ctxtFcExactHOL caller.funcs caller.eids [] [] []
  let inner := scalarDeclContext calleeContext (ofString name)
  let crepInit := compileProgExactHOLW caller (nestedSeqHOL initializers)
  let globalLimit := controlSteps (nestedSeqHOL initializers) pan +
    (4 + sizeOf (compileProgExactHOL globals (.skip : ProgHOL 64)) +
      sizeOf (compileProgExactHOL globals body) +
      sizeOf (compileProgExactHOL globals (.return (.const returned)))) * budget + 2
  let crepLimit := sizeOf crepInit + 2 +
    (4 + sizeOf (compileProgExactHOLW inner (compileProgExactHOL globals (.skip))) +
      sizeOf (compileProgExactHOLW inner (compileProgExactHOL globals body)) +
      sizeOf (compileProgExactHOLW inner (compileProgExactHOL globals (.return (.const returned))))) * globalLimit
  branchTailDeclLoopLimit loopCtxt live (newMainNameHOL declarations) crepInit (calleeContext.vmax+1)
    (declaredAssignLoopValue globals caller initial)
    (compileProgExactHOLW inner (compileProgExactHOL globals (.skip)))
    (declaredAssignLoopCondition globals caller name condition)
    (compileProgExactHOLW inner (compileProgExactHOL globals body))
    (compileProgExactHOLW inner (compileProgExactHOL globals (.return (.const returned)))) crepLimit

/-- A counted declared assignment loop reaches the compiled backend with a source-derived bound. -/
theorem counted_declared_assignLoop_globalEntry_riscv {σ : Type}
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
    (loopCtxt : CrepToLoopContextExact) (live : NumSet)
    (target : LoopSemStateFiniteExact 64 σ) (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) σ)
    (crepRel : crepToLoopStateRelExact crep target)
    (memRel : crepToLoopMemRelHOLExact crep.memory target.memory crep.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact crep.globals target.globals)
    (codeRel : crepToLoopCodeRelExact loopCtxt crep.code target.code)
    (localsRel : crepToLoopLocalsRelExact loopCtxt live crep.locals target.locals)
    (loopWordRel : loopToWordStateRelHOLExact target word)
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
      SteppedFlapjack.CrepSteps.steps (.seq crepInit (.call none callee [])) crep ≤ crepLimit ∧
      let value := declaredAssignLoopValue globals caller initial
      let crepCond := declaredAssignLoopCondition globals caller name condition
      ∃ (extra : Nat) (loopPost : LoopSemStateFiniteExact 64 σ),
        compileExpExactHOLW calleeContext (compileExpExactHOL globals (.const initial)) = ([value],.one) ∧
        compileExpExactHOLW inner (compileExpExactHOL globals (expToHOL condition)) = ([crepCond],.one) ∧
        let compiledCallee := ocompileHOLExact (ctxtFcExact loopCtxt.target loopCtxt.funcs [] []) .ln
          (.dec (calleeContext.vmax+1) value
            (.seq (compileProgExactHOLW inner (compileProgExactHOL globals (.skip)))
              (.seq (.while crepCond (compileProgExactHOLW inner (compileProgExactHOL globals (.assign .local (ofString name) (expToHOL assignment)))))
                (compileProgExactHOLW inner (compileProgExactHOL globals (.return (.const returned)))))))
        let loopEntry := optimiseHOL (compileHOLExact loopCtxt live (.seq crepInit (.call none callee [])))
        let loopLimit := declaredAssignLoopLimit declarations initializers globals caller condition assignment name initial returned
          pan sourceBudget loopCtxt live
        SteppedFlapjack.LoopLiveSteps.SingleTailEntryShape (findLabExact loopCtxt callee) loopEntry ∧
        LoopSequenceSource compiledCallee ∧
        sptLookup (findLabExact loopCtxt callee) {target with clock := target.clock+extra}.code = some ([],compiledCallee) ∧
        loopToWordStateRelHOLExact {target with clock := target.clock+extra} {word with clock := word.clock+extra} ∧
        evaluate loopEntry {target with clock := target.clock+extra} = (resultToLoop crepResult,loopPost) ∧
        resultToLoop crepResult ≠ some .error ∧ CompleteLoopResult (resultToLoop crepResult) ∧
        crepToLoopStateRelExact crepPost loopPost ∧
        SteppedFlapjack.LoopSteps.steps loopEntry {target with clock := target.clock+extra} ≤ loopLimit ∧
        TailRiscVReady loopEntry {target with clock := target.clock+extra} loopPost (resultToLoop crepResult)
          {word with clock := word.clock+extra} loopLimit ∧
        FullInitReturnedReady loopEntry {target with clock := target.clock+extra}
          {word with clock := word.clock+extra} loopLimit sourceFinal := by
  obtain ⟨sourceResult,sourceFinal,panPost,crepMiddle,crepPost,crepResult,sourceExec,sourceRun,postRel,crepInitRun,
    crepFound,crepClock,crepRun,complete,finalRel,resultRel,crepBound⟩ :=
    counted_declared_assignLoop_globalEntry_crep condition assignment initial loopCost sourceBudget budgetBound
      declarations start initializers globals caller production source pan middle crep rel ranged name nameRanged returned
      conditionRanged assignmentRanged sourceClock conditionShape bodyShape panCode initRun sourceFound entryClock globalRel
      panStateRel panCodeRel panExcpRel panLocalsRel initLocalised initShape context primitive handler functions fuel finalLocals loopExec
  refine ⟨sourceResult,sourceFinal,panPost,crepMiddle,crepPost,crepResult,sourceExec,sourceRun,postRel,crepInitRun,
    crepFound,crepClock,crepRun,complete,finalRel,resultRel,crepBound,?_⟩
  let calleeContext := ctxtFcExactHOL caller.funcs caller.eids [] [] []
  let inner := scalarDeclContext calleeContext (ofString name)
  let crepInit := compileProgExactHOLW caller (nestedSeqHOL initializers)
  obtain ⟨value,crepCond,valueEq,valueShape,conditionEq,conditionCrepShape,calleeInitShape,bodyCrepShape,tailCrepShape,compiledEq⟩ :=
    scalarDeclLoop_compiled_shapes calleeContext (ofString name)
      (compileExpExactHOL globals (.const initial))
      (compileExpExactHOL globals (expToHOL condition))
      (compileProgExactHOL globals (.skip)) (compileProgExactHOL globals (.assign .local (ofString name) (expToHOL assignment)))
      (compileProgExactHOL globals (.return (.const returned)))
      (globalCompile_scalar_shape globals (.const _)) (globalCompile_branch_shape globals .skip)
      (globalCompile_scalar_shape globals conditionShape) (globalCompile_branch_shape globals bodyShape)
      (globalCompile_branch_shape globals (.return (.const _)))
  have selectedValue : value = declaredAssignLoopValue globals caller initial := by
    change value = (compileExpExactHOLW calleeContext (compileExpExactHOL globals (.const initial))).1.headD (.const 0)
    rw [valueEq]
    rfl
  have selectedCondition : crepCond = declaredAssignLoopCondition globals caller name condition := by
    change crepCond = (compileExpExactHOLW inner (compileExpExactHOL globals (expToHOL condition))).1.headD (.const 0)
    rw [conditionEq]
    rfl
  subst value
  subst crepCond
  have found' := crepFound
  have run' := crepRun
  simp only [compileProgExactHOL] at found' run' compiledEq
  rw [compiledEq] at found' run'
  obtain ⟨extra,loopPost,entryShape,calleeShape,calleeLookup,loopRun,notError,loopComplete,shiftedRel,postLoopRel,loopBound⟩ :=
    branchTailDecl_riscv_inputs loopCtxt live (newMainNameHOL declarations) crepInit (branch_compile initShape)
      (calleeContext.vmax+1) (declaredAssignLoopValue globals caller initial) valueShape (compileProgExactHOLW inner (compileProgExactHOL globals (.skip)))
      (declaredAssignLoopCondition globals caller name condition) (compileProgExactHOLW inner (compileProgExactHOL globals (.assign .local (ofString name) (expToHOL assignment))))
      (compileProgExactHOLW inner (compileProgExactHOL globals (.return (.const returned))))
      calleeInitShape conditionCrepShape bodyCrepShape tailCrepShape crep crepMiddle crepPost crepResult target word _
      crepInitRun (by simpa only [compileProgExactHOL] using found') crepClock
      (by simpa only [compileProgExactHOL] using run') complete crepRel memRel globalsRel codeRel localsRel loopWordRel crepBound
  refine ⟨extra,loopPost,valueEq,conditionEq,entryShape,calleeShape,calleeLookup,shiftedRel,
    loopRun,notError,loopComplete,postLoopRel,loopBound,?_⟩
  have ready := tailRiscVReady_of_loop _ loopPost _ _ _ entryShape calleeShape calleeLookup
    loopRun notError shiftedRel loopComplete loopBound
  have fullReady := fullInitTailReady_of_loop _ loopPost _ _ _ entryShape calleeShape calleeLookup
    loopRun notError shiftedRel loopComplete loopBound
  refine ⟨ready,?_⟩
  exact fullInitReturnedReady_of_return globals calleeContext sourceFinal panPost crepPost _ loopPost crepResult returned
    postRel finalRel resultRel postLoopRel _ _ _ fullReady

end SteppedFlapjack.PanToCrepSteps
