import SteppedFlapjack.PanToCrepSteps.CountedAssignLoopReturn
import SteppedFlapjack.PanToCrepSteps.TailEntryCrepBound
import SteppedFlapjack.PanToCrepSteps.TailEntryRelations
import SteppedFlapjack.CrepToLoopSteps.RiscVInputs
import SteppedFlapjack.LoopToWordSteps.TailRiscVSetup

/-! Counted assignment-loop programs through the generated entry to RISC-V.

The machine result is supplied for every compatible backend setup; this module
does not construct the setup or exclude the resource-failure alternative. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open Flapjack.LoopSemStateFiniteExact Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend

/-- A normally terminating counted assignment loop and return yield the actual
generated Crep and optimized Loop entry runs, and a bounded RISC-V run for each
compatible backend setup, using the separately supplied source budget. -/
theorem counted_assignLoop_globalEntry_riscv {σ : Type}
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
    (loopCtxt : CrepToLoopContextExact) (live : NumSet)
    (target : LoopSemStateFiniteExact 64 σ) (word : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) σ)
    (crepRel : crepToLoopStateRelExact crep target)
    (memRel : crepToLoopMemRelHOLExact crep.memory target.memory crep.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact crep.globals target.globals)
    (codeRel : crepToLoopCodeRelExact loopCtxt crep.code target.code)
    (localsRel : crepToLoopLocalsRelExact loopCtxt live crep.locals target.locals)
    (loopWordRel : loopToWordStateRelHOLExact target word) :
    let callee := newMainNameHOL declarations
    let body := ProgHOL.assign .local (ofString name) (expToHOL assignment)
    let original := ProgHOL.seq .skip (.seq (.while (expToHOL condition) body) (.return (.const returned)))
    let lowered := compileProgExactHOL globals original
    let calleeContext := ctxtFcExactHOL caller.funcs caller.eids [] [] []
    let crepInit := compileProgExactHOLW caller (nestedSeqHOL initializers)
    let globalLimit := controlSteps (nestedSeqHOL initializers) pan +
      (3 + sizeOf (compileProgExactHOL globals (.skip : ProgHOL 64)) +
        sizeOf (compileProgExactHOL globals body) +
        sizeOf (compileProgExactHOL globals (.return (.const returned)))) * budget + 2
    let crepLimit := sizeOf crepInit + 2 +
      (3 + sizeOf (compileProgExactHOLW calleeContext (compileProgExactHOL globals (.skip))) +
        sizeOf (compileProgExactHOLW calleeContext (compileProgExactHOL globals body)) +
        sizeOf (compileProgExactHOLW calleeContext (compileProgExactHOL globals (.return (.const returned))))) * globalLimit
    ∃ sourceResult sourceFinal panPost crepMiddle crepPost crepResult,
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+3)
        production.locals production.globals production.memory production.ffi
        (.seq .skip (.seq (.while condition (.assign .local name assignment)) (.return (.const returned))))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (sourceResult,loopCost+5) ∧
      source.evaluateHOLFiniteState original = (some (.returned (.val (.word returned))),sourceFinal) ∧
      panGlobalsStateRelHOLExact (goodResHOL (some (.returned (.val (.word returned))))) globals sourceFinal panPost ∧
      evalCrepSemHOLProgExact crep crepInit = (none,crepMiddle) ∧
      crepMiddle.code.lookup callee = some ([],compileProgExactHOLW calleeContext lowered) ∧
      crepMiddle.clock ≠ 0 ∧
      evalCrepSemHOLProgExact (decClockCrepSemHOL {crepMiddle with locals := HolFiniteMapExact.empty.updateList []})
        (compileProgExactHOLW calleeContext lowered) = (crepResult,crepPost) ∧
      CompleteCrepResult crepResult ∧ panToCrepStateRelFiniteExact panPost crepPost ∧
      pcCompileCorrectResultRel calleeContext panPost crepPost (some (.returned (.val (.word returned)))) crepResult ∧
      SteppedFlapjack.CrepSteps.steps (.seq crepInit (.call none callee [])) crep ≤ crepLimit ∧
      ∃ (crepCondition : CrepExpHOL 64) (extra : Nat) (loopPost : LoopSemStateFiniteExact 64 σ),
        compileExpExactHOLW calleeContext (compileExpExactHOL globals (expToHOL condition)) = ([crepCondition],.one) ∧
        let calleeInit := compileProgExactHOLW calleeContext (compileProgExactHOL globals (.skip))
        let crepBody := compileProgExactHOLW calleeContext (compileProgExactHOL globals body)
        let crepTail := compileProgExactHOLW calleeContext (compileProgExactHOL globals (.return (.const returned)))
        let compiledCallee := ocompileHOLExact (ctxtFcExact loopCtxt.target loopCtxt.funcs [] []) .ln
          (.seq calleeInit (.seq (.while crepCondition crepBody) crepTail))
        let loopEntry := optimiseHOL (compileHOLExact loopCtxt live (.seq crepInit (.call none callee [])))
        let loopLimit := branchTailLoopLimit loopCtxt live callee crepInit calleeInit crepCondition crepBody crepTail crepLimit
        SteppedFlapjack.LoopLiveSteps.SingleTailEntryShape (findLabExact loopCtxt callee) loopEntry ∧
        LoopSequenceSource compiledCallee ∧
        sptLookup (findLabExact loopCtxt callee) {target with clock := target.clock+extra}.code = some ([],compiledCallee) ∧
        loopToWordStateRelHOLExact {target with clock := target.clock+extra} {word with clock := word.clock+extra} ∧
        evaluate loopEntry {target with clock := target.clock+extra} = (resultToLoop crepResult,loopPost) ∧
        resultToLoop crepResult ≠ some .error ∧ CompleteLoopResult (resultToLoop crepResult) ∧
        crepToLoopStateRelExact crepPost loopPost ∧
        SteppedFlapjack.LoopSteps.steps loopEntry {target with clock := target.clock+extra} ≤ loopLimit ∧
        TailRiscVReady loopEntry {target with clock := target.clock+extra} loopPost (resultToLoop crepResult)
          {word with clock := word.clock+extra} loopLimit := by
  let original : ProgHOL 64 := .seq .skip (.seq (.while (expToHOL condition)
    (.assign .local (ofString name) (expToHOL assignment))) (.return (.const returned)))
  let lowered := compileProgExactHOL globals original
  let calleeContext := ctxtFcExactHOL caller.funcs caller.eids [] [] []
  obtain ⟨sourceResult,sourceFinal,panPost,sourceExec,sourceRun,panRun,postRel,globalBound⟩ :=
    counted_assignLoop_globalEntry declarations start initializers globals calleeContext condition assignment name context primitive handler
      functions conditionRanged assignmentRanged nameRanged fuel production source pan middle rel ranged clock finalLocals loopCost budget
      returned budgetBound loopExec conditionShape bodyShape panCode initRun sourceFound entryClock globalRel
  have found := globalEntry_lowered_callee_lookup declarations start (nestedSeqHOL initializers) globals pan middle source
    original .one panCode initRun sourceFound globalRel
  have lookup := global_lowered_lookup_after_init declarations start (newMainNameHOL declarations) pan middle
    (nestedSeqHOL initializers) lowered .one panCode initRun found
  obtain ⟨crepMiddle,crepPost,crepResult,crepInitRun,crepFound,crepClock,calleeLocalised,calleeStateRel,calleeCodeRel,
    calleeExcpRel,calleeLocalsRel,crepRun,complete,finalRel,resultRel⟩ :=
    tailEntry_compiled_execution pan middle panPost crep caller (nestedSeqHOL initializers) lowered
      (newMainNameHOL declarations) HolFiniteMapExact.empty .one (some (.returned (.val (.word returned)))) (.return _)
      initRun lookup entryClock panRun panStateRel panCodeRel panExcpRel panLocalsRel initLocalised
  have crepBound := tailEntry_crep_bound (nestedSeqHOL initializers) (newMainNameHOL declarations) calleeContext
    (compileProgExactHOL globals (.skip)) (compileExpExactHOL globals (expToHOL condition))
    (compileProgExactHOL globals (.assign .local (ofString name) (expToHOL assignment)))
    (compileProgExactHOL globals (.return (.const returned)))
    (globalCompile_branch_shape globals (.skip : BranchProgram calleeContext .skip))
    (globalCompile_scalar_shape globals conditionShape) (globalCompile_branch_shape globals bodyShape)
    (globalCompile_branch_shape globals (.return (.const _))) pan middle panPost (some (.returned (.val (.word returned))))
    HolFiniteMapExact.empty .one crep crepMiddle (compileProgExactHOLW caller (nestedSeqHOL initializers))
    (branch_compile initShape) initRun (by simpa [lowered,original,compileProgExactHOL] using lookup) entryClock
    (by simpa [lowered,original,compileProgExactHOL] using panRun) (by simp) crepInitRun
    (by simpa [lowered,original,compileProgExactHOL] using crepFound) crepClock calleeStateRel calleeCodeRel calleeExcpRel
    calleeLocalsRel (by simpa [lowered,original,compileProgExactHOL] using calleeLocalised)
  have scaled := Nat.mul_le_mul_left
    (3 + sizeOf (compileProgExactHOLW calleeContext (compileProgExactHOL globals (.skip))) +
      sizeOf (compileProgExactHOLW calleeContext (compileProgExactHOL globals (.assign .local (ofString name) (expToHOL assignment)))) +
      sizeOf (compileProgExactHOLW calleeContext (compileProgExactHOL globals (.return (.const returned))))) globalBound
  have boundedCrep : SteppedFlapjack.CrepSteps.steps
      (.seq (compileProgExactHOLW caller (nestedSeqHOL initializers)) (.call none (newMainNameHOL declarations) [])) crep ≤
      sizeOf (compileProgExactHOLW caller (nestedSeqHOL initializers)) + 2 +
      (3 + sizeOf (compileProgExactHOLW calleeContext (compileProgExactHOL globals (.skip))) +
        sizeOf (compileProgExactHOLW calleeContext (compileProgExactHOL globals (.assign .local (ofString name) (expToHOL assignment)))) +
        sizeOf (compileProgExactHOLW calleeContext (compileProgExactHOL globals (.return (.const returned))))) *
      (controlSteps (nestedSeqHOL initializers) pan +
        (3 + sizeOf (compileProgExactHOL globals (.skip : ProgHOL 64)) +
          sizeOf (compileProgExactHOL globals (.assign .local (ofString name) (expToHOL assignment))) +
          sizeOf (compileProgExactHOL globals (.return (.const returned)))) * budget + 2) := by
    omega
  refine ⟨sourceResult,sourceFinal,panPost,crepMiddle,crepPost,crepResult,sourceExec,sourceRun,postRel,crepInitRun,
    crepFound,crepClock,crepRun,complete,finalRel,resultRel,boundedCrep,?_⟩
  let crepInit := compileProgExactHOLW caller (nestedSeqHOL initializers)
  obtain ⟨crepCondition,conditionEq,conditionCrepShape,initCrepShape,calleeInitShape,bodyCrepShape,tailCrepShape,compiledEq⟩ :=
    tailEntry_compiled_shapes caller (nestedSeqHOL initializers) (compileProgExactHOL globals (.skip))
      (compileExpExactHOL globals (expToHOL condition))
      (compileProgExactHOL globals (.assign .local (ofString name) (expToHOL assignment)))
      (compileProgExactHOL globals (.return (.const returned))) initShape
      (globalCompile_branch_shape globals (.skip : BranchProgram calleeContext .skip))
      (globalCompile_scalar_shape globals conditionShape) (globalCompile_branch_shape globals bodyShape)
      (globalCompile_branch_shape globals (.return (.const _)))
  have found' := crepFound
  have run' := crepRun
  simp only [lowered,original,compileProgExactHOL] at found' run' compiledEq
  rw [compiledEq] at found' run'
  obtain ⟨extra,loopPost,entryShape,calleeShape,calleeLookup,loopRun,notError,loopComplete,shiftedRel,postLoopRel,loopBound⟩ :=
    branchTail_riscv_inputs loopCtxt live (newMainNameHOL declarations) crepInit initCrepShape
      (compileProgExactHOLW calleeContext (compileProgExactHOL globals (.skip))) calleeInitShape
      crepCondition conditionCrepShape
      (compileProgExactHOLW calleeContext (compileProgExactHOL globals (.assign .local (ofString name) (expToHOL assignment))))
      (compileProgExactHOLW calleeContext (compileProgExactHOL globals (.return (.const returned))))
      bodyCrepShape tailCrepShape crep crepMiddle crepPost crepResult target word _ crepInitRun
      (by simpa only [compileProgExactHOL] using found') crepClock
      (by simpa only [compileProgExactHOL] using run') complete crepRel memRel globalsRel codeRel localsRel loopWordRel boundedCrep
  refine ⟨crepCondition,extra,loopPost,conditionEq,entryShape,calleeShape,calleeLookup,shiftedRel,
    loopRun,notError,loopComplete,postLoopRel,loopBound,?_⟩
  exact tailRiscVReady_of_loop _ loopPost _ _ _ entryShape calleeShape calleeLookup
    loopRun notError shiftedRel loopComplete loopBound

end SteppedFlapjack.PanToCrepSteps
