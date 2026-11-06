import SteppedFlapjack.PanToCrepSteps.CountedCountdown
import SteppedFlapjack.PanToCrepSteps.TailEntryDeclBound
import SteppedFlapjack.CrepToLoopSteps.DeclRiscVInputs
import SteppedFlapjack.LoopToWordSteps.TailRiscVSetup

/-! The counted countdown through the actual global Crep entry wrapper.

The Loop theorem also supplies a bounded machine execution for each compatible
`TailRiscVSetup`. It does not construct such a setup from a concrete machine
initial state, and the machine result retains the resource-failure alternative. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open Flapjack.LoopSemStateFiniteExact Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.LabToTargetSteps

/-- The generated entry's Crep execution and visit bound for the actual
counted countdown. The initial global and frontend state relations remain
explicit. -/
theorem countdown_globalEntry_crep {σ : Type} (count : Nat)
    (declarations : List (DeclHOL 64)) (start : MlString) (initializers : List (ProgHOL 64))
    (globals : PanGlobalsContextExact 64) (caller : PanToCrepContextExact 64)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source pan middle : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs]
    (crep : CrepSemHOLState 64 σ)
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (name : VarName) (nameRanged : NameRanged name) (wordRange : count < 2^64)
    (sourceClock : count ≤ source.clock) (returned : BitVec 64)
    (panCode : pan.code = HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse)
    (initRun : pan.evaluateHOLFiniteState (nestedSeqHOL initializers) = (none,middle))
    (sourceFound : source.code.lookup (newMainNameHOL declarations) = some ([],
      .dec (ofString name) .one (.const (BitVec.ofNat 64 count))
        (.seq .skip (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))),.one))
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
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat) :
    let callee := newMainNameHOL declarations
    let originalBody : ProgHOL 64 := .dec (ofString name) .one (.const (BitVec.ofNat 64 count))
      (.seq .skip (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned))))
    let loweredBody := compileProgExactHOL globals originalBody
    let calleeContext := ctxtFcExactHOL caller.funcs caller.eids [] [] []
    let crepInit := compileProgExactHOLW caller (nestedSeqHOL initializers)
    let inner := scalarDeclContext calleeContext (ofString name)
    let globalLimit := controlSteps (nestedSeqHOL initializers) pan +
      (4 + sizeOf (compileProgExactHOL globals (.skip : ProgHOL 64)) +
        sizeOf (compileProgExactHOL globals (countdownBodyHOL name)) +
        sizeOf (compileProgExactHOL globals (.return (.const returned)))) * (6*count+9) + 2
    let crepLimit := sizeOf crepInit + 2 +
      (4 + sizeOf (compileProgExactHOLW inner (compileProgExactHOL globals (.skip))) +
        sizeOf (compileProgExactHOLW inner (compileProgExactHOL globals (countdownBodyHOL name))) +
        sizeOf (compileProgExactHOLW inner (compileProgExactHOL globals (.return (.const returned))))) * globalLimit
    ∃ sourceResult sourceFinal panPost crepMiddle crepPost crepResult,
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+count+4)
        production.locals production.globals production.memory production.ffi
        (.dec name .one (.const (BitVec.ofNat 64 count))
          (.seq .skip (.seq (.while (.var .local name) (countdownBody name)) (.return (.const returned)))))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (sourceResult,6*count+9) ∧
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
  let originalBody : ProgHOL 64 := .dec (ofString name) .one (.const (BitVec.ofNat 64 count))
    (.seq .skip (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned))))
  let loweredBody := compileProgExactHOL globals originalBody
  let calleeContext := ctxtFcExactHOL caller.funcs caller.eids [] [] []
  obtain ⟨sourceResult,sourceFinal,panPost,sourceExec,sourceRun,panRun,postRel,globalBound⟩ :=
    countdown_globalEntry_inputs count declarations start initializers globals caller production source pan middle rel ranged
      name nameRanged wordRange sourceClock returned panCode initRun sourceFound entryClock globalRel context primitive handler functions fuel
  have found := globalEntry_lowered_callee_lookup declarations start (nestedSeqHOL initializers) globals pan middle source
    originalBody .one panCode initRun sourceFound globalRel
  have lookup := global_lowered_lookup_after_init declarations start (newMainNameHOL declarations) pan middle
    (nestedSeqHOL initializers) loweredBody .one panCode initRun found
  obtain ⟨crepMiddle,crepPost,crepResult,crepInitRun,crepFound,crepClock,calleeLocalised,calleeStateRel,calleeCodeRel,
    calleeExcpRel,calleeLocalsRel,crepRun,complete,finalRel,resultRel⟩ :=
    tailEntry_compiled_execution pan middle panPost crep caller (nestedSeqHOL initializers) loweredBody
      (newMainNameHOL declarations) HolFiniteMapExact.empty .one (some (.returned (.val (.word returned)))) (.return _)
      initRun lookup entryClock panRun panStateRel panCodeRel panExcpRel panLocalsRel initLocalised
  have localFound := scalarDeclContext_local calleeContext (ofString name)
  have bodyShape : BranchProgram (scalarDeclContext calleeContext (ofString name)) (countdownBodyHOL name) :=
    .assign _ _ localFound (.op .sub (.local _ _ localFound) (.const _))
  have crepBound := tailEntry_decl_crep_bound (nestedSeqHOL initializers) (newMainNameHOL declarations) calleeContext
    (ofString name) (compileExpExactHOL globals (.const (BitVec.ofNat 64 count)))
    (compileProgExactHOL globals (.skip)) (compileExpExactHOL globals (.var .local (ofString name)))
    (compileProgExactHOL globals (countdownBodyHOL name)) (compileProgExactHOL globals (.return (.const returned)))
    (globalCompile_scalar_shape globals (.const _)) (globalCompile_branch_shape globals .skip)
    (globalCompile_scalar_shape globals (.local _ _ localFound)) (globalCompile_branch_shape globals bodyShape)
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
      sizeOf (compileProgExactHOLW (scalarDeclContext calleeContext (ofString name)) (compileProgExactHOL globals (countdownBodyHOL name))) +
      sizeOf (compileProgExactHOLW (scalarDeclContext calleeContext (ofString name)) (compileProgExactHOL globals (.return (.const returned))))) globalBound
  dsimp only [calleeContext] at scaled crepBound ⊢
  omega

/-- The counted countdown reaches the optimized Loop entry within the source-derived limit. -/
theorem countdown_globalEntry_loop {σ : Type} (count : Nat)
    (declarations : List (DeclHOL 64)) (start : MlString) (initializers : List (ProgHOL 64))
    (globals : PanGlobalsContextExact 64) (caller : PanToCrepContextExact 64)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source pan middle : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs]
    (crep : CrepSemHOLState 64 σ)
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (name : VarName) (nameRanged : NameRanged name) (wordRange : count < 2^64)
    (sourceClock : count ≤ source.clock) (returned : BitVec 64)
    (panCode : pan.code = HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse)
    (initRun : pan.evaluateHOLFiniteState (nestedSeqHOL initializers) = (none,middle))
    (sourceFound : source.code.lookup (newMainNameHOL declarations) = some ([],
      .dec (ofString name) .one (.const (BitVec.ofNat 64 count))
        (.seq .skip (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))),.one))
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
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat) :
    let callee := newMainNameHOL declarations
    let originalBody : ProgHOL 64 := .dec (ofString name) .one (.const (BitVec.ofNat 64 count))
      (.seq .skip (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned))))
    let loweredBody := compileProgExactHOL globals originalBody
    let calleeContext := ctxtFcExactHOL caller.funcs caller.eids [] [] []
    let crepInit := compileProgExactHOLW caller (nestedSeqHOL initializers)
    let inner := scalarDeclContext calleeContext (ofString name)
    let globalLimit := controlSteps (nestedSeqHOL initializers) pan +
      (4 + sizeOf (compileProgExactHOL globals (.skip : ProgHOL 64)) +
        sizeOf (compileProgExactHOL globals (countdownBodyHOL name)) +
        sizeOf (compileProgExactHOL globals (.return (.const returned)))) * (6*count+9) + 2
    let crepLimit := sizeOf crepInit + 2 +
      (4 + sizeOf (compileProgExactHOLW inner (compileProgExactHOL globals (.skip))) +
        sizeOf (compileProgExactHOLW inner (compileProgExactHOL globals (countdownBodyHOL name))) +
        sizeOf (compileProgExactHOLW inner (compileProgExactHOL globals (.return (.const returned))))) * globalLimit
    ∃ sourceResult sourceFinal panPost crepMiddle crepPost crepResult,
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+count+4)
        production.locals production.globals production.memory production.ffi
        (.dec name .one (.const (BitVec.ofNat 64 count))
          (.seq .skip (.seq (.while (.var .local name) (countdownBody name)) (.return (.const returned)))))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (sourceResult,6*count+9) ∧
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
      ∃ (value condition : CrepExpHOL 64) (extra : Nat) (loopPost : LoopSemStateFiniteExact 64 σ),
        compileExpExactHOLW calleeContext (compileExpExactHOL globals (.const (BitVec.ofNat 64 count))) = ([value],.one) ∧
        compileExpExactHOLW inner (compileExpExactHOL globals (.var .local (ofString name))) = ([condition],.one) ∧
        let compiledCallee := ocompileHOLExact (ctxtFcExact loopCtxt.target loopCtxt.funcs [] []) .ln
          (.dec (calleeContext.vmax+1) value
            (.seq (compileProgExactHOLW inner (compileProgExactHOL globals (.skip)))
              (.seq (.while condition (compileProgExactHOLW inner (compileProgExactHOL globals (countdownBodyHOL name))))
                (compileProgExactHOLW inner (compileProgExactHOL globals (.return (.const returned)))))))
        let loopEntry := optimiseHOL (compileHOLExact loopCtxt live (.seq crepInit (.call none callee [])))
        let loopLimit := branchTailDeclLoopLimit loopCtxt live callee crepInit (calleeContext.vmax+1) value
          (compileProgExactHOLW inner (compileProgExactHOL globals (.skip))) condition
          (compileProgExactHOLW inner (compileProgExactHOL globals (countdownBodyHOL name)))
          (compileProgExactHOLW inner (compileProgExactHOL globals (.return (.const returned)))) crepLimit
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
  obtain ⟨sourceResult,sourceFinal,panPost,crepMiddle,crepPost,crepResult,sourceExec,sourceRun,postRel,crepInitRun,
    crepFound,crepClock,crepRun,complete,finalRel,resultRel,crepBound⟩ :=
    countdown_globalEntry_crep count declarations start initializers globals caller production source pan middle crep
      rel ranged name nameRanged wordRange sourceClock returned panCode initRun sourceFound entryClock globalRel
      panStateRel panCodeRel panExcpRel panLocalsRel initLocalised initShape context primitive handler functions fuel
  refine ⟨sourceResult,sourceFinal,panPost,crepMiddle,crepPost,crepResult,sourceExec,sourceRun,postRel,crepInitRun,
    crepFound,crepClock,crepRun,complete,finalRel,resultRel,crepBound,?_⟩
  let calleeContext := ctxtFcExactHOL caller.funcs caller.eids [] [] []
  let inner := scalarDeclContext calleeContext (ofString name)
  let crepInit := compileProgExactHOLW caller (nestedSeqHOL initializers)
  have found := scalarDeclContext_local calleeContext (ofString name)
  have bodyShape : BranchProgram inner (countdownBodyHOL name) :=
    .assign _ _ found (.op .sub (.local _ _ found) (.const _))
  obtain ⟨value,condition,valueEq,valueShape,conditionEq,conditionShape,calleeInitShape,bodyCrepShape,tailCrepShape,compiledEq⟩ :=
    scalarDeclLoop_compiled_shapes calleeContext (ofString name)
      (compileExpExactHOL globals (.const (BitVec.ofNat 64 count)))
      (compileExpExactHOL globals (.var .local (ofString name)))
      (compileProgExactHOL globals (.skip)) (compileProgExactHOL globals (countdownBodyHOL name))
      (compileProgExactHOL globals (.return (.const returned)))
      (globalCompile_scalar_shape globals (.const _)) (globalCompile_branch_shape globals .skip)
      (globalCompile_scalar_shape globals (.local _ _ found)) (globalCompile_branch_shape globals bodyShape)
      (globalCompile_branch_shape globals (.return (.const _)))
  have found' := crepFound
  have run' := crepRun
  simp only [compileProgExactHOL] at found' run' compiledEq
  rw [compiledEq] at found' run'
  obtain ⟨extra,loopPost,entryShape,calleeShape,calleeLookup,loopRun,notError,loopComplete,shiftedRel,postLoopRel,loopBound⟩ :=
    branchTailDecl_riscv_inputs loopCtxt live (newMainNameHOL declarations) crepInit (branch_compile initShape)
      (calleeContext.vmax+1) value valueShape (compileProgExactHOLW inner (compileProgExactHOL globals (.skip)))
      condition (compileProgExactHOLW inner (compileProgExactHOL globals (countdownBodyHOL name)))
      (compileProgExactHOLW inner (compileProgExactHOL globals (.return (.const returned))))
      calleeInitShape conditionShape bodyCrepShape tailCrepShape crep crepMiddle crepPost crepResult target word _
      crepInitRun (by simpa only [compileProgExactHOL] using found') crepClock
      (by simpa only [compileProgExactHOL] using run') complete crepRel memRel globalsRel codeRel localsRel loopWordRel crepBound
  refine ⟨value,condition,extra,loopPost,valueEq,conditionEq,entryShape,calleeShape,calleeLookup,shiftedRel,
    loopRun,notError,loopComplete,postLoopRel,loopBound,?_⟩
  exact tailRiscVReady_of_loop _ loopPost _ _ _ entryShape calleeShape calleeLookup
    loopRun notError shiftedRel loopComplete loopBound

end SteppedFlapjack.PanToCrepSteps
