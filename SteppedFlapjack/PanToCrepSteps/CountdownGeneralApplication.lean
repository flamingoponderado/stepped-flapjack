import SteppedFlapjack.PanToCrepSteps.LabInitializedCountdown
import SteppedFlapjack.PanToCrepSteps.LabCountedFullCompiler

/-! Full-initialization RISC-V bound for the Lab-derived countdown source. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.LabToTargetSteps

/-- Apply the general source-budget theorem to the independently counted countdown,
choosing a proof clock without changing the concrete machine. -/
theorem labInitialized_countdown_fromGeneral_withClock_riscv {σ : Type}
    (declarations : List (DeclHOL 64)) (start : MlString)
    (caller : PanToCrepContextExact 64) (loopCtxt : CrepToLoopContextExact)
    (arch : AsmArchitecture) (name : VarName) (count budget : Nat) (returned : BitVec 64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (template : PanSemStateFiniteExact 64 σ)
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ) (backend : FullInitMachineContext stack)
    (cfg : LabToTarget.Config)
    (environment : PanSemEnvironmentRel production template)
    (ranged : PanSemStateRelExecRanged production) (ffiRel : FfiStateRel production.ffi backend.lab.ffi)
    (nameRanged : NameRanged name) (wordRange : count < 2^64)
    (budgetBound : 6*count+9 ≤ budget)
    (templateLocals : template.locals = HolFiniteMapExact.empty)
    (templateGlobals : template.globals = HolFiniteMapExact.empty)
    (templateExceptions : template.eshapes = HolFiniteMapExact.empty)
    (templateStructs : template.structs = [])
    (startDef : start = ofString "main")
    (singleDef : declarations = singleEntryProgram start (.dec (ofString name) .one (.const (BitVec.ofNat 64 count))
      (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))))
    (sourceCode : template.code = HolFiniteMapExact.empty.update (newMainNameHOL declarations,
      ([],.dec (ofString name) .one (.const (BitVec.ofNat 64 count))
        (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned))),.one)))
    (callerEq : caller = mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
      (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start))) (sizeOfShapeHOL (.comb [])-1)
      (getEidsFromDeclsHOL (compileTopExactHOL declarations start)))
    (loopContextEq : loopCtxt = mkCtxtExact arch (makeVmapExact [])
      (crepToLoopMakeFuncsExactExecutable (compileProgDeclsHOLW (compileTopExactHOL declarations start))) 0)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (programsEq : programs = (compile wc ac (panToWordCompileProgHOL arch
      (singleEntryProgram (ofString "main") (.dec (ofString name) .one (.const (BitVec.ofNat 64 count))
        (.seq .skip (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))))))).2)
    (inputCodeEq : backend.inputCode = (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false programs).2.2.2)
    (bitmapPrefix : (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false programs).1.IsPrefix backend.bitmaps)
    (registers : 4 < ac.regCount-(5+ac.avoidRegs.length))
    (stackOracle : backend.coracle = fun _ => (cfg, [], []))
    (wordMemory : ∀ address, (labInitializedOriginal template stack backend).memaddrs address →
      ∃ word, backend.lab.memory address = .word word) :
    let adjustedStack := (fullMakeInit backend.stackConf backend.dataConf backend.maxHeap backend.sp backend.offset
      backend.bitmaps backend.inputCode {backend.lab with clock := budget+1} backend.saveRegs backend.dataSp backend.coracle).1
    let adjusted := backend.withClock (budget+1)
    let source := labInitializedOriginal template adjustedStack adjusted
    let prod := labInitializedProduction production template stack backend
    let pan := noGlobalsLoweredPreCall source (HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse)
    let entry := assignLoopEntryProgram declarations [] caller loopCtxt .ln
    let limit := declWhileSourceLoopLimit declarations [] emptyGlobalsContext caller (ofString name)
      (.const (BitVec.ofNat 64 count)) (.var .local (ofString name)) (countdownBodyHOL name)
      (.return (.const returned)) budget pan loopCtxt .ln
    ∃ sourceResult,
      evalPanValueFfiProgSteps context primitive handler prod.structs functions
        prod.baseAddress prod.topAddress panSemBitVec64BytesInWord (fuel+count+4)
        prod.locals prod.globals prod.memory prod.ffi
        (.dec name .one (.const (BitVec.ofNat 64 count)) (.seq .skip (.seq
          (.while (.var .local name) (countdownBody name)) (.return (.const returned)))))
        (memoryAccess := some (panSemBitVec64MemoryAccess prod)) = some (sourceResult,6*count+9) ∧
    ∃ sourceFinal,
      source.evaluateHOLFiniteState (.dec (ofString name) .one (.const (BitVec.ofNat 64 count)) (.seq .skip (.seq
        (.while (expToHOL (.var .local name : Exp (RiscV.Word 64))) (.assign .local (ofString name)
          (expToHOL (.op .sub [.var .local name,.const 1] : Exp (RiscV.Word 64))))) (.return (.const returned))))) =
        (some (.returned (.val (.word returned))),sourceFinal) ∧
      ∃ outcome ticks finalMachine finalFfi,
        ticks ≤ max (adjusted.successTickLimit wc ac
          (panToWordCompileProgHOL arch (singleEntryProgram (ofString "main")
            (.dec (ofString name) .one (.const (BitVec.ofNat 64 count)) (.seq .skip
              (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))))))
          entry (assignLoopEntryWordContext entry) (firstLoopName,2) limit) adjusted.resourceTickLimit ∧
        evaluateTargetHOL backend.mc backend.lab.ffi ticks backend.machine = (.halt outcome,finalMachine,finalFfi) ∧
        ((outcome = .success ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents) ∨
          (outcome = .resourceLimitHit ∧
            (finalFfi.ioEvents <+: sourceFinal.ffi.ioEvents ∨ finalFfi.ioEvents = adjustedStack.ffi.ioEvents))) := by
  classical
  let adjusted := backend.withClock (budget+1)
  let prod := labInitializedProduction production template stack backend
  let shiftedProd := labInitializedProduction production template _ adjusted
  let shiftedSource := labInitializedOriginal template _ adjusted
  have rel := labInitializedProduction_rel production template _ adjusted environment
    (by simpa [adjusted,FullInitMachineContext.withClock] using ffiRel)
  have ran := labInitializedProduction_ranged production template _ adjusted ranged
  have enough : count ≤ shiftedSource.clock := by
    simp [shiftedSource,labInitializedOriginal,labInitializedSource,adjusted,FullInitMachineContext.withClock]
    omega
  obtain ⟨sourceResult,sourceFinal,shiftedExec,_,_,_,resultEq⟩ := counted_decl_countdown_return count
    shiftedProd shiftedSource rel ran name nameRanged wordRange enough returned
    (ctxtFcExactHOL caller.funcs caller.eids [] [] []) context primitive handler functions fuel
  have exec : evalPanValueFfiProgSteps context primitive handler prod.structs functions
      prod.baseAddress prod.topAddress panSemBitVec64BytesInWord (fuel+count+4)
      prod.locals prod.globals prod.memory prod.ffi
      (.dec name .one (.const (BitVec.ofNat 64 count)) (.seq .skip (.seq
        (.while (.var .local name) (countdownBody name)) (.return (.const returned)))))
      (memoryAccess := some (panSemBitVec64MemoryAccess prod)) = some (sourceResult,6*count+9) := by
    simpa only [prod,shiftedProd,adjusted,labInitializedProduction_counted_withClock] using shiftedExec
  have resultEq' : sourceResult = .returned (restorePanValueLocal (fun _ => none) name (prod.locals name))
      prod.globals prod.memory prod.ffi [.word returned] := by
    simpa [shiftedProd,adjusted,labInitializedProduction_withClock,prod] using resultEq
  let ctxt := ctxtFcExactHOL caller.funcs caller.eids [] [] []
  have found := scalarDeclContext_local ctxt (ofString name)
  have conditionShape : ScalarExpression (scalarDeclContext ctxt (ofString name)) (expToHOL (.var .local name : Exp (RiscV.Word 64))) := by
    simpa [expToHOL] using (ScalarExpression.local _ _ found)
  have bodyShape : BranchProgram (scalarDeclContext ctxt (ofString name))
      (.assign .local (ofString name) (expToHOL (.op .sub [.var .local name,.const 1] : Exp (RiscV.Word 64)))) := by
    simpa [expToHOL] using (BranchProgram.assign _ _ found (.op .sub (.local _ _ found) (.const _)))
  have result := labInitialized_counted_declared_fullCompiler_withClock_riscv declarations start caller loopCtxt arch
    name (BitVec.ofNat 64 count) returned (.var .local name) (.op .sub [.var .local name,.const 1]) (6*count+9) budget
    context primitive handler functions (fuel+count) production template wc ac stack backend cfg environment ranged ffiRel
    nameRanged (by simpa [ExpByteRanged] using nameRanged) (by simpa [ExpByteRanged,ListExpByteRanged] using nameRanged)
    budgetBound (restorePanValueLocal (fun _ => none) name (prod.locals name)) prod.globals prod.memory prod.ffi [.word returned]
    (by rw [← resultEq']; simpa [prod,countdownBody] using exec) conditionShape bodyShape templateLocals templateGlobals
    templateExceptions templateStructs startDef (by simpa [expToHOL,countdownBodyHOL] using singleDef)
    (by simpa [expToHOL,countdownBodyHOL] using sourceCode) callerEq loopContextEq programs
    (by simpa [expToHOL,countdownBodyHOL] using programsEq) inputCodeEq bitmapPrefix registers stackOracle wordMemory
  refine ⟨sourceResult,exec,?_⟩
  simpa [expToHOL,countdownBodyHOL] using result

end SteppedFlapjack.PanToCrepSteps
