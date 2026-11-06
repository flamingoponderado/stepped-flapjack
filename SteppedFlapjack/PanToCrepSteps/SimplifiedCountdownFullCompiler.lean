import SteppedFlapjack.PanToCrepSteps.DeclWhileSingleEntry
import SteppedFlapjack.PanToCrepSteps.CountedCountdown

/-! Countdown source bound applied to full-initialization RISC-V compilation. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.LabToTargetSteps

/-- A countdown with separately established source budget yields the actual
full-initialization RISC-V bound, including entry-frame failure. -/
theorem counted_simplifiedCountdown_fullCompiler_riscv {σ : Type}
    (declarations : List (DeclHOL 64)) (start : MlString) (initializers : List (ProgHOL 64))
    (globals : PanGlobalsContextExact 64) (caller : PanToCrepContextExact 64)
    (name : VarName)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64)))
    (nameRanged : NameRanged name) (fuel : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source pan middle : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs] (crep : CrepSemHOLState 64 σ)
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (count budget : Nat) (returned : BitVec 64)
    (wordRange : count < 2^64) (sourceClock : count ≤ source.clock)
    (budgetBound : 6*count+7 ≤ budget)
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
    (singleDef : declarations = singleEntryProgram start (.dec (ofString name) .one (.const (BitVec.ofNat 64 count))
      (.seq (.while (.var .local (ofString name)) (.assign .local (ofString name) (.op .sub [.var .local (ofString name),.const 1]))) (.return (.const returned)))))
    (sourceCode : source.code = HolFiniteMapExact.empty.update (newMainNameHOL declarations,
      ([],.dec (ofString name) .one (.const (BitVec.ofNat 64 count)) (.seq (.while (.var .local (ofString name)) (.assign .local (ofString name) (.op .sub [.var .local (ofString name),.const 1])))
        (.return (.const returned))),.one)))
    (panDef : pan = noGlobalsLoweredPreCall source (HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse))
    (middleDef : middle = pan)
    (crepDef : crep = concreteDeclCrepState pan (compileProgDeclsHOLW (compileTopExactHOL declarations start)))
    (targetDef : target = {concreteDeclLoopState arch crep (compileProgDeclsHOLW (compileTopExactHOL declarations start)) with memory := target.memory})
    (memoryRel : crepToLoopMemRelHOLExact crep.memory target.memory crep.memaddrs)
    (native : FullInitAssignLoopInputs declarations start caller loopCtxt (assignLoopEntryProgram declarations initializers caller loopCtxt .ln)
      (declWhileSourceLoopLimit declarations initializers globals caller (ofString name) (.const (BitVec.ofNat 64 count)) (.var .local (ofString name)) (.assign .local (ofString name) (.op .sub [.var .local (ofString name),.const 1])) (.return (.const returned)) budget pan loopCtxt .ln) target) :
    let entry := assignLoopEntryProgram declarations initializers caller loopCtxt .ln
    ∃ originalResult,
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+count+4)
        production.locals production.globals production.memory production.ffi
        (.dec name .one (.const (BitVec.ofNat 64 count)) (.seq .skip
          (.seq (.while (.var .local name) (countdownBody name)) (.return (.const returned)))))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (originalResult,6*count+9) ∧
    ∃ sourceFinal,
      source.evaluateHOLFiniteState (.dec (ofString name) .one (.const (BitVec.ofNat 64 count))
        (.seq .skip (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned))))) =
          (some (.returned (.val (.word returned))),sourceFinal) ∧
      source.evaluateHOLFiniteState (.dec (ofString name) .one (.const (BitVec.ofNat 64 count))
        (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))) =
          (some (.returned (.val (.word returned))),sourceFinal) ∧
    ∃ outcome ticks finalMachine finalFfi,
      ticks ≤ max (native.backend.successTickLimit native.wc native.ac
          (panToWordCompileProgHOL native.arch (singleEntryProgram (ofString "main")
            (.dec (ofString name) .one (.const (BitVec.ofNat 64 count)) (.seq .skip
              (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))))))
          entry (assignLoopEntryWordContext entry) (firstLoopName,2)
          (declWhileSourceLoopLimit declarations initializers globals caller (ofString name) (.const (BitVec.ofNat 64 count)) (.var .local (ofString name)) (.assign .local (ofString name) (.op .sub [.var .local (ofString name),.const 1])) (.return (.const returned)) budget pan loopCtxt .ln)) native.backend.resourceTickLimit ∧
      evaluateTargetHOL native.backend.mc native.backend.lab.ffi ticks native.backend.machine =
          (.halt outcome,finalMachine,finalFfi) ∧
      ((outcome = .success ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents) ∨
          (outcome = .resourceLimitHit ∧
            (finalFfi.ioEvents <+: sourceFinal.ffi.ioEvents ∨ finalFfi.ioEvents = native.stack.ffi.ioEvents))) := by
  obtain ⟨originalResult,originalFinal,originalExec,originalRun,originalBound,originalShape,originalResultEq⟩ :=
    counted_decl_countdown_return count production source rel ranged name nameRanged wordRange sourceClock returned
      (ctxtFcExactHOL caller.funcs caller.eids [] [] []) context primitive handler functions fuel
  obtain ⟨result,sourceFinal,exec,run,bound,resultEq⟩ := counted_decl_countdown_simplified count production source rel ranged
    name nameRanged wordRange sourceClock returned context primitive handler functions fuel
  have sameFinal : originalFinal = sourceFinal := by
    rw [evaluateHOLFiniteState_dec_total] at originalRun run
    simp only [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_skip] at originalRun run
    exact (Prod.mk.inj (originalRun.symm.trans run)).2
  subst originalFinal
  let ctxt := ctxtFcExactHOL caller.funcs caller.eids [] [] []
  have found := scalarDeclContext_local ctxt (ofString name)
  have conditionShape : ScalarExpression (scalarDeclContext ctxt (ofString name)) (.var .local (ofString name)) :=
    .local _ _ found
  have bodyShape : BranchProgram (scalarDeclContext ctxt (ofString name))
      (.assign .local (ofString name) (.op .sub [.var .local (ofString name),.const 1])) :=
    .assign _ _ found (.op .sub (.local _ _ found) (.const _))
  obtain ⟨outcome,ticks,finalMachine,finalFfi,ticksBound,machineRun,events⟩ :=
    declWhile_singleEntry_source_fullInit_riscv declarations start initializers globals caller
      (ofString name) (BitVec.ofNat 64 count) returned (.var .local (ofString name))
      (.op .sub [.var .local (ofString name),.const 1]) source sourceFinal pan middle crep budget
      (by simpa [countdownBodyHOL] using run) (by simpa [countdownBodyHOL] using bound.trans budgetBound)
      conditionShape bodyShape loopCtxt target arch initializersEmpty globalsEmpty sourceLocals sourceGlobals
      sourceExceptions sourceStructs topOutside aligned singleDef sourceCode panDef middleDef crepDef targetDef memoryRel native
  refine ⟨originalResult,originalExec,sourceFinal,originalRun,run,outcome,ticks,finalMachine,finalFfi,?_,machineRun,events⟩
  have compilerEq := singleEntry_countdown_panToWord native.arch (ofString name) (BitVec.ofNat 64 count) returned
  have programEq : loopToWordCompileHOL (compileProgHOLExact native.arch native.crepPrograms) =
      panToWordCompileProgHOL native.arch (singleEntryProgram (ofString "main")
        (.dec (ofString name) .one (.const (BitVec.ofNat 64 count)) (.seq .skip
          (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned)))))) := by
    rw [native.programsEq]
    simpa only [singleDef,startDef,countdownBodyHOL] using compilerEq.symm
  simpa only [programEq] using ticksBound

end SteppedFlapjack.PanToCrepSteps
