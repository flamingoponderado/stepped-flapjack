import SteppedFlapjack.PanToCrepSteps.CountedSingleEntryFullInit
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
theorem counted_singleEntry_countdown_fullInit_riscv {σ : Type}
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
    (budgetBound : 6*count+9 ≤ budget)
    (loopCtxt : CrepToLoopContextExact) (target : LoopSemStateFiniteExact 64 σ)
    (arch : AsmArchitecture)
    (initializersEmpty : initializers = []) (globalsEmpty : globals = emptyGlobalsContext)
    (sourceLocals : source.locals = HolFiniteMapExact.empty)
    (sourceGlobals : source.globals = HolFiniteMapExact.empty)
    (sourceExceptions : source.eshapes = HolFiniteMapExact.empty)
    (sourceStructs : source.structs = [])
    (topOutside : ¬ source.memaddrs source.topAddr)
    (aligned : panGlobalsByteAlignedHOL source.topAddr)
    (singleDef : declarations = singleEntryProgram start (.dec (ofString name) .one (.const (BitVec.ofNat 64 count)) (.seq .skip (.seq
        (.while (expToHOL (.var .local name : Exp (RiscV.Word 64))) (.assign .local (ofString name) (expToHOL (.op .sub [.var .local name,.const 1] : Exp (RiscV.Word 64))))) (.return (.const returned))))))
    (sourceCode : source.code = HolFiniteMapExact.empty.update
      (newMainNameHOL declarations,([],(.dec (ofString name) .one (.const (BitVec.ofNat 64 count)) (.seq .skip (.seq
        (.while (expToHOL (.var .local name : Exp (RiscV.Word 64))) (.assign .local (ofString name) (expToHOL (.op .sub [.var .local name,.const 1] : Exp (RiscV.Word 64))))) (.return (.const returned))))),.one)))
    (panDef : pan = noGlobalsLoweredPreCall source (HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL declarations start)).reverse))
    (middleDef : middle = pan)
    (crepDef : crep = concreteDeclCrepState pan (compileProgDeclsHOLW (compileTopExactHOL declarations start)))
    (targetDef : target = {concreteDeclLoopState arch crep (compileProgDeclsHOLW (compileTopExactHOL declarations start)) with memory := target.memory})
    (memoryRel : crepToLoopMemRelHOLExact crep.memory target.memory crep.memaddrs)
    (native : FullInitAssignLoopInputs declarations start caller loopCtxt (assignLoopEntryProgram declarations initializers caller loopCtxt .ln)
      (declaredAssignLoopLimit declarations initializers globals caller (.var .local name : Exp (RiscV.Word 64)) (.op .sub [.var .local name,.const 1] : Exp (RiscV.Word 64)) name (BitVec.ofNat 64 count) returned pan budget loopCtxt .ln) target) :
    let entry := assignLoopEntryProgram declarations initializers caller loopCtxt .ln
    ∃ sourceFinal,
      source.evaluateHOLFiniteState (.dec (ofString name) .one (.const (BitVec.ofNat 64 count)) (.seq .skip (.seq (.while (expToHOL (.var .local name : Exp (RiscV.Word 64)))
        (.assign .local (ofString name) (expToHOL (.op .sub [.var .local name,.const 1] : Exp (RiscV.Word 64))))) (.return (.const returned))))) =
          (some (.returned (.val (.word returned))),sourceFinal) ∧
      ∃ outcome ticks finalMachine finalFfi,
        ticks ≤ max (native.backend.successTickLimit native.wc native.ac
          (loopToWordCompileHOL (compileProgHOLExact native.arch native.crepPrograms))
          entry (assignLoopEntryWordContext entry) (firstLoopName,2)
          (declaredAssignLoopLimit declarations initializers globals caller (.var .local name : Exp (RiscV.Word 64)) (.op .sub [.var .local name,.const 1] : Exp (RiscV.Word 64)) name (BitVec.ofNat 64 count) returned pan budget loopCtxt .ln)) native.backend.resourceTickLimit ∧
        evaluateTargetHOL native.backend.mc native.backend.lab.ffi ticks native.backend.machine =
          (.halt outcome,finalMachine,finalFfi) ∧
        ((outcome = .success ∧ finalFfi.ioEvents = sourceFinal.ffi.ioEvents) ∨
          (outcome = .resourceLimitHit ∧
            (finalFfi.ioEvents <+: sourceFinal.ffi.ioEvents ∨ finalFfi.ioEvents = native.stack.ffi.ioEvents))) := by
  let ctxt := ctxtFcExactHOL caller.funcs caller.eids [] [] []
  obtain ⟨result,final,exec,_,_,_,resultEq⟩ := counted_decl_countdown_return count production source rel ranged
    name nameRanged wordRange sourceClock returned ctxt context primitive handler functions fuel
  rw [resultEq] at exec
  have clock : 6*count+9 ≤ source.clock*(panValueExpStepCost (.var .local name : Exp (RiscV.Word 64)) +
      panValueExpStepCost (.op .sub [.var .local name,.const 1] : Exp (RiscV.Word 64))+2) +
      (panValueExpStepCost (.var .local name : Exp (RiscV.Word 64))+1)+7 := by
    simp [panValueExpStepCost,panValueExpStepCost.panValueExpsStepCost]
    omega
  have found := scalarDeclContext_local ctxt (ofString name)
  have conditionShape : ScalarExpression (scalarDeclContext ctxt (ofString name)) (expToHOL (.var .local name : Exp (RiscV.Word 64))) := by
    simpa [expToHOL] using (ScalarExpression.local _ _ found)
  have bodyShape : BranchProgram (scalarDeclContext ctxt (ofString name))
      (.assign .local (ofString name) (expToHOL (.op .sub [.var .local name,.const 1] : Exp (RiscV.Word 64)))) := by
    simpa [expToHOL] using (BranchProgram.assign _ _ found (.op .sub (.local _ _ found) (.const _)))
  exact counted_singleEntry_declared_fullInit_riscv declarations start initializers globals caller
    (.var .local name) (.op .sub [.var .local name,.const 1]) name (BitVec.ofNat 64 count)
    context primitive handler functions (by simpa [ExpByteRanged] using nameRanged)
    (by simpa [ExpByteRanged,ListExpByteRanged] using nameRanged) nameRanged (fuel+count)
    production source pan middle crep rel ranged (6*count+9) budget returned clock budgetBound
    (restorePanValueLocal (fun _ => none) name (production.locals name)) production.globals production.memory production.ffi
    [.word returned] (by simpa [countdownBody] using exec) conditionShape bodyShape loopCtxt target arch
    initializersEmpty globalsEmpty sourceLocals sourceGlobals sourceExceptions sourceStructs topOutside aligned singleDef sourceCode
    panDef middleDef crepDef targetDef memoryRel native

end SteppedFlapjack.PanToCrepSteps
