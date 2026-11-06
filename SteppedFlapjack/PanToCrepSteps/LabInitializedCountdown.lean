import SteppedFlapjack.PanToCrepSteps.SourceFullInitInputs
import SteppedFlapjack.PanToCrepSteps.CountedCountdown

/-! Counted source execution for the Lab-derived initial source. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open SteppedFlapjack.LoopToWordSteps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit

/-- The Lab-derived production and HOL source entries execute a finite
countdown with the independently established exact source cost. -/
theorem labInitialized_countdown {σ : Type} (count : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (template : PanSemStateFiniteExact 64 σ)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ)
    (backend : FullInitMachineContext stack)
    (environment : PanSemEnvironmentRel production template)
    (ranged : PanSemStateRelExecRanged production)
    (ffiRel : FfiStateRel production.ffi backend.lab.ffi)
    (name : VarName) (nameRanged : NameRanged name) (wordRange : count < 2^64)
    (clock : count ≤ backend.lab.clock - 1) (returned : BitVec 64)
    (ctxt : PanToCrepContextExact 64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat) :
    let prod := labInitializedProduction production template stack backend
    let source := labInitializedOriginal template stack backend
    let program : Prog (RiscV.Word 64) := .dec name .one (.const (BitVec.ofNat 64 count))
      (.seq .skip (.seq (.while (.var .local name) (countdownBody name)) (.return (.const returned))))
    let holProgram : ProgHOL 64 := .dec (ofString name) .one (.const (BitVec.ofNat 64 count))
      (.seq .skip (.seq (.while (.var .local (ofString name)) (countdownBodyHOL name)) (.return (.const returned))))
    ∃ result final,
      evalPanValueFfiProgSteps context primitive handler prod.structs functions
        prod.baseAddress prod.topAddress panSemBitVec64BytesInWord (fuel+count+4)
        prod.locals prod.globals prod.memory prod.ffi program
        (memoryAccess := some (panSemBitVec64MemoryAccess prod)) = some (result,6*count+9) ∧
      source.evaluateHOLFiniteState holProgram = (some (.returned (.val (.word returned))),final) ∧
      controlSteps holProgram source ≤ 6*count+9 ∧
      SteppedFlapjack.CrepToLoopSteps.SupportedCodeBody (compileProgExactHOLW ctxt holProgram) := by
  classical
  have rel := labInitializedProduction_rel production template stack backend environment ffiRel
  have ran := labInitializedProduction_ranged production template stack backend ranged
  have hclock : count ≤ (labInitializedOriginal template stack backend).clock := by
    simpa [labInitializedOriginal] using clock
  obtain ⟨result,final,exec,run,bound,shape,_⟩ := counted_decl_countdown_return count
    (labInitializedProduction production template stack backend) (labInitializedOriginal template stack backend)
    rel ran name nameRanged wordRange hclock returned ctxt context primitive handler functions fuel
  exact ⟨result,final,exec,run,bound,shape⟩

/-- A clock-zero initializer can support any finite countdown by choosing
the source proof clock, without changing its machine state. -/
theorem labInitialized_countdown_withClock {σ : Type} (count : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (template : PanSemStateFiniteExact 64 σ)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config σ)
    (backend : FullInitMachineContext stack)
    (environment : PanSemEnvironmentRel production template)
    (ranged : PanSemStateRelExecRanged production)
    (ffiRel : FfiStateRel production.ffi backend.lab.ffi)
    (name : VarName) (nameRanged : NameRanged name) (wordRange : count < 2^64)
    (returned : BitVec 64) (ctxt : PanToCrepContextExact 64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat) :
    let adjustedStack := (fullMakeInit backend.stackConf backend.dataConf backend.maxHeap backend.sp backend.offset
      backend.bitmaps backend.inputCode {backend.lab with clock := count+1} backend.saveRegs backend.dataSp backend.coracle).1
    let adjusted := backend.withClock (count+1)
    let prod := labInitializedProduction production template adjustedStack adjusted
    let source := labInitializedOriginal template adjustedStack adjusted
    let program : Prog (RiscV.Word 64) := .dec name .one (.const (BitVec.ofNat 64 count))
      (.seq .skip (.seq (.while (.var .local name) (countdownBody name)) (.return (.const returned))))
    ∃ result,
      evalPanValueFfiProgSteps context primitive handler prod.structs functions
        prod.baseAddress prod.topAddress panSemBitVec64BytesInWord (fuel+count+4)
        prod.locals prod.globals prod.memory prod.ffi program
        (memoryAccess := some (panSemBitVec64MemoryAccess prod)) = some (result,6*count+9) ∧
      source.clock = count ∧ adjusted.machine = backend.machine := by
  classical
  let adjusted := backend.withClock (count+1)
  have h := labInitialized_countdown count production template _ adjusted environment ranged
    (by simpa [adjusted,FullInitMachineContext.withClock] using ffiRel)
    name nameRanged wordRange (by simp [adjusted,FullInitMachineContext.withClock])
    returned ctxt context primitive handler functions fuel
  obtain ⟨result,_,exec,_,_,_⟩ := h
  refine ⟨result,exec,?_,rfl⟩
  simp [labInitializedOriginal,labInitializedSource,FullInitMachineContext.withClock]

end SteppedFlapjack.PanToCrepSteps
