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

end SteppedFlapjack.PanToCrepSteps
