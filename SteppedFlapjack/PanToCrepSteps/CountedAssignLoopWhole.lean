import SteppedFlapjack.PanToCrepSteps.CountedAssignLoopNative

/-! Invert whole-program counted runs to their assignment-loop execution. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.LabToTargetSteps

/-- A local-assignment loop can only finish normally or with an error, and it
preserves globals, memory and FFI state in either case. -/
theorem counted_assignLoop_result_shape {σ : Type}
    (condition assignment : Exp (RiscV.Word 64)) (name : VarName)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) :
    ∀ (fuel : Nat) (production : PanSemState (RiscV.Word 64) (FfiState σ))
      (result : PanValueFfiControlResult (RiscV.Word 64) σ) (cost : Nat),
      evalPanValueFfiProgSteps context primitive handler production.structs functions
        production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
        production.locals production.globals production.memory production.ffi (.while condition (.assign .local name assignment))
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,cost) →
      ∃ locals, result = .normal locals production.globals production.memory production.ffi ∨
        result = .error locals production.globals production.memory production.ffi := by
  intro fuel
  induction fuel with
  | zero =>
    intro production result cost run
    simp [evalPanValueFfiProgSteps] at run
  | succ fuel ih =>
    intro production result cost run
    rw [evalPanValueFfiProgSteps,counted_condition_eq] at run
    cases conditionRun : evalPanSemStateExp production condition with
    | none => simp [conditionRun] at run; cases run.1; exact ⟨_,Or.inr rfl⟩
    | some conditionValue =>
      cases conditionValue with
      | word word =>
        simp only [conditionRun,Option.elim_some] at run
        by_cases zero : word = 0
        · subst word
          simp at run
          cases run.1
          exact ⟨_,Or.inl rfl⟩
        · simp only [beq_iff_eq,if_neg zero] at run
          cases fuel with
          | zero => simp [evalPanValueFfiProgSteps] at run
          | succ fuel =>
            have counted : evalPanValueExpCounted production.structs production.locals production.globals production.memory
                production.baseAddress production.topAddress panSemBitVec64BytesInWord assignment
                (some (panSemBitVec64MemoryAccess production)) =
                (evalPanSemStateExp production assignment).map (fun value => (value,panValueExpStepCost assignment)) := by
              simp [evalPanValueExpCounted,evalPanSemStateExp_64_eq_previous]
            cases assigned : evalPanSemStateExp production assignment with
            | none =>
              have body : evalPanValueFfiProgSteps context primitive handler production.structs functions
                  production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
                  production.locals production.globals production.memory production.ffi (.assign .local name assignment)
                  (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
                    some (.error production.locals production.globals production.memory production.ffi,0) := by
                simp [evalPanValueFfiProgSteps,panValueAssignLocalResult,counted,assigned]
              simp [body] at run
              cases run.1
              exact ⟨_,Or.inr rfl⟩
            | some value =>
              cases valid : panValueAssignmentValid production.structs production.locals production.globals .local name value with
              | false =>
                have body : evalPanValueFfiProgSteps context primitive handler production.structs functions
                    production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
                    production.locals production.globals production.memory production.ffi (.assign .local name assignment)
                    (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
                      some (.error production.locals production.globals production.memory production.ffi,panValueExpStepCost assignment+1) := by
                  simp [evalPanValueFfiProgSteps,panValueAssignLocalResult,counted,assigned,valid]
                simp [body] at run
                cases run.1
                exact ⟨_,Or.inr rfl⟩
              | true =>
                have body : evalPanValueFfiProgSteps context primitive handler production.structs functions
                    production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
                    production.locals production.globals production.memory production.ffi (.assign .local name assignment)
                    (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
                      some (.normal (updatePanValueMap production.locals name value) production.globals production.memory production.ffi,
                        panValueExpStepCost assignment+1) := by
                  simp [evalPanValueFfiProgSteps,panValueAssignLocalResult,counted,assigned,valid]
                simp only [body] at run
                let next := {production with locals := updatePanValueMap production.locals name value}
                cases rest : evalPanValueFfiProgSteps context primitive handler production.structs functions
                    production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
                    (updatePanValueMap production.locals name value) production.globals production.memory production.ffi
                    (.while condition (.assign .local name assignment))
                    (memoryAccess := some (panSemBitVec64MemoryAccess production)) with
                | none => simp [rest] at run
                | some pair =>
                  rcases pair with ⟨restResult,restCost⟩
                  simp [rest] at run
                  have resultEq := run.1
                  subst result
                  exact ih next restResult restCost (by simpa [next,panSemBitVec64MemoryAccess] using rest)
      | _ => simp [conditionRun] at run; cases run.1; exact ⟨_,Or.inr rfl⟩

/-- A successful counted run of the whole generated source body exposes its
normal inner-loop run, and the wrapper contributes exactly five steps. -/
theorem counted_assignLoop_whole_invert {σ : Type}
    (condition assignment : Exp (RiscV.Word 64)) (name : VarName) (returned : BitVec 64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat)
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (cost : Nat)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+3)
      production.locals production.globals production.memory production.ffi
      (.seq .skip (.seq (.while condition (.assign .local name assignment)) (.return (.const returned))))
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.returned (fun _ => none) production.globals production.memory production.ffi [.word returned],cost)) :
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
      simp [loopRun,evalPanValueFfiProgSteps,panValueReturnResult,
        evalPanValueExpCounted,evalPanValueExp,panValuePayloadWithinLimit,
        panValuePayloadSizeFuel,panValueExpStepCost] at run
      exact ⟨locals,loopCost,rfl,by omega⟩
    · subst loopResult
      simp [loopRun] at run

end SteppedFlapjack.PanToCrepSteps
