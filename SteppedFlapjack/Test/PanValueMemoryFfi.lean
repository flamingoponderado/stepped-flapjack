import Flapjack.Test.PanValueMemoryFfi
import SteppedFlapjack.PanValueFfiSemantics

/-!
The stepped evaluator with the memory FFI handler of `Flapjack.Test.PanValueMemoryFfi`.
Moved from flapjack with the stepped semantics (flapjack#1251).
-/

namespace Flapjack

def memoryFfiSteppedResult :=
  evalPanValueFfiProgramStepped memoryFfiTestContext memoryFfiInitial
    (fun _ _ => none) memoryFfiTestHandler 20 memoryFfiDeclarations "main" []
    (memoryAccess := some memoryFfiTestMemoryAccess)
    (memoryHandler := some memoryFfiAccelerator)

def memoryFfiResultHasWrite : Bool :=
  match memoryFfiSteppedResult with
  | some (.returned _ _ memory _ [.word value], _) =>
      value == 8 && match memory 200 with
        | some (.word stored) => stored == 8
        | _ => false
  | _ => false

#guard memoryFfiResultHasWrite

theorem memoryFfiStepped_projects_to_nonstepped :
    memoryFfiSteppedResult.map Prod.fst =
      evalPanValueFfiProgram memoryFfiTestContext memoryFfiInitial
        (fun _ _ => none) memoryFfiTestHandler 20 memoryFfiDeclarations "main" []
        (memoryAccess := some memoryFfiTestMemoryAccess)
        (memoryHandler := some memoryFfiAccelerator) := by
  exact evalPanValueFfiProgramStepped_fst memoryFfiTestContext memoryFfiInitial
    (fun _ _ => none) memoryFfiTestHandler 20 memoryFfiDeclarations "main" []
    (memoryAccess := some memoryFfiTestMemoryAccess)
    (memoryHandler := some memoryFfiAccelerator)

theorem memoryFfi_dispatch_contract :
    evalPanValueFfiProgSteps memoryFfiTestContext
      (fun _ _ => none) memoryFfiTestHandler [] [] 0 1000 1 20
      (fun _ => none) (fun _ => none) memoryFfiInitial.source.memory
      memoryFfiTestState
      (.extCall "accelerator" (.const 7) (.const 0) (.const 200) (.const 1))
      (memoryAccess := some memoryFfiTestMemoryAccess)
      (contracts := none)
      (memoryHandler := some memoryFfiAccelerator) =
      some (.normal (fun _ => none) (fun _ => none)
        (updatePanValueMemory memoryFfiInitial.source.memory 200 (.word 8))
        memoryFfiTestState, 5) := by
  exact evalPanValueFfiProgSteps_extCall_memoryHandler
    memoryFfiTestContext (fun _ _ => none) memoryFfiTestHandler [] []
    0 1000 1 19 (fun _ => none) (fun _ => none)
    memoryFfiInitial.source.memory memoryFfiTestState "accelerator"
    7 0 200 1 (some memoryFfiTestMemoryAccess) none memoryFfiAccelerator
    (fun _ => none)
    (updatePanValueMemory memoryFfiInitial.source.memory 200 (.word 8))
    memoryFfiTestState 4
    (by simp [evalPanValueExpsCounted, evalPanValueExps,
      evalPanValueExp.evalPanValueExps, evalPanValueExp,
      panValueExpsStepCost, panValueExpStepCost,
      panValueExpStepCost.panValueExpsStepCost]) (by rfl)

def memoryFfiDecliningFinalResult :=
  evalPanValueFfiProgSteps memoryFfiTestContext
    (fun _ _ => none) memoryFfiTestHandler [] [] 0 1000 1 10
    (fun _ => none) (fun _ => none) memoryFfiInitial.source.memory
    memoryFfiFinalState
    memoryFfiFinalMain
    (memoryAccess := some memoryFfiTestMemoryAccess)
    (memoryHandler := some memoryFfiDecliningHandler)

def memoryFfiDecliningFinalIsReachable : Bool :=
  match memoryFfiDecliningFinalResult with
  | some (.finalFfi locals _ memory ffi event, steps) =>
      locals "x" = none && memory 200 = none && ffi.state = () &&
        event.name = .extCall "unknown" && event.outcome = .failed && steps = 5
  | _ => false

#guard memoryFfiDecliningFinalIsReachable

end Flapjack
