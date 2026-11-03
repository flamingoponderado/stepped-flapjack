import Flapjack.Test.PanValueAcceleratorFfi
import SteppedFlapjack.PanSteppedSemantics

/-!
The stepped evaluator with the accelerator handler of `Flapjack.Test.PanValueAcceleratorFfi`.
Moved from flapjack with the stepped semantics (flapjack#1251).
-/

namespace Flapjack

def acceleratorTestResult :=
  evalPanValueSteppedProg (fun _ _ => none) (fun _ _ _ _ _ locals => some locals)
    [] [] 0 1000 1 20 (fun _ => none) (fun _ => none) (fun _ => none)
    acceleratorTestProgram
    (memoryAccess := some acceleratorTestMemoryAccess)
    (memoryHandler := some acceleratorTestHandler)

#guard
  acceleratorTestResult.map (fun (result, _) => match result with
    | .returned _ _ memory [PanValue.word 0] =>
        match memory 200 with
        | some (.word 8) => true
        | _ => false
    | _ => false) = some true

end Flapjack
