import SteppedFlapjack.PanValueFfiFuel
import SteppedFlapjack.Test.PanValueMemoryFfi

namespace Flapjack

/-! A successful stepped stateful-FFI run can be reused at a larger fuel. -/

example {result : PanValueFfiSteppedResult Nat Unit}
    (hrun : evalPanValueFfiProgramStepped memoryFfiTestContext memoryFfiInitial
      (fun _ _ => none) memoryFfiTestHandler 20 memoryFfiDeclarations "main" []
      (memoryAccess := some memoryFfiTestMemoryAccess)
      (memoryHandler := some memoryFfiAccelerator) = some result) :
    evalPanValueFfiProgramStepped memoryFfiTestContext memoryFfiInitial
      (fun _ _ => none) memoryFfiTestHandler 30 memoryFfiDeclarations "main" []
      (memoryAccess := some memoryFfiTestMemoryAccess)
      (memoryHandler := some memoryFfiAccelerator) = some result := by
  exact StepCalculus.evalPanValueFfiProgramStepped_fuel_mono
    memoryFfiTestContext memoryFfiInitial (fun _ _ => none) memoryFfiTestHandler
    (hfuel := by decide) memoryFfiDeclarations "main" []
    (ma := some memoryFfiTestMemoryAccess)
    (mh := some memoryFfiAccelerator) hrun

end Flapjack
