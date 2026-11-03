import SteppedFlapjack.PanSteppedSemantics

/-!
The stepped evaluator with the accelerator handler of `Flapjack.Test.PanValueAcceleratorFfi`.
Split from that module (flapjack#1251), with copies of the fixtures it
uses, so that this package does not import Flapjack's tests.
-/

namespace Flapjack

def acceleratorTestMemoryAccess : PanValueMemoryAccess Nat :=
  { domain := fun _ => true
    wordOp := fun _ _ => some 0
    compare := fun _ _ _ => 0
    shift := fun _ _ _ => some 0
    readWord := fun _ _ _ _ => none
    readByte := fun _ _ _ _ => none
    read16 := fun _ _ _ _ => none
    read32 := fun _ _ _ _ => none
    storeWord := fun _ _ _ _ _ => none
    storeByte := fun _ _ _ _ _ => none
    store16 := fun _ _ _ _ _ => none
    store32 := fun _ _ _ _ _ => none
    sharedRead := fun _ _ _ _ => none
    sharedStore := fun _ _ _ _ _ => none }

def acceleratorTestHandler : PanValueAcceleratorFfiHandler Nat :=
  fun function configuration _ array _ locals memory =>
    if function == "accelerator" then
      some (locals, updatePanValueMemory memory array (.word (configuration + 1)))
    else none

def acceleratorTestProgram : Prog Nat :=
  .seq
    (.extCall "accelerator" (.const 7) (.const 0) (.const 200) (.const 1))
    (.return (.const 0))

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
