import SteppedFlapjack.PanValueFfiSemantics

/-!
The stepped evaluator with the memory FFI handler of `Flapjack.Test.PanValueMemoryFfi`.
Split from that module (flapjack#1251), with copies of the fixtures it
uses, so that this package does not import Flapjack's tests.
-/

namespace Flapjack

def memoryFfiTestContext : PanValueFfiContext Nat :=
  { sharedDomain := fun _ => true
    byteAlign := id
    bigEndian := false
    wordToBytes := fun _ _ => []
    wordOfBytes := fun _ _ => 0
    wordToByte := fun value => UInt8.ofNat value
    byteToWord := fun value => value.toNat
    valueToNat := id }

def memoryFfiTestState : FfiState Unit :=
  { oracle := fun _ state _ _ => .returned state []
    state := ()
    ioEvents := [] }

def memoryFfiTestHandler : PanValueStatefulFfiHandler Nat Unit :=
  fun _ _ _ _ _ locals ffi => some (locals, ffi)

def memoryFfiTestMemoryAccess : PanValueMemoryAccess Nat :=
  { domain := fun _ => true
    wordOp := fun _ _ => some 0
    compare := fun _ _ _ => 0
    shift := fun _ _ _ => some 0
    readWord := fun domain memory _ address =>
      if domain address then
        match memory address with
        | some (.word value) => some value
        | _ => none
      else none
    readByte := fun _ _ _ _ => none
    read16 := fun _ _ _ _ => none
    read32 := fun _ _ _ _ => none
    storeWord := fun domain memory _ address value =>
      if domain address then some (updatePanValueMemory memory address (.word value))
      else none
    storeByte := fun _ _ _ _ _ => none
    store16 := fun _ _ _ _ _ => none
    store32 := fun _ _ _ _ _ => none
    sharedRead := fun _ _ _ _ => none
    sharedStore := fun _ _ _ _ _ => none }

def memoryFfiAccelerator : PanValueMemoryFfiHandler Nat Unit :=
  fun function configuration _ array _ locals memory ffi =>
    if function == "accelerator" then
      some (locals, updatePanValueMemory memory array (.word (configuration + 1)), ffi)
    else none

def memoryFfiDecliningHandler : PanValueMemoryFfiHandler Nat Unit :=
  fun _ _ _ _ _ _ _ _ => none

def memoryFfiFinalState : FfiState Unit :=
  { oracle := fun _ _ _ _ => .final .failed
    state := ()
    ioEvents := [] }

def memoryFfiInitial : PanValueFfiProgramState Nat Unit :=
  { source :=
      { structs := []
        globals := fun _ => none
        functions := []
        returnShapes := []
        exceptions := []
        memory := fun _ => none
        baseAddress := 0
        topAddress := 1000
        bytesInWord := 1 }
    ffi := memoryFfiTestState }

def memoryFfiMain : Prog Nat :=
  .seq
    (.extCall "accelerator" (.const 7) (.const 0) (.const 200) (.const 1))
    (.return (.load .one (.const 200)))

def memoryFfiFinalMain : Prog Nat :=
  .extCall "unknown" (.const 7) (.const 0) (.const 200) (.const 0)

def memoryFfiDeclarations : List (Decl Nat) :=
  [.function
    { name := "main", inline := false, exported := true, params := [],
      body := memoryFfiMain, returnShape := .one }]

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
