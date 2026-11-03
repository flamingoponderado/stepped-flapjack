import SteppedFlapjack.PanSteppedSemantics
namespace Flapjack

def steppedTestLocals : VarName → Option (PanValue Nat) := fun name =>
  if name == "x" then some (.word 0) else none
def steppedTestGlobals : VarName → Option (PanValue Nat) := fun _ => none
def steppedTestMemory : Nat → Option (PanValue Nat) := fun _ => none

def steppedTestPrimitive : PanPrimitiveHandler Nat := fun _ _ => none
def steppedTestFfi : PanValueFfiHandler Nat := fun _ _ _ _ _ locals => some locals

def steppedReturnedValues : PanValueControlResult Nat → List Nat
  | .returned _ _ _ values => values.map (fun value => match value with
      | .word value => value
      | _ => 0)
  | _ => []

def steppedTestProgram : Prog Nat :=
  .seq
    (.assign .local "x" (.const 7))
    (.seq (.while (.const 0) .skip) (.return (.var .local "x")))

def steppedStructuredStoreLoadProgram : Prog Nat :=
  .seq
    (.store (.const 10) (.rStruct [.const 3, .const 5]))
    (.return (.load (.comb [.one, .one]) (.const 10)))

#guard
  (evalPanValueSteppedProg steppedTestPrimitive steppedTestFfi [] [] 0 100 1 20
    (fun _ => none) (fun _ => none) (fun _ => none)
    steppedStructuredStoreLoadProgram).map
      (fun (result, steps) => match result with
        | .returned _ _ memory [PanValue.rStruct [PanValue.word 3, PanValue.word 5]] =>
            steps == 9 &&
              (match memory 10 with
                | some (.word 3) => true
                | _ => false) &&
              (match memory 11 with
                | some (.word 5) => true
                | _ => false)
        | _ => false) = some true

#guard
  (evalPanValueSteppedProg steppedTestPrimitive steppedTestFfi [] [] 0 100 1 8
    steppedTestLocals steppedTestGlobals steppedTestMemory steppedTestProgram).map Prod.snd =
    some 8

#guard
  (evalPanValueSteppedProg steppedTestPrimitive steppedTestFfi [] [] 0 100 1 8
    steppedTestLocals steppedTestGlobals steppedTestMemory
    (.assign .local "x" (.rStruct []))).isNone

#guard
  (evalPanValueSteppedProg steppedTestPrimitive steppedTestFfi [] [] 0 100 1 8
    (fun _ => none) steppedTestGlobals steppedTestMemory
    (.assign .local "missing" (.const 7))).isNone

#guard
  (evalPanValueSteppedProg steppedTestPrimitive steppedTestFfi [] [] 0 100 1 8
    steppedTestLocals steppedTestGlobals steppedTestMemory steppedTestProgram).map
      (fun (result, _) => steppedReturnedValues result) =
    (evalPanValueProgWithPrimitiveCallsAndFfi steppedTestPrimitive steppedTestFfi [] []
      0 100 1 20 steppedTestLocals steppedTestGlobals steppedTestMemory
      steppedTestProgram).map steppedReturnedValues

def steppedTestFunctions : List (FunName × List VarName × Prog Nat) :=
  [("id", ["x"], .return (.var .local "x"))]

/- A callee whose return payload exceeds the CakeML 32-word limit is rejected
   by the callee `Return`, so the enclosing call still fails even though the
   Call itself now checks only the return shape (as in HOL). -/
def steppedOversizedReturn : Prog Nat :=
  .return (.rStruct (List.replicate 33 (.const 0)))

#guard
  (evalPanValueSteppedProg steppedTestPrimitive steppedTestFfi []
    [("big", [], steppedOversizedReturn)] 0 100 1 20
    steppedTestLocals steppedTestGlobals steppedTestMemory
    (.call none "big" [])).isNone

def steppedRaiseFunctions : List (FunName × List VarName × Prog Nat) :=
  [("raise", [], .raise "E" (.const 9))]

#guard
  (evalPanValueSteppedProg steppedTestPrimitive steppedTestFfi [] steppedRaiseFunctions
    0 100 1 20 (fun _ => none) (fun _ => none) (fun _ => none)
    (.decCall "result" .one "raise" [] (.return (.const 0)))).map
      (fun (result, _) => match result with
        | .raised _ _ _ exception (.word value) => exception == "E" && value == 9
        | _ => false) = some true

def steppedStateFunctions : List (FunName × List VarName × Prog Nat) :=
  [("setGlobal", [], .seq (.assign .global "g" (.const 7)) (.return (.const 1)))]

def steppedStateGlobals : VarName → Option (PanValue Nat) := fun name =>
  if name == "g" then some (.word 0) else none

#guard
  (evalPanValueExpCounted [] steppedTestLocals steppedTestGlobals steppedTestMemory
    0 100 1 (.op .add [.const 1, .const 2])).map Prod.snd = some 3

example :
    ((some 7 : Option Nat).map (fun value => (value, 3))).bind
        (fun pair => (some (pair.1 + pair.2, 0) : Option (Nat × Nat)).map Prod.fst) =
      (some 7 : Option Nat).bind (fun value => some (value + 3)) := by
  exact panOptionCountedBindMapFst (values := some 7) (steps := 3)
    (stepped := fun value _ => some (value + 3, 0))
    (original := fun value => some (value + 3)) (by
      intro value step
      simp)

example :
    (evalPanValueExpCounted [] steppedTestLocals steppedTestGlobals steppedTestMemory
      0 100 1 (.op .add [.const 1, .const 2])).bind
        (fun pair => (some (pair.1, pair.2) : Option (PanValue Nat × Nat)).map Prod.fst) =
      (evalPanValueExp [] steppedTestLocals steppedTestGlobals steppedTestMemory
        0 100 1 (.op .add [.const 1, .const 2])).bind (fun value => some value) := by
  simpa using (panEvalPanValueExpCountedBindMapFst
    (structs := []) (locals := steppedTestLocals) (globals := steppedTestGlobals)
    (memory := steppedTestMemory) (baseAddress := 0) (topAddress := 100)
    (bytesInWord := 1) (expression := .op .add [.const 1, .const 2])
    (stepped := fun value step => some (value, step))
    (original := fun value => some value) (by
      intro value step
      simp))

example :
    (evalPanValueExpCounted [] steppedTestLocals steppedTestGlobals steppedTestMemory
      0 100 1 (.op .add [.const 1, .const 2])).map Prod.snd =
      (evalPanValueExp [] steppedTestLocals steppedTestGlobals steppedTestMemory
        0 100 1 (.op .add [.const 1, .const 2])).map
        (fun _ => panValueExpStepCost (.op .add [.const 1, .const 2])) := by
  exact evalPanValueExpCounted_snd [] steppedTestLocals steppedTestGlobals
    steppedTestMemory 0 100 1 (.op .add [.const 1, .const 2])

#guard
  (evalPanValueSteppedProg steppedTestPrimitive steppedTestFfi [] steppedTestFunctions
    0 100 1 8 steppedTestLocals steppedTestGlobals steppedTestMemory
    (.call none "id" [.const 41])).map Prod.snd = some 4

#guard
  (evalPanValueSteppedProg steppedTestPrimitive steppedTestFfi [] steppedTestFunctions
    0 100 1 8 steppedTestLocals steppedTestGlobals steppedTestMemory
    (.call (some (none, none)) "id" [.const 41])).map Prod.snd = some 4

#guard
  (evalPanValueSteppedProg steppedTestPrimitive steppedTestFfi [] steppedTestFunctions
    0 100 1 8 steppedTestLocals steppedTestGlobals steppedTestMemory
    (.call none "id" [.const 41])).map
      (fun (result, _) => steppedReturnedValues result) =
    (evalPanValueProgWithPrimitiveCallsAndFfi steppedTestPrimitive steppedTestFfi []
      steppedTestFunctions 0 100 1 20 steppedTestLocals steppedTestGlobals
      steppedTestMemory (.call none "id" [.const 41])).map steppedReturnedValues

#guard
      (evalPanValueSteppedProg steppedTestPrimitive steppedTestFfi [] steppedStateFunctions
    0 100 1 8 (fun _ => none) steppedStateGlobals steppedTestMemory
    (.call none "setGlobal" [])).map
      (fun (result, _) => match result with
        | .returned _ globals _ _ => match globals "g" with
          | some (.word 7) => true
          | _ => false
        | _ => false) == some true

example :
    (evalPanValueProgWithPrimitiveCallsAndFfiSteps steppedTestPrimitive steppedTestFfi [] []
      0 100 1 8 steppedTestLocals steppedTestGlobals steppedTestMemory
      steppedTestProgram).map Prod.fst =
      evalPanValueProgWithPrimitiveCallsAndFfi steppedTestPrimitive steppedTestFfi [] []
        0 100 1 8 steppedTestLocals steppedTestGlobals steppedTestMemory
        steppedTestProgram := by
  apply evalPanValueProgWithPrimitiveCallsAndFfiSteps_fst

def steppedTestInitial : PanValueProgramState Nat :=
  { structs := []
    globals := steppedTestGlobals
    functions := []
    returnShapes := []
    exceptions := []
    memory := steppedTestMemory
    baseAddress := 0
    topAddress := 100
    bytesInWord := 8 }

#guard
  (evalPanValueSteppedProgram steppedTestInitial steppedTestPrimitive steppedTestFfi 20
    [.function
      { name := "id", inline := false, exported := true,
        params := [("x", .one)], body := .return (.var .local "x"),
        returnShape := .one }]
    "id" [.const 41]).map Prod.snd = some 4

#guard
  (evalPanValueSteppedProgram steppedTestInitial steppedTestPrimitive steppedTestFfi 30
    [.function
      { name := "badReturn", inline := false, exported := false, params := [],
        body := .return (.rStruct [.const 1, .const 2]), returnShape := .one },
     .function
      { name := "main", inline := false, exported := true, params := [],
        body := .seq (.call none "badReturn" []) (.return (.const 0)),
        returnShape := .one }]
    "main" []).isNone = true

end Flapjack
