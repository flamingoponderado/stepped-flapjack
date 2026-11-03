import SteppedFlapjack.PanCost

namespace Flapjack

def panCostTestPrimitive : PanPrimitiveHandler Nat := fun _ _ => none
def panCostTestFfi : PanValueFfiHandler Nat := fun _ _ _ _ _ locals => some locals
def panCostTestMemory : Nat → Option (PanValue Nat) := fun _ => none

def panCostSharedLoadMemory : Nat → Option (PanValue Nat)
  | 8 => some (.word 9)
  | _ => none

#guard
  (evalPanValueCostProg panCostTestPrimitive panCostTestFfi [] [] 0 100 1 20
    (fun _ => none) (fun _ => none) panCostTestMemory
    (.seq
      (.store (.const 10) (.rStruct [.const 3, .const 5]))
      (.return (.load (.comb [.one, .one]) (.const 10))))).map
      (fun (result, cost) => match result with
        | .returned _ _ _ [PanValue.rStruct [PanValue.word 3, PanValue.word 5]] =>
            cost.steps == 9 && cost.maxCallDepth == 0 && cost.maxStoreAddress == some 11
        | _ => false) = some true

def panCostTestFunctions : List (FunName × List VarName × Prog Nat) :=
  [("id", ["x"], .return (.var .local "x"))]

#guard
  (evalPanValueCostProg panCostTestPrimitive panCostTestFfi [] panCostTestFunctions
    0 100 1 20 (fun _ => none) (fun _ => none) panCostTestMemory
    (.call none "id" [.const 41])).map
      (fun (result, cost) => match result with
        | .returned _ _ _ [PanValue.word 41] =>
            cost.steps == 4 && cost.maxCallDepth == 1 && cost.maxStoreAddress.isNone
        | _ => false) = some true

def panCostReturned41 : PanValueControlResult Nat → Bool
  | .returned _ _ _ [PanValue.word 41] => true
  | _ => false

#guard
  (evalPanValueCostProg panCostTestPrimitive panCostTestFfi [] panCostTestFunctions
    0 100 1 20 (fun _ => none) (fun _ => none) panCostTestMemory
    (.call none "id" [.const 41])).map (fun (result, _) => panCostReturned41 result) =
  (evalPanValueProgWithPrimitiveCallsAndFfi panCostTestPrimitive panCostTestFfi []
    panCostTestFunctions 0 100 1 20 (fun _ => none) (fun _ => none) panCostTestMemory
    (.call none "id" [.const 41])).map panCostReturned41

/- A callee whose return payload exceeds the CakeML 32-word limit is rejected
   by the callee `Return`, so the enclosing call still fails even though the
   Call itself now checks only the return shape (as in HOL). -/
def panCostOversizedReturn : Prog Nat :=
  .return (.rStruct (List.replicate 33 (.const 0)))

#guard
  (evalPanValueCostProg panCostTestPrimitive panCostTestFfi []
    [("big", [], panCostOversizedReturn)] 0 100 1 20 (fun _ => none) (fun _ => none)
    panCostTestMemory (.call none "big" [])).isNone

#guard
  (evalPanValueProgWithPrimitiveCallsAndFfi panCostTestPrimitive panCostTestFfi []
    [("big", [], panCostOversizedReturn)] 0 100 1 20 (fun _ => none) (fun _ => none)
    panCostTestMemory (.call none "big" [])).isNone

/- CakeML turns all non-returning terminal results from an ordinary callee into
   an error, including the callee's normal, break, and continue results. -/
#guard
  (evalPanValueCostProg panCostTestPrimitive panCostTestFfi []
    [("normal", [], .skip)] 0 100 1 20 (fun _ => none) (fun _ => none)
    panCostTestMemory (.call none "normal" [])).isNone

#guard
  (evalPanValueCostProg panCostTestPrimitive panCostTestFfi []
    [("break", [], .break)] 0 100 1 20 (fun _ => none) (fun _ => none)
    panCostTestMemory (.call none "break" [])).isNone

#guard
  (evalPanValueCostProg panCostTestPrimitive panCostTestFfi []
    [("continue", [], .continue)] 0 100 1 20 (fun _ => none) (fun _ => none)
    panCostTestMemory (.call none "continue" [])).isNone

/- A shared load is an assignment to an existing word destination, including
   in the cost-instrumented evaluator. -/
#guard
  (evalPanValueCostProg panCostTestPrimitive panCostTestFfi [] []
    0 100 1 20 (fun _ => none) (fun _ => none) panCostSharedLoadMemory
    (.shMemLoad .opW .local "missing" (.const 8))).isNone

end Flapjack
