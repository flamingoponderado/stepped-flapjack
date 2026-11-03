import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Pancake.Semantics.PanSemStateEval
import SteppedFlapjack.Test.PanValueFfiSemantics

/-!
The non-clocked Call evaluator receives declaration-derived returnShapes
through PanValueCallContracts. A malformed callee return must produce Error
with the callee post-state, matching the direct HOL malformed-return oracle.
Split from `Flapjack.Test.PanEvaluateParity` (flapjack#1251), with copies of the
fixtures it uses, so that this package does not import Flapjack's tests.
-/

namespace Flapjack.Test.PanEvaluateParity

open Flapjack
open Flapjack.RiscV

def nonClockedBadReturnFunctions :
    List (FunName × List VarName × Prog (Word 64)) :=
  [("badret", ["x"], .return (.const (BitVec.ofNat 64 7)))]

def nonClockedBadReturnContracts : PanValueCallContracts :=
  PanValueCallContracts.mk
    [("badret", .comb [.one, .one])] []
    [("badret", [("x", .one)])]

def evaluateNonClockedCallBadReturnShape :=
  evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive
    statefulTestHandler [] nonClockedBadReturnFunctions
    (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 8
    (fun _ => none) (fun _ => none) (fun _ => none) statefulTestFfiState
    (.call none "badret" [.const (BitVec.ofNat 64 4)] : Prog (Word 64))
    (contracts := some nonClockedBadReturnContracts)

def observeNonClockedCallBadReturnShape : Bool :=
  match evaluateNonClockedCallBadReturnShape with
  | some (.error locals _ _ _, _) =>
      (locals "x").isNone
  | _ => false

#guard observeNonClockedCallBadReturnShape

end Flapjack.Test.PanEvaluateParity
