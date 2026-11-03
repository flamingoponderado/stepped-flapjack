import Flapjack.Test.PanEvaluateParity
import SteppedFlapjack.PanValueFfiSemantics

/-!
The non-clocked Call evaluator receives declaration-derived returnShapes
through PanValueCallContracts. A malformed callee return must produce Error
with the callee post-state, matching the direct HOL malformed-return oracle.
Moved from flapjack with the stepped semantics (flapjack#1251).
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
