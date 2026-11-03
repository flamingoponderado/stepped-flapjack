import Flapjack.Test.PanSemReturnRaiseErrorParity
import SteppedFlapjack.PanValueFfiSemantics

/-!
The non-clocked step evaluator `evalPanValueFfiProgSteps` on the `Return` and
`Raise` fixtures of `Flapjack.Test.PanSemReturnRaiseErrorParity`. It reaches
the same `panValueReturnResult`/`panValueRaiseResult` helpers as the clocked
evaluator; these guards check the carried state.
Moved from flapjack with the stepped semantics (flapjack#1251).
-/

namespace Flapjack.Test.PanSemReturnRaiseErrorParity

open Flapjack
open Flapjack.RiscV

def nonClockedEvaluate (program : Prog Word64)
    (contracts : Option PanValueCallContracts := none) :
    Option (PanValueFfiSteppedResult Word64 Unit) :=
  evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive statefulTestHandler
    [] [] (BitVec.ofNat 64 0) (BitVec.ofNat 64 100) (BitVec.ofNat 64 8) 5
    (returnRaiseState 5).locals (returnRaiseState 5).globals (returnRaiseState 5).memory
    statefulTestFfiState program (contracts := contracts)

/-- Check the oracle fixture's local, representative global/memory lookups, and
    FFI observation. This is a regression guard, not a full-state equality proof. -/
def errorSteppedPreserving (result : Option (PanValueFfiSteppedResult Word64 Unit)) : Bool :=
  match result with
  | some (.error locals globals memory ffi, _) =>
      isWordOption 3 (locals "x") && (globals "g").isNone && (globals "x").isNone &&
        (memory 0).isNone && (memory 8).isNone &&
        ffi.state == () && decide (ffi.ioEvents = ([] : List FfiEvent))
  | _ => false

def returnedSteppedCleared (expected : Nat)
    (result : Option (PanValueFfiSteppedResult Word64 Unit)) : Bool :=
  match result with
  | some (.returned locals _ _ _ values, _) =>
      isMissingLocal (locals "x") && isWordList expected values
  | _ => false

def raisedSteppedCleared (exceptionId : String) (expected : Nat)
    (result : Option (PanValueFfiSteppedResult Word64 Unit)) : Bool :=
  match result with
  | some (.raised locals _ _ _ exception value, _) =>
      isMissingLocal (locals "x") && exception == exceptionId && isWordValue expected value
  | _ => false

def retEvalFailNonClockedGuard : Bool := errorSteppedPreserving (nonClockedEvaluate retEvalFail)

def retOversizedNonClockedGuard : Bool := errorSteppedPreserving (nonClockedEvaluate retOversized)

def retOkNonClockedGuard : Bool := returnedSteppedCleared 7 (nonClockedEvaluate retOk)

def raiseMissingShapeNonClockedGuard : Bool :=
  errorSteppedPreserving (nonClockedEvaluate raiseMissingShape (some (contractsWith [])))

def raiseMismatchNonClockedGuard : Bool :=
  errorSteppedPreserving (nonClockedEvaluate raiseMismatch oneExceptionContracts)

def raiseEvalFailNonClockedGuard : Bool :=
  errorSteppedPreserving (nonClockedEvaluate raiseEvalFail oneExceptionContracts)

def raiseOversizedNonClockedGuard : Bool :=
  errorSteppedPreserving (nonClockedEvaluate raiseOversized oversizedExceptionContracts)

def raiseOkNonClockedGuard : Bool :=
  raisedSteppedCleared "E" 7
    (nonClockedEvaluate (.raise "E" (.const (BitVec.ofNat 64 7))) oneExceptionContracts)

def returnRaiseNonClockedGuard : Bool :=
  retEvalFailNonClockedGuard && retOversizedNonClockedGuard && retOkNonClockedGuard &&
    raiseMissingShapeNonClockedGuard && raiseMismatchNonClockedGuard &&
    raiseEvalFailNonClockedGuard && raiseOversizedNonClockedGuard && raiseOkNonClockedGuard

#guard returnRaiseNonClockedGuard

end Flapjack.Test.PanSemReturnRaiseErrorParity
