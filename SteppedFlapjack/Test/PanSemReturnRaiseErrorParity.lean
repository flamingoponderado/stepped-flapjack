import Flapjack.Pancake.Semantics.PanSem
import SteppedFlapjack.Test.PanValueFfiSemantics

/-!
The non-clocked step evaluator `evalPanValueFfiProgSteps` on the `Return` and
`Raise` fixtures of `Flapjack.Test.PanSemReturnRaiseErrorParity`. It reaches
the same `panValueReturnResult`/`panValueRaiseResult` helpers as the clocked
evaluator; these guards check the carried state.
Split from that module (flapjack#1251), with copies of the fixtures it
uses, so that this package does not import Flapjack's tests.
-/

namespace Flapjack.Test.PanSemReturnRaiseErrorParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

def returnRaiseState (clock : Nat) : PanSemState Word64 (FfiState Unit) :=
  { locals := fun name =>
      if name == "x" then some (.word (BitVec.ofNat 64 3)) else none
    globals := fun _ => none
    structs := []
    code := []
    exceptionShapes := fun _ => none
    memory := fun _ => none
    memaddrs := fun _ => false
    sharedMemaddrs := fun _ => false
    clock := clock
    be := false
    ffi := statefulTestFfiState
    baseAddress := BitVec.ofNat 64 0
    topAddress := BitVec.ofNat 64 100 }

def contractsWith (exceptionShapes : InfoMap Shape) : PanValueCallContracts :=
  { returnShapes := [], exceptionShapes := exceptionShapes }

def isWordOption (expected : Nat) (value : Option (PanValue Word64)) : Bool :=
  match value with
  | some (.word word) => word == BitVec.ofNat 64 expected
  | _ => false

def isMissingLocal (value : Option (PanValue Word64)) : Bool := value.isNone

def isWordValue (expected : Nat) (value : PanValue Word64) : Bool :=
  match value with
  | .word word => word == BitVec.ofNat 64 expected
  | _ => false

def isWordList (expected : Nat) : List (PanValue Word64) → Bool
  | [.word word] => word == BitVec.ofNat 64 expected
  | _ => false

def retEvalFail : Prog Word64 := .return (.var .local "z")

def retOversized : Prog Word64 := .return (.rStruct (List.replicate 33 (.const 0)))

def retOk : Prog Word64 := .return (.const (BitVec.ofNat 64 7))

def raiseMissingShape : Prog Word64 := .raise "E" (.const (BitVec.ofNat 64 7))

def raiseMismatch : Prog Word64 := .raise "E" (.rStruct [.const (BitVec.ofNat 64 7)])

def raiseEvalFail : Prog Word64 := .raise "E" (.var .local "z")

def raiseOversized : Prog Word64 :=
  .raise "E" (.rStruct (List.replicate 33 (.const 0)))

def oneExceptionContracts : Option PanValueCallContracts :=
  some (contractsWith [("E", .one)])

def oversizedExceptionContracts : Option PanValueCallContracts :=
  some (contractsWith [("E", .comb (List.replicate 33 .one))])

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
