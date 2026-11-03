import Flapjack.Pancake.Semantics.PanSem
import SteppedFlapjack.Test.PanValueFfiSemantics

/-!
The non-clocked evaluator `evalPanValueFfiProgSteps` on the `ExtCall` failures
of `Flapjack.Test.PanSemExtCallErrorParity`. The `nonClocked*_full` theorems
equate the complete control-result payload with its input values.
Split from that module (flapjack#1251), with copies of the fixtures it
uses, so that this package does not import Flapjack's tests.
-/

namespace Flapjack.Test.PanSemExtCallErrorParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

def extState (clock : Nat) : PanSemState Word64 (FfiState Unit) :=
  { locals := fun name =>
      if name == "x" then some (.word (BitVec.ofNat 64 3))
      else if name == "s" then some (.rStruct [])
      else none
    globals := fun name => if name == "g" then some (.word (BitVec.ofNat 64 4)) else none
    structs := []
    code := []
    exceptionShapes := fun _ => none
    memory := fun _ => some (.word (BitVec.ofNat 64 0))
    memaddrs := fun _ => false
    sharedMemaddrs := fun _ => false
    clock := clock
    be := false
    ffi := statefulTestFfiState
    baseAddress := 0
    topAddress := 100 }

def emptyAccess : PanValueMemoryAccess Word64 :=
  panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel (domain := fun _ => false)

/-- With an empty read domain every byte read fails, so reading `n + 1` bytes
    yields `none`. -/
theorem emptyRead_succ (context : PanValueFfiContext Word64)
    (memory : Word64 → Option (PanValue Word64)) (n : Nat) (address : Word64) :
    panValueFfiReadBytes emptyAccess context memory (BitVec.ofNat 64 8) address (n + 1) = none := by
  simp [panValueFfiReadBytes, emptyAccess, panValueMemoryAccessOfModel, panModelReadByte,
    panRiscVMemoryModel, panRiscVByteAlign]

theorem emptyRead_one (context : PanValueFfiContext Word64)
    (memory : Word64 → Option (PanValue Word64)) (address : Word64) :
    panValueFfiReadBytes emptyAccess context memory (BitVec.ofNat 64 8) address 1 = none :=
  emptyRead_succ context memory 0 address

def nonwordProgram : Prog Word64 :=
  .extCall "f" (.var .local "s") (.const 0) (.const 0) (.const 0)

def readFailProgram : Prog Word64 :=
  .extCall "f" (.const 0) (.const 1) (.const 0) (.const 0)

/-- An `ExtCall` whose first argument expression fails to evaluate (unbound
    local).  HOL returns `(SOME Error, s)`; the production evaluator must not
    collapse this to the fuel-exhaustion `none`. -/
def argFailProgram : Prog Word64 :=
  .extCall "f" (.var .local "missing") (.const 0) (.const 0) (.const 0)

def nonClockedEvaluate (program : Prog Word64)
    (memoryAccess : Option (PanValueMemoryAccess Word64) := none) :
    Option (PanValueFfiSteppedResult Word64 Unit) :=
  evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive statefulTestHandler
    [] [] 0 100 (BitVec.ofNat 64 8) 5 (extState 5).locals (extState 5).globals
    (extState 5).memory statefulTestFfiState program (memoryAccess := memoryAccess)

private def isWord (expected : Nat) : Option (PanValue Word64) → Bool
  | some (.word value) => value == BitVec.ofNat 64 expected
  | _ => false

theorem nonClockedNonword_full :
    (nonClockedEvaluate nonwordProgram).map Prod.fst =
      some (.error (extState 5).locals (extState 5).globals (extState 5).memory
        statefulTestFfiState) := by
  simp (config := { decide := true }) [nonClockedEvaluate, evalPanValueFfiProgramSteps,
    evalPanValueFfiProgSteps, panValueFfiExtCallSteps, evalPanValueExpsCounted,
    evalPanValueExps, evalPanValueExp.evalPanValueExps, evalPanValueExp, extState,
    nonwordProgram]

theorem nonClockedReadFail_full :
    (nonClockedEvaluate readFailProgram (some emptyAccess)).map Prod.fst =
      some (.error (extState 5).locals (extState 5).globals (extState 5).memory
        statefulTestFfiState) := by
  simp (config := { decide := true }) [nonClockedEvaluate, evalPanValueFfiProgramSteps,
    evalPanValueFfiProgSteps, panValueFfiExtCallSteps, evalPanValueExpsCounted,
    evalPanValueExps, evalPanValueExp.evalPanValueExps, evalPanValueExp, extState,
    readFailProgram, panValueFfiExtCall, emptyRead_one, statefulTestContext]

theorem nonClockedArgFail_full :
    (nonClockedEvaluate argFailProgram).map Prod.fst =
      some (.error (extState 5).locals (extState 5).globals (extState 5).memory
        statefulTestFfiState) := by
  simp (config := { decide := true }) [nonClockedEvaluate, evalPanValueFfiProgramSteps,
    evalPanValueFfiProgSteps, panValueFfiExtCallSteps, evalPanValueExpsCounted,
    evalPanValueExps, evalPanValueExp.evalPanValueExps, evalPanValueExp, extState,
    argFailProgram]

private def ffiObservable (ffi : FfiState Unit) : Bool :=
  ffi.state == () && decide (ffi.ioEvents = ([] : List FfiEvent))

private def isErrorSteppedPreserving
    (result : Option (PanValueFfiSteppedResult Word64 Unit)) : Bool :=
  match result with
  | some (.error locals globals memory ffi, _) =>
      isWord 3 (locals "x") && isWord 4 (globals "g") && isWord 0 (memory 0)
        && ffiObservable ffi
  | _ => false

def nonClockedNonwordGuard : Bool :=
  isErrorSteppedPreserving (nonClockedEvaluate nonwordProgram)

def nonClockedReadFailGuard : Bool :=
  isErrorSteppedPreserving (nonClockedEvaluate readFailProgram (some emptyAccess))

def nonClockedArgFailGuard : Bool :=
  isErrorSteppedPreserving (nonClockedEvaluate argFailProgram)

#guard nonClockedNonwordGuard
#guard nonClockedReadFailGuard
#guard nonClockedArgFailGuard

end Flapjack.Test.PanSemExtCallErrorParity
