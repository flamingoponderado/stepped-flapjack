import Flapjack.Test.PanSemExtCallErrorParity
import SteppedFlapjack.PanValueFfiSemantics

/-!
The non-clocked evaluator `evalPanValueFfiProgSteps` on the `ExtCall` failures
of `Flapjack.Test.PanSemExtCallErrorParity`. The `nonClocked*_full` theorems
equate the complete control-result payload with its input values.
Moved from flapjack with the stepped semantics (flapjack#1251).
-/

namespace Flapjack.Test.PanSemExtCallErrorParity

open Flapjack
open Flapjack.RiscV

def nonClockedEvaluate (program : Prog Word64)
    (memoryAccess : Option (PanValueMemoryAccess Word64) := none) :
    Option (PanValueFfiSteppedResult Word64 Unit) :=
  evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive statefulTestHandler
    [] [] 0 100 (BitVec.ofNat 64 8) 5 (extState 5).locals (extState 5).globals
    (extState 5).memory statefulTestFfiState program (memoryAccess := memoryAccess)

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
