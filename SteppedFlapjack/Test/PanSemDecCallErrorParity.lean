import Flapjack.Test.PanSemDecCallErrorParity
import SteppedFlapjack.PanValueFfiSemantics

/-!
The non-clocked `evalPanValueFfiProgramSteps` step evaluator on the `DecCall`
cases of `Flapjack.Test.PanSemDecCallErrorParity`: shape mismatch, callee
Error, callee `Skip`/`Break`/`Continue`, missing function and failing argument.
Moved from flapjack with the stepped semantics (flapjack#1251).
-/

namespace Flapjack.Test.PanSemDecCallErrorParity

open Flapjack
open Flapjack.RiscV

def nestedBadShapeNonClockedFunctions : List (FunName × List VarName × Prog Word64) :=
  [("bad", ["p"], .decCall "p" .one "id" [] (.return (.var .local "p"))),
    ("id", [], .return (.const (BitVec.ofNat 64 7)))]

def nestedBadShapeNonClockedResult : Option (PanValueFfiSteppedResult Word64 Unit) :=
  evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive statefulTestHandler
    [] nestedBadShapeNonClockedFunctions (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
    (BitVec.ofNat 64 8) 10 (fun _ => none) (fun _ => none) (fun _ => none)
    statefulTestFfiState nestedBadShapeProgram

/- Exact result and step count for the nonclocked step evaluator. -/
set_option linter.unusedSimpArgs false in
theorem nestedBadShapeNonClockedExact : nestedBadShapeNonClockedResult = some
    (.error nestedBadShapeLocals (fun _ => none) (fun _ => none)
      statefulTestFfiState, 7) := by
  simp (config := { decide := true }) [nestedBadShapeNonClockedResult,
    evalPanValueFfiProgramSteps, evalPanValueFfiProgSteps,
    evalPanValueFfiCallSteps, evalPanValueExpCounted, evalPanValueExpsCounted,
    panValueReturnSteps, panValuePayloadWithinLimit, panValueExpStepCost,
    panValueExpsStepCost,
    updatePanValueMap, restorePanValueLocal, restorePanValueFfiLocal,
    panValueCallArguments, panValueCallTarget, panValueReturnValid, panValueShape,
    nestedBadShapeBindParameters, emptyPanValueBindParameters,
    bindPanValueParameters, lookupPanFunction,
    panShapeMatches, evalPanValueExps, evalPanValueExp.evalPanValueExps,
    evalPanValueExp, nestedBadShapeNonClockedFunctions, nestedBadShapeProgram,
    nestedBadShapeLocals]
  all_goals first
    | simp [panValueExpStepCost.panValueExpsStepCost, panValueExpStepCost]
    | (funext key; simp [nestedBadShapeLocals, restorePanValueLocal,
        updatePanValueMap, beq_iff_eq])

def nestedBadShapeNonClockedGuard : Bool :=
  match nestedBadShapeNonClockedResult with
  | some (.error locals _ _ _, _) => isWord 42 (locals "p")
  | _ => false


/-- The non-clocked step evaluator driven with an explicit callee list. -/
def nonClockedFunctions (code : Prog Word64) :
    List (FunName × List VarName × Prog Word64) :=
  [("f", [], code)]

def nonClockedEvaluate (code : Prog Word64) (program : Prog Word64) :
    Option (PanValueFfiSteppedResult Word64 Unit) :=
  evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive statefulTestHandler
    [] (nonClockedFunctions code) (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
    (BitVec.ofNat 64 8) 3 (fun _ => none) (fun _ => none) (fun _ => none)
    statefulTestFfiState program

def nonClockedIsError (code : Prog Word64) (program : Prog Word64) : Bool :=
  match nonClockedEvaluate code program with
  | some (.error _ _ _ _, _) => true
  | _ => false

def deccallNonClockedShapeGuard : Bool := nonClockedIsError calleeBody deccallShapeProgram
def deccallNonClockedErrorGuard : Bool := nonClockedIsError calleeErrorBody deccallOkProgram
def nonClockedFunctionsNamed (name : FunName) (code : Prog Word64) :
    List (FunName × List VarName × Prog Word64) :=
  [(name, [], code)]

def nonClockedEvaluateNamed (name : FunName) (code : Prog Word64) (program : Prog Word64) :
    Option (PanValueFfiSteppedResult Word64 Unit) :=
  evalPanValueFfiProgramSteps statefulTestContext statefulTestPrimitive statefulTestHandler
    [] (nonClockedFunctionsNamed name code) (BitVec.ofNat 64 0) (BitVec.ofNat 64 100)
    (BitVec.ofNat 64 8) 3 (fun _ => none) (fun _ => none) (fun _ => none)
    statefulTestFfiState program

def nonClockedIsErrorNamed (name : FunName) (code : Prog Word64)
    (program : Prog Word64) : Bool :=
  match nonClockedEvaluateNamed name code program with
  | some (.error _ _ _ _, _) => true
  | _ => false

def deccallNcMissingGuard : Bool :=
  nonClockedIsErrorNamed "missing" .skip (deccallNamedProgram "missing")
def deccallNcSkipGuard : Bool :=
  nonClockedIsErrorNamed "s" .skip (deccallNamedProgram "s")
def deccallNcBreakGuard : Bool :=
  nonClockedIsErrorNamed "b" .break (deccallNamedProgram "b")
def deccallNcContinueGuard : Bool :=
  nonClockedIsErrorNamed "c" .continue (deccallNamedProgram "c")

def deccallNcArgFailGuard : Bool :=
  nonClockedIsErrorNamed "f" calleeBody (deccallArgFailProgram "f")
def deccallNcArgFailMissingGuard : Bool :=
  nonClockedIsErrorNamed "missing" .skip (deccallArgFailProgram "missing")

#guard deccallNonClockedShapeGuard
#guard deccallNonClockedErrorGuard
#guard deccallNcMissingGuard
#guard deccallNcSkipGuard
#guard deccallNcBreakGuard
#guard deccallNcContinueGuard
#guard deccallNcArgFailGuard
#guard deccallNcArgFailMissingGuard

#guard nestedBadShapeNonClockedGuard

end Flapjack.Test.PanSemDecCallErrorParity
