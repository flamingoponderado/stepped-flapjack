import SteppedFlapjack.Concrete.SourceState
import SteppedFlapjack.PanToCrepSteps.CountedIte

/-! Exact source runs for the phase-zero witnesses. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.PanSemStateFiniteExact SteppedFlapjack.PanToCrepSteps

/-- Exact-syntax form of the countdown used in the single-function table. -/
def countdownHOL (n : Nat) : ProgHOL 64 :=
  .dec (ofString "x") .one (.const (BitVec.ofNat 64 n))
    (.seq .skip (.seq (.while (.var .local (ofString "x")) (countdownBodyHOL "x")) (.return (.const 0))))

def branchingHOL : ProgHOL 64 := .ite (.cmp .lower (.const 0) (.const 1)) (.return (.const 7)) (.return (.const 9))

theorem countdown_hol_eq (n : Nat) : countdownHOL n = progToHOL (countdown n) := by
  simp [countdownHOL,countdown,countdownBody,countdownBodyHOL,progToHOL,expToHOL,shapeToHOL]

theorem branching_hol_eq : branchingHOL = progToHOL branching := by
  simp [branchingHOL,branching,progToHOL,expToHOL]

theorem countdown_name_ranged : NameRanged "x" := by simp [NameRanged]

theorem countdown_expressions_ranged (n : Nat) :
    ExpByteRanged (.const (BitVec.ofNat 64 n)) ∧
    ExpByteRanged (.var .local "x" : Exp (RiscV.Word 64)) ∧
    ExpByteRanged (.op .sub [.var .local "x",.const 1] : Exp (RiscV.Word 64)) := by
  simp [ExpByteRanged,ListExpByteRanged]

/-- The comparison conditional takes its first branch in six counted steps. -/
theorem branching_run
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    evalPanValueFfiProgSteps context primitive handler (executableState branchingHOL).structs []
      (executableState branchingHOL).baseAddress (executableState branchingHOL).topAddress
      panSemBitVec64BytesInWord 2 (executableState branchingHOL).locals
      (executableState branchingHOL).globals (executableState branchingHOL).memory
      (executableState branchingHOL).ffi branching
      (memoryAccess := some (panSemBitVec64MemoryAccess (executableState branchingHOL))) =
      some (.returned (executableState branchingHOL).locals (executableState branchingHOL).globals
        (executableState branchingHOL).memory (executableState branchingHOL).ffi [.word 7],6) := by
  simp [branching,evalPanValueFfiProgSteps,panValueIteCondition,panValueReturnResult,evalPanValueExpCounted,
    evalPanValueExp,panValueExpStepCost,executableState,singleEntrySourceProduction,
    panSemBitVec64MemoryAccess,panValueMemoryAccessOfModel,panSemBitVec64WordModel,
    panSemWordModel,RiscV.panRiscVMemoryModel,RiscV.panRiscVCmp]

theorem branching_expressions_ranged :
    ExpByteRanged (.cmp .lower (.const 0) (.const 1) : Exp (RiscV.Word 64)) ∧
      ExpByteRanged (.const (7 : BitVec 64)) ∧ ExpByteRanged (.const (9 : BitVec 64)) := by
  simp [ExpByteRanged]

/-- The HOL source run selects the same branch and has at most six control visits. -/
theorem branching_hol_run :
    (exactState branchingHOL).evaluateHOLFiniteState branchingHOL =
      (some (.returned (.val (.word 7))), (exactState branchingHOL).emptyLocalsHOLFinite) ∧
    controlSteps branchingHOL (exactState branchingHOL) ≤ 6 := by
  constructor
  · rw [branchingHOL,PanSemStateFiniteExact.evaluateHOLFiniteState_ite]
    simp [PanSemStateFiniteExact.evaluateHOLFiniteState_return,
      evalHOLExact,shapeOfHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  · simp [branchingHOL,controlSteps.eq_def,evalHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    split <;> omega

end SteppedFlapjack.Concrete
