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

def branchingHOL : ProgHOL 64 := .ite (.const 1) (.return (.const 7)) (.return (.const 9))

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

/-- The exact `6*n+9` count and the matching HOL run use no initialization
hypotheses: the concrete state already satisfies them. -/
theorem countdown_run (n : Nat) (range : n < 2^64)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) Unit) :
    ∃ result final,
      evalPanValueFfiProgSteps context primitive handler (executableState (countdownHOL n)).structs []
        (executableState (countdownHOL n)).baseAddress (executableState (countdownHOL n)).topAddress
        panSemBitVec64BytesInWord (n+4) (executableState (countdownHOL n)).locals
        (executableState (countdownHOL n)).globals (executableState (countdownHOL n)).memory
        (executableState (countdownHOL n)).ffi (countdown n)
        (memoryAccess := some (panSemBitVec64MemoryAccess (executableState (countdownHOL n)))) =
          some (result,6*n+9) ∧
      (exactState (countdownHOL n)).evaluateHOLFiniteState (countdownHOL n) =
        (some (.returned (.val (.word 0))),final) ∧
      controlSteps (countdownHOL n) (exactState (countdownHOL n)) ≤ 6*n+9 ∧
      result = .returned (restorePanValueLocal (fun _ => none) "x"
        ((executableState (countdownHOL n)).locals "x"))
        (executableState (countdownHOL n)).globals (executableState (countdownHOL n)).memory
        (executableState (countdownHOL n)).ffi [.word 0] := by
  have run := counted_decl_countdown_return n (executableState (countdownHOL n)) (exactState (countdownHOL n))
    (source_related _) (source_ranged _) "x" countdown_name_ranged range (by
      change n ≤ 2^64
      omega) 0 (mkCtxtExactHOL HolFiniteMapExact.empty HolFiniteMapExact.empty 0 HolFiniteMapExact.empty) context primitive handler [] 0
  obtain ⟨result,final,exec,hol,bound,_,resultEq⟩ := run
  exact ⟨result,final,by simpa [countdown] using exec,by simpa [countdownHOL] using hol,
    by simpa [countdownHOL] using bound,resultEq⟩

/-- The constant conditional takes its first branch in four counted steps. -/
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
        (executableState branchingHOL).memory (executableState branchingHOL).ffi [.word 7],4) := by
  simp [branching,evalPanValueFfiProgSteps,panValueIteCondition,panValueReturnSteps,evalPanValueExpCounted,
    evalPanValueExp,panValueExpStepCost,executableState,singleEntrySourceProduction]

theorem branching_expressions_ranged :
    ExpByteRanged (.const (1 : BitVec 64)) ∧ ExpByteRanged (.const (7 : BitVec 64)) ∧
      ExpByteRanged (.const (9 : BitVec 64)) := by
  simp [ExpByteRanged]

/-- The HOL source run selects the same branch and has at most four control visits. -/
theorem branching_hol_run :
    (exactState branchingHOL).evaluateHOLFiniteState branchingHOL =
      (some (.returned (.val (.word 7))), (exactState branchingHOL).emptyLocalsHOLFinite) ∧
    controlSteps branchingHOL (exactState branchingHOL) ≤ 4 := by
  constructor
  · rw [branchingHOL,PanSemStateFiniteExact.evaluateHOLFiniteState_ite]
    simp [PanSemStateFiniteExact.evaluateHOLFiniteState_return,
      evalHOLExact,shapeOfHOLExact]
  · simp [branchingHOL,controlSteps.eq_def,evalHOLExact]
    split <;> omega

end SteppedFlapjack.Concrete
