import SteppedFlapjack.PanToCrepSteps.ControlSteps
import SteppedFlapjack.PanValueFfiSemantics

/-! Compositional counted-sequence rules for executable and HOL semantics. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang

/-- If the first statement completes normally, the actual sequence evaluates
the second statement and counts one sequence node. The child bounds compose
for arbitrary child syntax and results. -/
theorem counted_seq_normal {σ : Type}
    (context : PanValueFfiContext (BitVec 64)) (primitive : PanPrimitiveHandler (BitVec 64))
    (handler : PanValueStatefulFfiHandler (BitVec 64) σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog (BitVec 64)))
    (base top bytes : BitVec 64) (fuel : Nat)
    (locals globals : VarName → Option (PanValue (BitVec 64)))
    (memory : BitVec 64 → Option (PanValue (BitVec 64))) (ffi : FfiState σ)
    (localsPost globalsPost : VarName → Option (PanValue (BitVec 64)))
    (memoryPost : BitVec 64 → Option (PanValue (BitVec 64))) (ffiPost : FfiState σ)
    (first second : Prog (BitVec 64)) (firstHOL secondHOL : ProgHOL 64)
    (access : Option (PanValueMemoryAccess (BitVec 64))) (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler (BitVec 64) σ))
    (result : PanValueFfiControlResult (BitVec 64) σ) (firstCost secondCost : Nat)
    (source middle final : PanSemStateFiniteExact 64 σ) (holResult : Option (PanSemResultExact 64))
    (firstExec : evalPanValueFfiProgSteps context primitive handler structs functions base top bytes fuel
      locals globals memory ffi first (memoryAccess := access) (contracts := contracts) (memoryHandler := memoryHandler) =
        some (.normal localsPost globalsPost memoryPost ffiPost,firstCost))
    (secondExec : evalPanValueFfiProgSteps context primitive handler structs functions base top bytes fuel
      localsPost globalsPost memoryPost ffiPost second (memoryAccess := access) (contracts := contracts) (memoryHandler := memoryHandler) =
        some (result,secondCost))
    (firstRun : source.evaluateHOLFiniteState firstHOL = (none,middle))
    (secondRun : middle.evaluateHOLFiniteState secondHOL = (holResult,final))
    (firstBound : controlSteps firstHOL source ≤ firstCost)
    (secondBound : controlSteps secondHOL middle ≤ secondCost) :
    evalPanValueFfiProgSteps context primitive handler structs functions base top bytes (fuel+1)
      locals globals memory ffi (.seq first second) (memoryAccess := access) (contracts := contracts) (memoryHandler := memoryHandler) =
        some (result,firstCost+secondCost+1) ∧
    source.evaluateHOLFiniteState (.seq firstHOL secondHOL) = (holResult,final) ∧
    controlSteps (.seq firstHOL secondHOL) source ≤ firstCost+secondCost+1 := by
  constructor
  · rw [evalPanValueFfiProgSteps]
    simp [firstExec,secondExec]
  · constructor
    · rw [evaluateHOLFiniteState_seq_line780,firstRun]
      exact secondRun
    · rw [controlSteps_seq,firstRun]
      simp only
      omega


/-- If the first statement exits early, neither evaluator visits the second
statement; the only additional counted visit is the sequence node. -/
theorem counted_seq_exit {σ : Type}
    (context : PanValueFfiContext (BitVec 64)) (primitive : PanPrimitiveHandler (BitVec 64))
    (handler : PanValueStatefulFfiHandler (BitVec 64) σ) (structs : StructContext)
    (functions : List (FunName × List VarName × Prog (BitVec 64)))
    (base top bytes : BitVec 64) (fuel : Nat)
    (locals globals : VarName → Option (PanValue (BitVec 64)))
    (memory : BitVec 64 → Option (PanValue (BitVec 64))) (ffi : FfiState σ)
    (first second : Prog (BitVec 64)) (firstHOL secondHOL : ProgHOL 64)
    (access : Option (PanValueMemoryAccess (BitVec 64))) (contracts : Option PanValueCallContracts)
    (memoryHandler : Option (PanValueMemoryFfiHandler (BitVec 64) σ))
    (result : PanValueFfiControlResult (BitVec 64) σ) (cost : Nat)
    (source final : PanSemStateFiniteExact 64 σ) (holResult : PanSemResultExact 64)
    (firstExec : evalPanValueFfiProgSteps context primitive handler structs functions base top bytes fuel
      locals globals memory ffi first (memoryAccess := access) (contracts := contracts) (memoryHandler := memoryHandler) =
        some (result,cost))
    (nonNormal : ∀ l g m f, result ≠ .normal l g m f)
    (firstRun : source.evaluateHOLFiniteState firstHOL = (some holResult,final))
    (firstBound : controlSteps firstHOL source ≤ cost) :
    evalPanValueFfiProgSteps context primitive handler structs functions base top bytes (fuel+1)
      locals globals memory ffi (.seq first second) (memoryAccess := access) (contracts := contracts) (memoryHandler := memoryHandler) =
        some (result,cost+1) ∧
    source.evaluateHOLFiniteState (.seq firstHOL secondHOL) = (some holResult,final) ∧
    controlSteps (.seq firstHOL secondHOL) source ≤ cost+1 := by
  constructor
  · rw [evalPanValueFfiProgSteps]
    cases result with
    | normal l g m f => exact (nonNormal l g m f rfl).elim
    | returned l g m f values => simp [firstExec]
    | raised l g m f exception value => simp [firstExec]
    | broke l g m f => simp [firstExec]
    | continued l g m f => simp [firstExec]
    | error l g m f => simp [firstExec]
    | finalFfi l g m f event => simp [firstExec]
  · constructor
    · rw [evaluateHOLFiniteState_seq_line780,firstRun]
    · rw [controlSteps_seq,firstRun]
      simp only
      omega

end SteppedFlapjack.PanToCrepSteps
