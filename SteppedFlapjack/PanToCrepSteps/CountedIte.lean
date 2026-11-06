import SteppedFlapjack.PanToCrepSteps.CountedAssign

/-! Counted conditional composition over related Pancake states. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang

/-- The condition is evaluated by both semantics and the selected branch is
executed once. The child bound and expression-node cost bound the entire
conditional, for either zero or nonzero conditions. -/
theorem counted_ite_word {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source final : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (condition : Exp (RiscV.Word 64)) (conditionRanged : ExpByteRanged condition) (word : BitVec 64)
    (conditionRun : evalPanSemStateExp production condition = some (.word word))
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat)
    (thenBranch elseBranch : Prog (RiscV.Word 64)) (thenHOL elseHOL : ProgHOL 64)
    (result : PanValueFfiControlResult (RiscV.Word 64) σ) (holResult : Option (PanSemResultExact 64))
    (branchCost : Nat)
    (branchExec : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi
      (if word = 0 then elseBranch else thenBranch)
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,branchCost))
    (branchRun : source.evaluateHOLFiniteState (if word = 0 then elseHOL else thenHOL) = (holResult,final))
    (branchBound : controlSteps (if word = 0 then elseHOL else thenHOL) source ≤ branchCost) :
    evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
      production.locals production.globals production.memory production.ffi (.ite condition thenBranch elseBranch)
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (result,panValueExpStepCost condition+branchCost+1) ∧
    source.evaluateHOLFiniteState (.ite (expToHOL condition) thenHOL elseHOL) = (holResult,final) ∧
    controlSteps (.ite (expToHOL condition) thenHOL elseHOL) source ≤ panValueExpStepCost condition+branchCost+1 := by
  have previous : evalPanValueExp production.structs production.locals production.globals production.memory
      production.baseAddress production.topAddress panSemBitVec64BytesInWord condition
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (.word word) := by
    simpa only [evalPanSemStateExp_64_eq_previous] using conditionRun
  have counted : evalPanValueExpCounted production.structs production.locals production.globals production.memory
      production.baseAddress production.topAddress panSemBitVec64BytesInWord condition
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.word word,panValueExpStepCost condition) := by simp [evalPanValueExpCounted,previous]
  have valueAgree := evalPanSemStateExp_agree production source rel ranged condition conditionRanged
  have exactEval : @evalHOLExact 64 σ _ source.toExact
      (fun address => Classical.propDecidable (source.memaddrs address)) (expToHOL condition) = some (.val (.word word)) := by
    rw [evalHOLFinite_eq_classical,← valueAgree,conditionRun]
    simp
  have smallerThen : Prod.Lex (fun x y : Nat => x < y) (fun x y : Nat => x < y)
      (source.clock,sizeOf thenHOL) (source.clock,sizeOf (.ite (expToHOL condition) thenHOL elseHOL : ProgHOL 64)) := by
    apply Prod.Lex.right
    simp_wf
    omega
  have smallerElse : Prod.Lex (fun x y : Nat => x < y) (fun x y : Nat => x < y)
      (source.clock,sizeOf elseHOL) (source.clock,sizeOf (.ite (expToHOL condition) thenHOL elseHOL : ProgHOL 64)) := by
    apply Prod.Lex.right
    simp_wf
  by_cases zero : word = 0
  · subst word
    simp only [if_true] at branchExec branchRun branchBound
    constructor
    · rw [evalPanValueFfiProgSteps]
      simp [panValueIteCondition,counted,branchExec]
    · constructor
      · rw [PanSemStateFiniteExact.evaluateHOLFiniteState_ite,exactEval]
        simpa using branchRun
      · rw [controlSteps.eq_def]
        simp only [dif_pos smallerThen,dif_pos smallerElse,exactEval]
        simp only [ne_eq,not_true_eq_false,if_false]
        omega
  · simp only [if_neg zero] at branchExec branchRun branchBound
    have zeroBits : word ≠ (0#64) := by simpa using zero
    constructor
    · rw [evalPanValueFfiProgSteps]
      simp [panValueIteCondition,counted,zeroBits,branchExec]
    · constructor
      · rw [PanSemStateFiniteExact.evaluateHOLFiniteState_ite,exactEval]
        simpa [zeroBits] using branchRun
      · rw [controlSteps.eq_def]
        simp only [dif_pos smallerThen,dif_pos smallerElse,exactEval]
        simp only [if_pos zero]
        omega

end SteppedFlapjack.PanToCrepSteps
