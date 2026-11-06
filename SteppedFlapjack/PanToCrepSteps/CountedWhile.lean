import SteppedFlapjack.PanToCrepSteps.CountedIte

/-! Compositional loop steps for the counted executable and HOL semantics. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A zero condition stops immediately and counts the condition and loop node. -/
theorem counted_while_zero {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (condition : Exp (RiscV.Word 64)) (conditionRanged : ExpByteRanged condition)
    (conditionRun : evalPanSemStateExp production condition = some (.word 0))
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat)
    (body : Prog (RiscV.Word 64)) (bodyHOL : ProgHOL 64) :
    evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
      production.locals production.globals production.memory production.ffi (.while condition body)
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal production.locals production.globals production.memory production.ffi,panValueExpStepCost condition+1) ∧
    source.evaluateHOLFiniteState (.while (expToHOL condition) bodyHOL) = (none,source) ∧
    controlSteps (.while (expToHOL condition) bodyHOL) source ≤ panValueExpStepCost condition+1 := by
  obtain ⟨conditionCounted,exactEval⟩ := counted_condition_word production source rel ranged condition conditionRanged 0 conditionRun
  constructor
  · rw [evalPanValueFfiProgSteps]
    simp [conditionCounted]
  · constructor
    · rw [evaluateHOLFiniteState_while_fixClockRewrite]
      have finiteEval : @evalHOLFinite 64 σ _ source
          (fun address => Classical.propDecidable (source.memaddrs address)) (expToHOL condition) = some (.val (.word 0)) := exactEval
      rw [finiteEval]
      simp
    · rw [controlSteps_while]
      simp [exactEval]

/-- One nonzero iteration composes the actual body and recursive-loop runs.
The body may finish normally or continue; both evaluators agree on the
corresponding control result and use the decremented HOL clock. -/
theorem counted_while_iteration {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source middle final : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (condition : Exp (RiscV.Word 64)) (conditionRanged : ExpByteRanged condition) (word : BitVec 64)
    (conditionRun : evalPanSemStateExp production condition = some (.word word))
    (nonzero : word ≠ 0) (clock : source.clock ≠ 0)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat)
    (body : Prog (RiscV.Word 64)) (bodyHOL : ProgHOL 64)
    (localsPost globalsPost : VarName → Option (PanValue (RiscV.Word 64)))
    (memoryPost : BitVec 64 → Option (PanValue (BitVec 64))) (ffiPost : FfiState σ)
    (continued : Bool) (bodyCost restCost : Nat)
    (result : PanValueFfiControlResult (BitVec 64) σ) (holResult : Option (PanSemResultExact 64))
    (bodyExec : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi body
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
      some ((if continued then .continued localsPost globalsPost memoryPost ffiPost
        else .normal localsPost globalsPost memoryPost ffiPost),bodyCost))
    (bodyRun : source.decClockHOLFinite.evaluateHOLFiniteState bodyHOL =
      (if continued then some .continue else none,middle))
    (bodyBound : controlSteps bodyHOL source.decClockHOLFinite ≤ bodyCost)
    (restExec : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      localsPost globalsPost memoryPost ffiPost (.while condition body)
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) = some (result,restCost))
    (restRun : middle.evaluateHOLFiniteState (.while (expToHOL condition) bodyHOL) = (holResult,final))
    (restBound : controlSteps (.while (expToHOL condition) bodyHOL) middle ≤ restCost) :
    evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
      production.locals production.globals production.memory production.ffi (.while condition body)
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (result,panValueExpStepCost condition+bodyCost+restCost+1) ∧
    source.evaluateHOLFiniteState (.while (expToHOL condition) bodyHOL) = (holResult,final) ∧
    controlSteps (.while (expToHOL condition) bodyHOL) source ≤
      panValueExpStepCost condition+bodyCost+restCost+1 := by
  obtain ⟨conditionCounted,exactEval⟩ := counted_condition_word production source rel ranged condition conditionRanged word conditionRun
  have zeroBits : word ≠ (0#64) := by simpa using nonzero
  cases continued <;> simp only [Bool.false_eq_true,if_false,if_true] at bodyExec bodyRun
  all_goals
    constructor
    · rw [evalPanValueFfiProgSteps]
      simp [conditionCounted,zeroBits,bodyExec,restExec]
    · constructor
      · rw [evaluateHOLFiniteState_while_fixClockRewrite]
        have finiteEval : @evalHOLFinite 64 σ _ source
            (fun address => Classical.propDecidable (source.memaddrs address)) (expToHOL condition) = some (.val (.word word)) := exactEval
        rw [finiteEval]
        simp [zeroBits,clock,bodyRun,restRun]
      · rw [controlSteps_while]
        simp only [exactEval,if_pos (show word ≠ 0 ∧ source.clock ≠ 0 from ⟨nonzero,clock⟩),bodyRun]
        change 1 + (controlSteps bodyHOL source.decClockHOLFinite +
          controlSteps (.while (expToHOL condition) bodyHOL) middle) ≤ _
        omega


/-- A nonzero loop iteration ending in `break` completes the loop without a
recursive visit, in both the counted and HOL semantics. -/
theorem counted_while_break {σ : Type}
    (production : PanSemState (RiscV.Word 64) (FfiState σ))
    (source final : PanSemStateFiniteExact 64 σ) [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (condition : Exp (RiscV.Word 64)) (conditionRanged : ExpByteRanged condition) (word : BitVec 64)
    (conditionRun : evalPanSemStateExp production condition = some (.word word))
    (nonzero : word ≠ 0) (clock : source.clock ≠ 0)
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel : Nat)
    (body : Prog (RiscV.Word 64)) (bodyHOL : ProgHOL 64)
    (localsPost globalsPost : VarName → Option (PanValue (RiscV.Word 64)))
    (memoryPost : BitVec 64 → Option (PanValue (BitVec 64))) (ffiPost : FfiState σ) (bodyCost : Nat)
    (bodyExec : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi body
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
      some (.broke localsPost globalsPost memoryPost ffiPost,bodyCost))
    (bodyRun : source.decClockHOLFinite.evaluateHOLFiniteState bodyHOL = (some .break,final))
    (bodyBound : controlSteps bodyHOL source.decClockHOLFinite ≤ bodyCost) :
    evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
      production.locals production.globals production.memory production.ffi (.while condition body)
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.normal localsPost globalsPost memoryPost ffiPost,panValueExpStepCost condition+bodyCost+1) ∧
    source.evaluateHOLFiniteState (.while (expToHOL condition) bodyHOL) = (none,final) ∧
    controlSteps (.while (expToHOL condition) bodyHOL) source ≤ panValueExpStepCost condition+bodyCost+1 := by
  obtain ⟨conditionCounted,exactEval⟩ := counted_condition_word production source rel ranged condition conditionRanged word conditionRun
  have zeroBits : word ≠ (0#64) := by simpa using nonzero
  constructor
  · rw [evalPanValueFfiProgSteps]
    simp [conditionCounted,zeroBits,bodyExec]
  · constructor
    · rw [evaluateHOLFiniteState_while_fixClockRewrite]
      have finiteEval : @evalHOLFinite 64 σ _ source
          (fun address => Classical.propDecidable (source.memaddrs address)) (expToHOL condition) = some (.val (.word word)) := exactEval
      rw [finiteEval]
      simp [zeroBits,clock,bodyRun]
    · rw [controlSteps_while]
      simp only [exactEval,if_pos (show word ≠ 0 ∧ source.clock ≠ 0 from ⟨nonzero,clock⟩),bodyRun]
      change 1 + (controlSteps bodyHOL source.decClockHOLFinite + 0) ≤ _
      omega

end SteppedFlapjack.PanToCrepSteps
