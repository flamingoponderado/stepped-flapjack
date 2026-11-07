import SteppedFlapjack.Concrete.ScalarWords
import SteppedFlapjack.PanToCrepSteps.CountedInvert
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact SteppedFlapjack.PanToCrepSteps

/-- A successful counted scalar initializer supplies the HOL value and its
exact expression cost; scalar locals remain word-valued. -/
theorem counted_scalar_initializer_invert {σ : Type} {scope : List VarName}
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (words : WordLocals production.locals)
    (initializer : Exp (RiscV.Word 64)) (scalar : Scalar scope initializer) (exprRanged : ExpByteRanged initializer)
    (value : PanValue (RiscV.Word 64)) (cost : Nat)
    (run : panValueDecAccepted production.structs production.baseAddress production.topAddress panSemBitVec64BytesInWord
      production.locals production.globals production.memory initializer
      (some (panSemBitVec64MemoryAccess production)) .one = some (value,cost)) :
    ∃ word, value = .word word ∧ cost = panValueExpStepCost initializer ∧
      @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a))
        (expToHOL initializer) = some (.val (.word word)) := by
  simp only [panValueDecAccepted,evalPanValueExpCounted] at run
  cases evaluated : evalPanValueExp production.structs production.locals production.globals production.memory
      production.baseAddress production.topAddress panSemBitVec64BytesInWord initializer
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) with
  | none => simp [evaluated] at run
  | some result =>
    simp only [evaluated,Option.map_some] at run
    split at run
    · simp only [Option.some.injEq,Prod.mk.injEq] at run
      obtain ⟨rfl,rfl⟩ := run
      have expressionRun : evalPanSemStateExp production initializer = some result := by
        simpa only [evalPanSemStateExp_64_eq_previous] using evaluated
      obtain ⟨word,rfl⟩ := scalar_eval_word scalar production words result expressionRun
      exact ⟨word,rfl,rfl,(counted_condition_word production source rel ranged initializer exprRanged word expressionRun).2⟩
    · simp at run
/-- A counted scalar return carries a word, clears locals, and has the
corresponding HOL result and state. -/
theorem counted_scalar_return_invert {σ : Type} {scope : List VarName}
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    [DecidablePred source.memaddrs]
    (rel : PanSemStateRelExec production source.toExact) (ranged : PanSemStateRelExecRanged production)
    (words : WordLocals production.locals)
    (expression : Exp (RiscV.Word 64)) (scalar : Scalar scope expression) (exprRanged : ExpByteRanged expression)
    (value : PanValue (RiscV.Word 64)) (postLocals : VarName → Option (PanValue (RiscV.Word 64)))
    (context : PanValueFfiContext (RiscV.Word 64)) (primitive : PanPrimitiveHandler (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (functions : List (FunName × List VarName × Prog (RiscV.Word 64))) (fuel count : Nat)
    (run : evalPanValueFfiProgSteps context primitive handler production.structs functions
      production.baseAddress production.topAddress panSemBitVec64BytesInWord fuel
      production.locals production.globals production.memory production.ffi (.return expression)
      (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
        some (.returned postLocals production.globals production.memory production.ffi [value],count)) :
    ∃ word, value = .word word ∧ postLocals = (fun _ => none) ∧
      source.evaluateHOLFiniteState (.return (expToHOL expression)) =
        (some (.returned (.val (.word word))),source.emptyLocalsHOLFinite) ∧
      PanSemStateRelExec (panEmptyLocals production) source.emptyLocalsHOLFinite.toExact ∧
      PanSemStateRelExecRanged (panEmptyLocals production) ∧
      controlSteps (.return (expToHOL expression)) source ≤ count := by
  cases fuel with
  | zero => simp [evalPanValueFfiProgSteps] at run
  | succ fuel =>
    have originalRun := run
    simp only [evalPanValueFfiProgSteps,panValueReturnSteps,evalPanValueExpCountedWith,
      evalPanValueExpCounted] at run
    cases evaluated : evalPanValueExp production.structs production.locals production.globals production.memory
        production.baseAddress production.topAddress panSemBitVec64BytesInWord expression
        (memoryAccess := some (panSemBitVec64MemoryAccess production)) with
    | none => simp [evaluated] at run
    | some result =>
      simp only [evaluated,Option.map_some] at run
      split at run
      · simp only [Option.some.injEq,Prod.mk.injEq,PanValueFfiControlResult.returned.injEq,List.cons.injEq,
          and_true,true_and] at run
        obtain ⟨⟨localsEq,valueEq⟩,costEq⟩ := run
        have expressionRun : evalPanSemStateExp production expression = some result := by
          simpa only [evalPanSemStateExp_64_eq_previous] using evaluated
        obtain ⟨word,resultEq⟩ := scalar_eval_word scalar production words result expressionRun
        have valueWord : value = .word word := valueEq.symm.trans resultEq
        subst postLocals
        have originalRun' : evalPanValueFfiProgSteps context primitive handler production.structs functions
            production.baseAddress production.topAddress panSemBitVec64BytesInWord (fuel+1)
            production.locals production.globals production.memory production.ffi (.return expression)
            (memoryAccess := some (panSemBitVec64MemoryAccess production)) =
              some (.returned (fun _ => none) production.globals production.memory production.ffi [.word word],count) := by
          simpa [valueWord] using originalRun
        have inverted := counted_return_invert production source rel ranged expression exprRanged word
          context primitive handler functions (fuel+1) count originalRun'
        exact ⟨word,valueWord,rfl,inverted⟩
      · simp at run

end SteppedFlapjack.Concrete
