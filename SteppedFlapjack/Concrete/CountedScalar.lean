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
end SteppedFlapjack.Concrete
