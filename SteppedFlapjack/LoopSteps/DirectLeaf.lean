import SteppedFlapjack.LoopSteps.Defs
import SteppedFlapjack.WordSteps.Defs
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Assembly

/-! Quantitative Loop-to-Word correctness for direct compiler leaves. -/
namespace SteppedFlapjack.LoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact

/-- Source leaves compiled to a single WordSem evaluator node. -/
inductive DirectLeaf {width : Nat} [NeZero width] : HolLoopProg width → Prop
  | skip : DirectLeaf .skip
  | fail : DirectLeaf .fail
  | tick : DirectLeaf .tick
  | assign (v e) : DirectLeaf (.assign v e)
  | arith (a) : DirectLeaf (.arith a)
  | store (e v) : DirectLeaf (.store e v)
  | setGlobal (v e) : DirectLeaf (.setGlobal v e)
  | load32 (a v) : DirectLeaf (.load32 a v)
  | loadByte (a v) : DirectLeaf (.loadByte a v)
  | store32 (a v) : DirectLeaf (.store32 a v)
  | storeByte (a v) : DirectLeaf (.storeByte a v)
  | break (n) : DirectLeaf (.break n)
  | continue (n) : DirectLeaf (.continue n)
  | raise (n) : DirectLeaf (.raise n)
  | ret (ns) : DirectLeaf (.return ns)
  | locValue (a b) : DirectLeaf (.locValue a b)

/-- Each direct leaf visits exactly one WordSem node, equal to its LoopSem
node count, independent of the source and target states. -/
theorem directLeaf_exact_steps {width : Nat} [NeZero width] {C F : Type}
    {p : HolLoopProg width} (leaf : DirectLeaf p)
    (source : LoopSemStateFiniteExact width F) (target : WordSemStateFiniteExact width C F)
    (ctxt : Spt Nat) (labels : Nat × Nat) :
    WordSteps.steps (LoopToWord.compHOL ctxt p labels).1 target = steps p source := by
  have sourceOne : steps p source = 1 := by
    apply steps_leaf
    cases leaf <;> rfl
  rw [sourceOne]
  apply WordSteps.steps_leaf
  cases labels
  cases leaf <;> try simp [LoopToWord.compHOL,WordSteps.isRecursive]
  case arith op => cases op <;> simp [LoopToWord.compHOL]


/-- Original Loop-to-Word semantic correctness plus the proved exact step
count for direct leaves. -/
theorem directLeaf_correct_with_steps {width : Nat} [NeZero width] {C F : Type}
    (p : HolLoopProg width) (leaf : DirectLeaf p)
    (source sourcePost : LoopSemStateFiniteExact width F)
    (result : Option (LoopResultExact width)) (target : WordSemStateFiniteExact width C F)
    (ctxt : Spt Nat) (retv : WordLocW width) (labels : Nat × Nat)
    (premises : LoopSemStateFiniteExact.evaluate p source = (result,sourcePost) ∧ result ≠ some .error ∧
      loopToWordStateRelHOLExact source target ∧ LoopToWord.localsRelHOL ctxt source.locals target.locals ∧
      sptLookup 0 target.locals = some retv ∧ goodDimindex width ∧ ¬ wordSemIsWordLoc retv = true ∧
      (∀ k, sptMem k (accVarsHOL p .ln) → sptMem k ctxt)) :
    ∃ targetPost targetResult,
      WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt p labels).1 target = (targetResult,targetPost) ∧
      targetPost.ffi = sourcePost.ffi ∧
      LoopToWord.CompileCorrect.resultCase ctxt retv target result sourcePost targetResult targetPost ∧
      WordSteps.steps (LoopToWord.compHOL ctxt p labels).1 target = steps p source := by
  obtain ⟨targetPost,targetResult,run,ffi,relation⟩ :=
    compileCorrect p source result sourcePost target ctxt retv labels premises
  exact ⟨targetPost,targetResult,run,ffi,relation,directLeaf_exact_steps leaf source target ctxt labels⟩

end SteppedFlapjack.LoopSteps
