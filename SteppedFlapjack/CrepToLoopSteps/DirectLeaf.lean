import SteppedFlapjack.CrepSteps.Defs
import SteppedFlapjack.LoopSteps.Defs
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Assembly

/-! Quantitative Crep-to-Loop correctness for direct control-flow leaves. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- Crep leaves compiled to a single Loop evaluator node. -/
inductive DirectLeaf {width : Nat} [NeZero width] : CrepProgHOL width → Prop
  | skip : DirectLeaf .skip
  | break (label) : DirectLeaf (.break label)
  | continue (label) : DirectLeaf (.continue label)
  | tick : DirectLeaf .tick

/-- The compiler preserves the exact number of visits for direct leaves,
independently of both states and their clocks. -/
theorem directLeaf_exact_steps {width : Nat} [NeZero width] {σ : Type}
    {p : CrepProgHOL width} (leaf : DirectLeaf p)
    (source : CrepSemHOLState width σ) (target : LoopSemStateFiniteExact width σ)
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    LoopSteps.steps (compileHOLExact ctxt live p) target = CrepSteps.steps p source := by
  have sourceOne : CrepSteps.steps p source = 1 := by
    apply CrepSteps.steps_leaf
    cases leaf <;> rfl
  rw [sourceOne]
  apply LoopSteps.steps_leaf
  cases leaf <;> simp [compileHOLExact]

/-- Original semantic correctness paired with the direct-leaf step equality. -/
theorem directLeaf_correct_with_steps {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (leaf : DirectLeaf p)
    (source sourcePost : CrepSemHOLState width σ) (result : Option (CrepResultHOLExact width))
    (target : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (live : NumSet)
    (run : evalCrepSemHOLProgExact source p = (result,sourcePost))
    (nonerror : result ≠ some .error)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    ∃ extra targetResult targetPost,
      LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt live p)
        { target with clock := target.clock + extra } = (targetResult,targetPost) ∧
      crepToLoopStateRelExact sourcePost targetPost ∧
      crepToLoopMemRelHOLExact sourcePost.memory targetPost.memory sourcePost.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourcePost.globals targetPost.globals ∧
      crepToLoopCodeRelExact ctxt sourcePost.code targetPost.code ∧
      targetResult = resultToLoop result ∧
      localsResultRel ctxt live result sourcePost targetPost ∧
      LoopSteps.steps (compileHOLExact ctxt live p)
        { target with clock := target.clock + extra } = CrepSteps.steps p source := by
  obtain ⟨extra,targetResult,targetPost,he,hs,hm,hg,hc,hr,hl⟩ :=
    crepToLoopNcompileCorrectOf p source result sourcePost target ctxt live
      run nonerror stateRel memRel globalsRel codeRel localsRel
  exact ⟨extra,targetResult,targetPost,he,hs,hm,hg,hc,hr,hl,
    directLeaf_exact_steps leaf source _ ctxt live⟩

end SteppedFlapjack.CrepToLoopSteps
