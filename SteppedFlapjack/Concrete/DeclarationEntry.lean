import SteppedFlapjack.Concrete.BranchEntryLoop
import SteppedFlapjack.CrepSteps.TailEntryReturn
import SteppedFlapjack.CrepToLoopSteps.DeclExplicit

/-! Entry-level quantitative simulation for declarations with loops. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps

/-- A returning generated tail entry inherits an explicit optimized Loop
clock and visit bound from its Crep entry limit. -/
theorem generatedDecl_entry_explicit {σ : Type}
    (ctxt : CrepToLoopContextExact) (name : MlString) (declName : Nat) (init condition : CrepExpHOL 64)
    (body tail : CrepProgHOL 64) (initShape : DirectExpression init) (conditionShape : DirectExpression condition)
    (bodyShape : LoopFreeCrep body) (tailShape : LoopFreeCrep tail)
    (scalar : ScalarProgram (.dec declName init (.seq (.while condition body) tail)))
    (source : CrepSemHOLState 64 σ) (target : LoopSemStateFiniteExact 64 σ) (values : List (HolWordLab 64))
    (limit : Nat) (nonzero : source.clock ≠ 0)
    (found : source.code.lookup name = some ([],.dec declName init (.seq (.while condition body) tail)))
    (entryRun : ∃ final, evalCrepSemHOLProgExact source (.seq .skip (.call none name [])) =
      (some (.return values),final))
    (entryBound : CrepSteps.steps (.seq .skip (.call none name [])) source ≤ limit)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt .ln source.locals target.locals)
    (label : findLabExact ctxt name = 65) :
    let c := ctxtFcExact ctxt.target ctxt.funcs [] []
    let p := CrepProgHOL.dec declName init (.seq (.while condition body) tail)
    let bc := {c with vars := c.vars.updateEq (declName,c.vmax+1), vmax := c.vmax+1}
    let bl := sptInsert (c.vmax+1) () .ln
    let factor := 1 + (1 + sizeOf (compileHOLExact bc bl (.while condition body))) *
      (sizeOf (compileHOLExact bc bl body)+4) + sizeOf (compileHOLExact bc bl tail)
    let budget := (factor+4)*(limit+1)
    let code := compileHOLExact c .ln p
    ∃ post,
      evaluate branchingLoopEntry {target with clock := target.clock+2*budget} =
        (some (.result (values.map wlabWlocExact)),post) ∧
      LoopSteps.steps branchingLoopEntry {target with clock := target.clock+2*budget} ≤
        sizeOf (optimiseScalar code)*(2*budget+1)+8 := by
  let c := ctxtFcExact ctxt.target ctxt.funcs [] []
  let p := CrepProgHOL.dec declName init (.seq (.while condition body) tail)
  let bc := {c with vars := c.vars.updateEq (declName,c.vmax+1), vmax := c.vmax+1}
  let bl := sptInsert (c.vmax+1) () .ln
  let factor := 1 + (1 + sizeOf (compileHOLExact bc bl (.while condition body))) *
    (sizeOf (compileHOLExact bc bl body)+4) + sizeOf (compileHOLExact bc bl tail)
  let budget := (factor+4)*(limit+1)
  let code := compileHOLExact c .ln p
  obtain ⟨entryFinal,entryRun⟩ := entryRun
  obtain ⟨sourceFinal,calleeRun,calleeBound⟩ := CrepSteps.tail_entry_return_inv source entryFinal name p values limit
    found nonzero entryRun entryBound
  have rel := tailCall_nil_entry_relations ctxt .ln source target name p stateRel memRel globalsRel codeRel localsRel found
  obtain ⟨post,run,bound,_,_,_,_⟩ := directDecl_whileThenBranch_explicit declName init initShape condition body tail
    conditionShape bodyShape tailShape scalar c .ln _ sourceFinal _ _ limit calleeRun calleeBound (.return _)
    rel.1 rel.2.1 rel.2.2.1 rel.2.2.2.1 rel.2.2.2.2
  have targetNonzero : target.clock ≠ 0 := by have h := stateRel.2.2.1; omega
  have clockEq : ({decClock {target with clock := target.clock+2*budget} with locals := .ln} : LoopSemStateFiniteExact 64 σ) =
      {decClock target with locals := .ln, clock := (decClock target).clock+2*budget} := by
    simp only [decClock]
    congr 1
    omega
  have lookup := tailCall_nil_lookup ctxt source {target with clock := target.clock+2*budget} name p codeRel found
  rw [label] at lookup
  have lookup' : findCode (some 65) [] {target with clock := target.clock+2*budget}.code = some (.ln,optimiseHOL code) := by
    simpa [ocompileHOLExact,code,c,p] using lookup
  have cr : evaluate (optimiseHOL code) {decClock {target with clock := target.clock+2*budget} with locals := .ln} =
      (some (.result (values.map wlabWlocExact)),post) := by
    rw [clockEq]
    simpa [code,c,p,resultToLoop] using run
  have cb : LoopSteps.steps (optimiseHOL code) {decClock {target with clock := target.clock+2*budget} with locals := .ln} ≤
      sizeOf (optimiseScalar code)*(2*budget+1) := by rw [clockEq]; exact bound
  have entry := generatedEntry_return {target with clock := target.clock+2*budget} post (optimiseHOL code) _
    (sizeOf (optimiseScalar code)*(2*budget+1)) (by simp only; omega) lookup' cr cb
  exact ⟨post,entry.1,entry.2⟩
end SteppedFlapjack.Concrete
