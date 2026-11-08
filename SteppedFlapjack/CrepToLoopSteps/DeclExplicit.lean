import SteppedFlapjack.CrepToLoopSteps.DeclTerminal
import SteppedFlapjack.CrepToLoopSteps.ExplicitFromVisits
import SteppedFlapjack.CrepToLoopSteps.ScalarLoopShape

/-! Explicit source-derived clocks for declarations containing a loop. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.LoopToWordSteps

/-- A completed declaration/loop run compiles to an optimized Loop run at a
clock calculated from the source visit limit and compiler output. -/
theorem directDecl_whileThenBranch_explicit {σ : Type}
    (name : Nat) (e : CrepExpHOL 64) (shape : DirectExpression e)
    (condition : CrepExpHOL 64) (body tail : CrepProgHOL 64)
    (conditionShape : DirectExpression condition) (bodyShape : LoopFreeCrep body) (tailShape : BranchProgram tail)
    (scalar : ScalarProgram (.dec name e (.seq (.while condition body) tail)))
    (ctxt : CrepToLoopContextExact) (live : NumSet)
    (source sourceFinal : CrepSemHOLState 64 σ) (result : Option (CrepResultHOLExact 64))
    (target : LoopSemStateFiniteExact 64 σ) (limit : Nat)
    (run : evalCrepSemHOLProgExact source (.dec name e (.seq (.while condition body) tail)) = (result,sourceFinal))
    (sourceBound : CrepSteps.steps (.dec name e (.seq (.while condition body) tail)) source ≤ limit)
    (complete : CompleteCrepResult result)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    let p := CrepProgHOL.dec name e (.seq (.while condition body) tail)
    let bodyCtxt := {ctxt with vars := ctxt.vars.updateEq (name,ctxt.vmax+1), vmax := ctxt.vmax+1}
    let bodyLive := sptInsert (ctxt.vmax+1) () live
    let factor := 1 + (1 + sizeOf (compileHOLExact bodyCtxt bodyLive (.while condition body))) *
      (sizeOf (compileHOLExact bodyCtxt bodyLive body)+4) + sizeOf (compileHOLExact bodyCtxt bodyLive tail)
    let bound := (factor+4)*(limit+1)
    let code := compileHOLExact ctxt live p
    ∃ post,
      evaluate (optimiseHOL code) {target with clock := target.clock+2*bound} = (resultToLoop result,post) ∧
      LoopSteps.steps (optimiseHOL code) {target with clock := target.clock+2*bound} ≤
        sizeOf (optimiseScalar code)*(2*bound+1) ∧
      crepToLoopStateRelExact sourceFinal {post with clock := sourceFinal.clock} ∧
      crepToLoopMemRelHOLExact sourceFinal.memory post.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals post.globals ∧
      crepToLoopCodeRelExact ctxt sourceFinal.code post.code := by
  let p := CrepProgHOL.dec name e (.seq (.while condition body) tail)
  let bc := {ctxt with vars := ctxt.vars.updateEq (name,ctxt.vmax+1), vmax := ctxt.vmax+1}
  let bl := sptInsert (ctxt.vmax+1) () live
  let factor := 1 + (1 + sizeOf (compileHOLExact bc bl (.while condition body))) *
    (sizeOf (compileHOLExact bc bl body)+4) + sizeOf (compileHOLExact bc bl tail)
  let bound := (factor+4)*(limit+1)
  let code := compileHOLExact ctxt live p
  have ⟨condValue,condCompiled⟩ := directExpression_noCode conditionShape bc (bc.vmax+1) bl
  have continuation := conditionWhileThenBranch_programBound (σ := σ) condition (.direct conditionShape) body tail
    bodyShape tailShape bc bl
  simp only [condCompiled,loopNestedSeqHOL] at continuation
  obtain ⟨extra,oldPost,oldRun,hs,hm,hg,hc,visits⟩ :=
    directDecl_terminal_bound name e shape (.seq (.while condition body) tail) ctxt live _ continuation
      source sourceFinal result target run (completeCrep_nonerror complete)
      stateRel memRel globalsRel codeRel localsRel
  have sizeEq : sizeOf (.skip : HolLoopProg 64) + sizeOf (compileHOLExact bc bl body) + 3 =
      sizeOf (compileHOLExact bc bl body) + 4 := by simp; omega
  rw [sizeEq] at visits
  change LoopSteps.steps code {target with clock := target.clock+extra} ≤
      (factor+4)*(CrepSteps.steps p source+1) at visits
  change CrepSteps.steps p source ≤ limit at sourceBound
  have visitBound : LoopSteps.steps code {target with clock := target.clock+extra} ≤ bound := by
    exact visits.trans (Nat.mul_le_mul_left _ (by omega))
  have loopShape := compile_scalar_program scalar ctxt live
  have consumed := scalarLoop_consumed loopShape _ oldPost (resultToLoop result) oldRun
  change target.clock+extra-oldPost.clock ≤ 2*LoopSteps.steps code {target with clock := target.clock+extra} at consumed
  have sourceClock := evalCrepSemHOLProgExact_clock_le source p
  rw [run] at sourceClock
  have initial := stateRel.2.2.1
  have final := hs.2.2.1
  have extraBound : extra ≤ 2*bound := by simp only at consumed sourceClock; omega
  have optimized := scalarLoop_explicit_optimised loopShape target oldPost (resultToLoop result)
    extra (2*bound) bound oldRun (completeCrep_loop complete) extraBound visitBound
  refine ⟨{oldPost with clock := oldPost.clock+(2*bound-extra)},optimized.1,optimized.2,?_,?_,?_,?_⟩
  · simpa [crepToLoopStateRelExact,final] using hs
  · simpa using hm
  · simpa using hg
  · simpa using hc
end SteppedFlapjack.CrepToLoopSteps
