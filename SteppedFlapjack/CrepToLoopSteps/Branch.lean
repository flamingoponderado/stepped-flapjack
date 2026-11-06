import SteppedFlapjack.CrepToLoopSteps.ExprShape
import SteppedFlapjack.LoopSteps.BranchedStatic

/-! Crep direct expressions with declarations, sequences and conditionals. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.LoopToWordSteps

/-- Direct-expression programs closed under local declarations, sequencing and branching. -/
inductive BranchProgram {width : Nat} [NeZero width] : CrepProgHOL width → Prop
  | expr {p} : ExprProgram p → BranchProgram p
  | dec {name value body} : DirectExpression value → BranchProgram body → BranchProgram (.dec name value body)
  | seq {a b} : BranchProgram a → BranchProgram b → BranchProgram (.seq a b)
  | ite {cond a b} : DirectExpression cond → BranchProgram a → BranchProgram b → BranchProgram (.ite cond a b)

/-- Direct Loop programs are also branch programs. -/
theorem direct_branched {width : Nat} [NeZero width] {p : HolLoopProg width}
    (shape : LoopToWordSteps.DirectProgram p) : BranchedProgram p := by
  induction shape with
  | leaf h => exact .leaf h
  | seq _ _ ha hb => exact .seq ha hb
  | mark _ ih => exact .mark ih

/-- Crep branch compilation remains loop-free in LoopSem. -/
theorem compile_branchProgram {width : Nat} [NeZero width] {p : CrepProgHOL width}
    (shape : BranchProgram p) (ctxt : CrepToLoopContextExact) (live : NumSet) :
    BranchedProgram (compileHOLExact ctxt live p) := by
  induction shape generalizing ctxt live with
  | expr shape => exact direct_branched (compile_exprProgram shape ctxt live)
  | @dec name e body he hb ih =>
    obtain ⟨value,h⟩ := directExpression_noCode he ctxt (ctxt.vmax+1) live
    simp only [compileHOLExact,h,loopNestedSeqHOL]
    exact .seq (.leaf .skip) (.seq (.leaf (.assign _ _)) (ih _ _))
  | seq ha hb iha ihb => simpa only [compileHOLExact] using BranchedProgram.seq (iha ctxt live) (ihb ctxt live)
  | @ite cond a b hcond ha hb iha ihb =>
    obtain ⟨value,h⟩ := directExpression_noCode hcond ctxt (ctxt.vmax + 1) live
    simp only [compileHOLExact,h,List.nil_append,loopNestedSeqHOL]
    exact .seq (.leaf (.assign _ _)) (.seq (.ite _ _ _ _ (iha ctxt live) (ihb ctxt live)) (.leaf .skip))

/-- The same compiled program lies in the selected Loop-to-RISC-V fragment. -/
theorem compile_branchProgram_select {width : Nat} [NeZero width] {p : CrepProgHOL width}
    (shape : BranchProgram p) (ctxt : CrepToLoopContextExact) (live : NumSet) :
    LoopSelectProgram (compileHOLExact ctxt live p) := by
  induction shape generalizing ctxt live with
  | expr shape => exact compile_exprProgram_select shape ctxt live
  | @dec name e body he hb ih =>
    obtain ⟨value,h⟩ := directExpression_noCode he ctxt (ctxt.vmax+1) live
    simp only [compileHOLExact,h,loopNestedSeqHOL]
    exact .seq (.leaf .skip) (.seq (.assign _ _) (ih _ _))
  | seq ha hb iha ihb => simpa only [compileHOLExact] using LoopSelectProgram.seq (iha ctxt live) (ihb ctxt live)
  | @ite cond a b hcond ha hb iha ihb =>
    obtain ⟨value,h⟩ := directExpression_noCode hcond ctxt (ctxt.vmax + 1) live
    simp only [compileHOLExact,h,List.nil_append,loopNestedSeqHOL]
    exact .seq (.assign _ _) (.seq (.ite _ _ _ _ (iha ctxt live) (ihb ctxt live)) (.leaf .skip))

/-- The original semantic correctness theorem paired with a source-program
computed factor and the actual Crep statement count. -/
theorem branchProgram_correct_with_steps {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (shape : BranchProgram p)
    (source sourceFinal : CrepSemHOLState width σ) (result : Option (CrepResultHOLExact width))
    (target : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (live : NumSet)
    (run : evalCrepSemHOLProgExact source p = (result,sourceFinal)) (nonerror : result ≠ some .error)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    ∃ extra targetResult targetFinal,
      evaluate (compileHOLExact ctxt live p) {target with clock := target.clock + extra} = (targetResult,targetFinal) ∧
      crepToLoopStateRelExact sourceFinal targetFinal ∧
      crepToLoopMemRelHOLExact sourceFinal.memory targetFinal.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals targetFinal.globals ∧
      crepToLoopCodeRelExact ctxt sourceFinal.code targetFinal.code ∧
      targetResult = resultToLoop result ∧ localsResultRel ctxt live result sourceFinal targetFinal ∧
      LoopSteps.steps (compileHOLExact ctxt live p) {target with clock := target.clock + extra} ≤
        sizeOf (compileHOLExact ctxt live p) * CrepSteps.steps p source := by
  obtain ⟨extra,targetResult,targetFinal,he,hs,hm,hg,hc,hr,hl⟩ :=
    crepToLoopNcompileCorrectOf p source result sourceFinal target ctxt live run nonerror
      stateRel memRel globalsRel codeRel localsRel
  refine ⟨extra,targetResult,targetFinal,he,hs,hm,hg,hc,hr,hl,?_⟩
  have bound := LoopSteps.branchedProgram_static_bound (compile_branchProgram shape ctxt live)
    {target with clock := target.clock + extra}
  have positive := CrepSteps.steps_pos p source
  nlinarith

end SteppedFlapjack.CrepToLoopSteps
