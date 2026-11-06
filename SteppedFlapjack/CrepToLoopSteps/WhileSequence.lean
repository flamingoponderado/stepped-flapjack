import SteppedFlapjack.CrepToLoopSteps.WhileInduction
import SteppedFlapjack.LoopSteps.IterationShift

/-! A direct-condition loop followed by a loop-free branch. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.LoopToWordSteps

/-- The sequence is accepted by the existing Loop-to-RISC-V fragment. -/
theorem whileThenBranch_select {width : Nat} [NeZero width]
    (condition : CrepExpHOL width) (conditionShape : DirectExpression condition)
    (body tail : CrepProgHOL width) (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    LoopSelectProgram (compileHOLExact ctxt live (.seq (.while condition body) tail)) := by
  obtain ⟨_,_,_,whileShape⟩ := compile_directWhile condition conditionShape body bodyShape ctxt live
  simpa only [compileHOLExact] using
    LoopSelectProgram.seq whileShape (compile_branchProgram_select tailShape ctxt live)

/-- Actual compilation preserves a source-step bound for a direct Crep while
followed by a supported branch, including early loop exits. -/
theorem whileThenBranch_correct_with_steps {width : Nat} [NeZero width] {σ : Type}
    (condition : CrepExpHOL width) (conditionShape : DirectExpression condition)
    (body tail : CrepProgHOL width) (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (source sourceFinal : CrepSemHOLState width σ) (result : Option (CrepResultHOLExact width))
    (target : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (live : NumSet)
    (run : evalCrepSemHOLProgExact source (.seq (.while condition body) tail) = (result,sourceFinal))
    (nonerror : result ≠ some .error)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    ∃ value extra targetFinal,
      compileHOLExact ctxt live (.while condition body) = .loop live (directWhileBody ctxt live value body) live ∧
      evaluate (compileHOLExact ctxt live (.seq (.while condition body) tail)) {target with clock := target.clock+extra} =
        (resultToLoop result,targetFinal) ∧
      crepToLoopStateRelExact sourceFinal targetFinal ∧
      crepToLoopMemRelHOLExact sourceFinal.memory targetFinal.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals targetFinal.globals ∧
      crepToLoopCodeRelExact ctxt sourceFinal.code targetFinal.code ∧
      localsResultRel ctxt live result sourceFinal targetFinal ∧
      LoopSteps.steps (compileHOLExact ctxt live (.seq (.while condition body) tail)) {target with clock := target.clock+extra} ≤
        (1 + (1 + sizeOf (directWhileBody ctxt live value body)) * (sizeOf (compileHOLExact ctxt live body)+3) +
          sizeOf (compileHOLExact ctxt live tail)) * (CrepSteps.steps (.seq (.while condition body) tail) source+1) := by
  have seqRun := run
  rw [evalCrepSemHOLProgExact_seq_holShape] at seqRun
  rcases firstRun : evalCrepSemHOLProgExact source (.while condition body) with ⟨firstResult,middle⟩
  rw [firstRun] at seqRun
  have sourceCount := CrepSteps.steps_seq (.while condition body) tail source
  rw [firstRun] at sourceCount
  have firstNonerror : firstResult ≠ some .error := by
    intro bad
    rw [bad] at seqRun
    simp only [Option.some_ne_none,if_false,Prod.mk.injEq] at seqRun
    exact nonerror seqRun.1.symm
  obtain ⟨value,firstExtra,firstTarget,compiledFirst,firstTargetRun,firstState,firstMem,firstGlobals,
    firstCode,firstLocals,firstBound⟩ :=
    directWhile_bounded_steps condition conditionShape body bodyShape source middle firstResult target ctxt live
      firstRun firstNonerror stateRel memRel globalsRel codeRel localsRel
  have firstShape : BranchedProgram (directWhileBody ctxt live value body) := by
    obtain ⟨value2,comp2,shape2,_⟩ := compile_directWhile condition conditionShape body bodyShape ctxt live
    rw [compiledFirst] at comp2
    cases comp2
    exact shape2
  cases firstResult with
  | none =>
    simp only at seqRun
    obtain ⟨secondExtra,targetResult,targetFinal,secondRun,secondState,secondMem,secondGlobals,
      secondCode,resultMap,secondLocals,_,_⟩ :=
      branchProgram_correct_with_bounded_extra tail tailShape middle sourceFinal result firstTarget ctxt live
        seqRun nonerror firstState firstMem firstGlobals firstCode firstLocals
    have targetLift := evaluate_add_clock_eq (compileHOLExact ctxt live (.while condition body))
      {target with clock := target.clock+firstExtra} none firstTarget secondExtra firstTargetRun (by simp)
    have loopRun : evaluate (.loop live (directWhileBody ctxt live value body) live)
        {target with clock := target.clock+firstExtra} = (none,firstTarget) := by
      simpa [compiledFirst,resultToLoop] using firstTargetRun
    have stepLift := LoopSteps.branchedLoop_steps_add_clock live live (directWhileBody ctxt live value body)
      firstShape {target with clock := target.clock+firstExtra} firstTarget none loopRun (by simp) secondExtra
    have firstLift : evaluate (compileHOLExact ctxt live (.while condition body))
        {target with clock := target.clock+(firstExtra+secondExtra)} =
          (none,{firstTarget with clock := firstTarget.clock+secondExtra}) := by
      simpa [Nat.add_assoc] using targetLift
    have firstStepLift : LoopSteps.steps (compileHOLExact ctxt live (.while condition body))
        {target with clock := target.clock+(firstExtra+secondExtra)} =
          LoopSteps.steps (compileHOLExact ctxt live (.while condition body)) {target with clock := target.clock+firstExtra} := by
      simpa [compiledFirst,Nat.add_assoc] using stepLift
    have secondBound := LoopSteps.branchedProgram_static_bound (compile_branchProgram tailShape ctxt live)
      {firstTarget with clock := firstTarget.clock+secondExtra}
    have seqCount := LoopSteps.steps_seq (compileHOLExact ctxt live (.while condition body)) (compileHOLExact ctxt live tail)
      {target with clock := target.clock+(firstExtra+secondExtra)}
    rw [firstLift,firstStepLift] at seqCount
    refine ⟨value,firstExtra+secondExtra,targetFinal,compiledFirst,?_,secondState,secondMem,secondGlobals,secondCode,secondLocals,?_⟩
    · rw [compileHOLExact,evaluate_seq,firstLift]
      simpa [resultMap] using secondRun
    · simp only at sourceCount seqCount
      rw [compileHOLExact]
      let L := (1 + sizeOf (directWhileBody ctxt live value body)) * (sizeOf (compileHOLExact ctxt live body)+3)
      rw [← Nat.mul_assoc] at firstBound
      change LoopSteps.steps (compileHOLExact ctxt live (.while condition body)) {target with clock := target.clock+firstExtra} ≤
        L * (CrepSteps.steps (.while condition body) source+1) at firstBound
      change LoopSteps.steps (.seq (compileHOLExact ctxt live (.while condition body)) (compileHOLExact ctxt live tail))
        {target with clock := target.clock+(firstExtra+secondExtra)} ≤
        (1+L+sizeOf (compileHOLExact ctxt live tail)) * (CrepSteps.steps (.seq (.while condition body) tail) source+1)
      nlinarith
  | some r =>
    simp only [Option.some_ne_none,if_false,Prod.mk.injEq] at seqRun
    obtain ⟨rfl,rfl⟩ := seqRun
    have targetSome : resultToLoop (some r) ≠ none := by cases r <;> simp [resultToLoop]
    refine ⟨value,firstExtra,firstTarget,compiledFirst,?_,firstState,firstMem,firstGlobals,firstCode,firstLocals,?_⟩
    · rw [compileHOLExact,evaluate_seq,firstTargetRun]
      cases h : resultToLoop (some r) with
      | none => exact (targetSome h).elim
      | some v => rfl
    · have seqCount := LoopSteps.steps_seq (compileHOLExact ctxt live (.while condition body)) (compileHOLExact ctxt live tail)
        {target with clock := target.clock+firstExtra}
      rw [firstTargetRun] at seqCount
      cases h : resultToLoop (some r) with
      | none => exact (targetSome h).elim
      | some v =>
        simp only [h] at seqCount
        simp only at sourceCount
        rw [compileHOLExact]
        let L := (1 + sizeOf (directWhileBody ctxt live value body)) * (sizeOf (compileHOLExact ctxt live body)+3)
        rw [← Nat.mul_assoc] at firstBound
        change LoopSteps.steps (compileHOLExact ctxt live (.while condition body)) {target with clock := target.clock+firstExtra} ≤
          L * (CrepSteps.steps (.while condition body) source+1) at firstBound
        change LoopSteps.steps (.seq (compileHOLExact ctxt live (.while condition body)) (compileHOLExact ctxt live tail))
          {target with clock := target.clock+firstExtra} ≤
          (1+L+sizeOf (compileHOLExact ctxt live tail)) * (CrepSteps.steps (.seq (.while condition body) tail) source+1)
        nlinarith

end SteppedFlapjack.CrepToLoopSteps
