import SteppedFlapjack.CrepToLoopSteps.ConditionInduction
import SteppedFlapjack.LoopSteps.IterationShift

/-! A direct-condition loop followed by a loop-free branch. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open SteppedFlapjack.LoopToWordSteps

/-- The sequence is accepted by the existing Loop-to-RISC-V fragment. -/
theorem conditionWhileThenBranch_select {width : Nat} [NeZero width]
    (condition : CrepExpHOL width) (conditionShape : CompiledScalar condition)
    (body tail : CrepProgHOL width) (bodyShape : LoopFreeCrep body) (tailShape : LoopFreeCrep tail)
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    LoopSelectProgram (compileHOLExact ctxt live (.seq (.while condition body) tail)) := by
  obtain ⟨_,_,_,_,_,_,_,whileShape⟩ := branchCondition_compileWhile condition conditionShape body bodyShape ctxt live
  simpa only [compileHOLExact] using
    LoopSelectProgram.seq whileShape (compile_loopFreeCrep_select tailShape ctxt live)

/-- Actual compilation preserves a source-step bound for a direct Crep while
followed by a supported branch, including early loop exits. -/
theorem conditionWhileThenBranch_correct_with_steps {width : Nat} [NeZero width] {σ : Type}
    (condition : CrepExpHOL width) (conditionShape : CompiledScalar condition)
    (body tail : CrepProgHOL width) (bodyShape : LoopFreeCrep body) (tailShape : LoopFreeCrep tail)
    (source sourceFinal : CrepSemHOLState width σ) (result : Option (CrepResultHOLExact width))
    (target : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (live : NumSet)
    (run : evalCrepSemHOLProgExact source (.seq (.while condition body) tail) = (result,sourceFinal))
    (nonerror : result ≠ some .error)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    ∃ code value next outLive extra targetFinal,
      compileExpHOLExact ctxt (ctxt.vmax+1) live condition = (code,value,next,outLive) ∧
      compileHOLExact ctxt live (.while condition body) = .loop live (branchConditionWhileBody ctxt live code value next body) live ∧
      evaluate (compileHOLExact ctxt live (.seq (.while condition body) tail)) {target with clock := target.clock+extra} =
        (resultToLoop result,targetFinal) ∧
      crepToLoopStateRelExact sourceFinal targetFinal ∧
      crepToLoopMemRelHOLExact sourceFinal.memory targetFinal.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals targetFinal.globals ∧
      crepToLoopCodeRelExact ctxt sourceFinal.code targetFinal.code ∧
      localsResultRel ctxt live result sourceFinal targetFinal ∧
      LoopSteps.steps (compileHOLExact ctxt live (.seq (.while condition body) tail)) {target with clock := target.clock+extra} ≤
        (1 + (1 + sizeOf (branchConditionWhileBody ctxt live code value next body)) * (sizeOf (loopNestedSeqHOL code) + sizeOf (compileHOLExact ctxt live body)+3) +
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
  obtain ⟨code,value,next,outLive,firstExtra,firstTarget,exprCompiled,compiledFirst,firstTargetRun,firstState,firstMem,firstGlobals,
    firstCode,firstLocals,firstBound⟩ :=
    branchConditionWhile_bounded_steps condition conditionShape body bodyShape source middle firstResult target ctxt live
      firstRun firstNonerror stateRel memRel globalsRel codeRel localsRel
  have firstShape : BranchedProgram (branchConditionWhileBody ctxt live code value next body) := by
    obtain ⟨code2,value2,next2,outLive2,_,comp2,shape2,_⟩ := branchCondition_compileWhile condition conditionShape body bodyShape ctxt live
    rw [compiledFirst] at comp2
    have eqBody : branchConditionWhileBody ctxt live code2 value2 next2 body =
        branchConditionWhileBody ctxt live code value next body := by
      injection comp2
      symm
      assumption
    rw [← eqBody]
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
    have loopRun : evaluate (.loop live (branchConditionWhileBody ctxt live code value next body) live)
        {target with clock := target.clock+firstExtra} = (none,firstTarget) := by
      simpa [compiledFirst,resultToLoop] using firstTargetRun
    have stepLift := LoopSteps.branchedLoop_steps_add_clock live live (branchConditionWhileBody ctxt live code value next body)
      firstShape {target with clock := target.clock+firstExtra} firstTarget none loopRun (by simp) secondExtra
    have firstLift : evaluate (compileHOLExact ctxt live (.while condition body))
        {target with clock := target.clock+(firstExtra+secondExtra)} =
          (none,{firstTarget with clock := firstTarget.clock+secondExtra}) := by
      simpa [Nat.add_assoc] using targetLift
    have firstStepLift : LoopSteps.steps (compileHOLExact ctxt live (.while condition body))
        {target with clock := target.clock+(firstExtra+secondExtra)} =
          LoopSteps.steps (compileHOLExact ctxt live (.while condition body)) {target with clock := target.clock+firstExtra} := by
      simpa [compiledFirst,Nat.add_assoc] using stepLift
    have secondBound := LoopSteps.branchedProgram_static_bound (compile_loopFreeCrep tailShape ctxt live)
      {firstTarget with clock := firstTarget.clock+secondExtra}
    have seqCount := LoopSteps.steps_seq (compileHOLExact ctxt live (.while condition body)) (compileHOLExact ctxt live tail)
      {target with clock := target.clock+(firstExtra+secondExtra)}
    rw [firstLift,firstStepLift] at seqCount
    refine ⟨code,value,next,outLive,firstExtra+secondExtra,targetFinal,exprCompiled,compiledFirst,?_,secondState,secondMem,secondGlobals,secondCode,secondLocals,?_⟩
    · rw [compileHOLExact,evaluate_seq,firstLift]
      simpa [resultMap] using secondRun
    · simp only at sourceCount seqCount
      rw [compileHOLExact]
      let L := (1 + sizeOf (branchConditionWhileBody ctxt live code value next body)) * (sizeOf (loopNestedSeqHOL code) + sizeOf (compileHOLExact ctxt live body)+3)
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
    refine ⟨code,value,next,outLive,firstExtra,firstTarget,exprCompiled,compiledFirst,?_,firstState,firstMem,firstGlobals,firstCode,firstLocals,?_⟩
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
        let L := (1 + sizeOf (branchConditionWhileBody ctxt live code value next body)) * (sizeOf (loopNestedSeqHOL code) + sizeOf (compileHOLExact ctxt live body)+3)
        rw [← Nat.mul_assoc] at firstBound
        change LoopSteps.steps (compileHOLExact ctxt live (.while condition body)) {target with clock := target.clock+firstExtra} ≤
          L * (CrepSteps.steps (.while condition body) source+1) at firstBound
        change LoopSteps.steps (.seq (compileHOLExact ctxt live (.while condition body)) (compileHOLExact ctxt live tail))
          {target with clock := target.clock+firstExtra} ≤
          (1+L+sizeOf (compileHOLExact ctxt live tail)) * (CrepSteps.steps (.seq (.while condition body) tail) source+1)
        nlinarith

end SteppedFlapjack.CrepToLoopSteps
