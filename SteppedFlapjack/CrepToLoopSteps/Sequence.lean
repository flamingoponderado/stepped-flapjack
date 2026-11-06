import SteppedFlapjack.CrepToLoopSteps.DirectLeaf
import SteppedFlapjack.LoopSteps.Clock

/-! Quantitative Crep-to-Loop simulation for direct leaves and sequences. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- Direct Crep leaves closed under sequencing. -/
inductive DirectProgram {width : Nat} [NeZero width] : CrepProgHOL width → Prop
  | leaf {p} : DirectLeaf p → DirectProgram p
  | returnNil : DirectProgram (.return [])
  | seq {a b} : DirectProgram a → DirectProgram b → DirectProgram (.seq a b)

/-- The compiled code lies in the Loop fragment with a clock-stable count. -/
theorem compile_directProgram {width : Nat} [NeZero width]
    {p : CrepProgHOL width} (shape : DirectProgram p)
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    LoopToWordSteps.DirectProgram (compileHOLExact ctxt live p) := by
  induction shape with
  | leaf leaf =>
    cases leaf <;> simp only [compileHOLExact] <;>
      exact .leaf (by constructor)
  | returnNil =>
    simp only [compileHOLExact, compileExpsHOLExact, genTemps, List.nil_append]
    exact .seq (.leaf (.ret _)) (.leaf .skip)
  | seq ha hb iha ihb =>
    simpa only [compileHOLExact] using LoopToWordSteps.DirectProgram.seq iha ihb

/-- Semantic correctness and a twofold count bound at a fixed source state. -/
def BoundPropertyAt {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (source : CrepSemHOLState width σ) : Prop :=
  ∀ (result : Option (CrepResultHOLExact width)) (sourceFinal : CrepSemHOLState width σ)
    (target : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (live : NumSet),
    evalCrepSemHOLProgExact source p = (result,sourceFinal) → result ≠ some .error →
    crepToLoopStateRelExact source target →
    crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs →
    crepToLoopGlobalsRelHOLExact source.globals target.globals →
    crepToLoopCodeRelExact ctxt source.code target.code →
    crepToLoopLocalsRelExact ctxt live source.locals target.locals →
    ∃ extra targetResult targetFinal,
      evaluate (compileHOLExact ctxt live p) {target with clock := target.clock + extra} =
        (targetResult,targetFinal) ∧
      crepToLoopStateRelExact sourceFinal targetFinal ∧
      crepToLoopMemRelHOLExact sourceFinal.memory targetFinal.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals targetFinal.globals ∧
      crepToLoopCodeRelExact ctxt sourceFinal.code targetFinal.code ∧
      targetResult = resultToLoop result ∧
      localsResultRel ctxt live result sourceFinal targetFinal ∧
      LoopSteps.steps (compileHOLExact ctxt live p) {target with clock := target.clock + extra} ≤
        2 * CrepSteps.steps p source

/-- Sequential composition preserves the quantitative correctness property. -/
theorem boundedSeq {width : Nat} [NeZero width] {σ : Type}
    (a b : CrepProgHOL width) (shapeA : DirectProgram a)
    (source : CrepSemHOLState width σ)
    (first : BoundPropertyAt a source)
    (second : ∀ middle : CrepSemHOLState width σ, BoundPropertyAt b middle) : BoundPropertyAt (.seq a b) source := by
  intro result sourceFinal target ctxt live run nonerror stateRel memRel globalsRel codeRel localsRel
  have sourceSeq := run
  rw [evalCrepSemHOLProgExact_seq_holShape] at sourceSeq
  rcases sourceFirst : evalCrepSemHOLProgExact source a with ⟨firstResult,middle⟩
  rw [sourceFirst] at sourceSeq
  cases firstResult with
  | none =>
    simp only at sourceSeq
    obtain ⟨firstExtra,firstTargetResult,firstTarget,firstRun,firstState,firstMem,
      firstGlobals,firstCode,firstResultMap,firstLocals,firstSteps⟩ :=
      first none middle target ctxt live sourceFirst (by simp) stateRel memRel globalsRel codeRel localsRel
    have firstNone : firstTargetResult = none := by simpa [resultToLoop] using firstResultMap
    subst firstTargetResult
    obtain ⟨secondExtra,targetResult,targetFinal,secondRun,secondState,secondMem,
      secondGlobals,secondCode,secondResultMap,secondLocals,secondSteps⟩ :=
      second middle result sourceFinal firstTarget ctxt live sourceSeq nonerror firstState firstMem
        firstGlobals firstCode firstLocals
    have firstLift := evaluate_add_clock_eq (compileHOLExact ctxt live a)
      {target with clock := target.clock + firstExtra} none firstTarget secondExtra firstRun (by simp)
    have stepLift := LoopSteps.directProgram_steps_add_clock (compile_directProgram shapeA ctxt live)
      {target with clock := target.clock + firstExtra} firstTarget none firstRun (by simp) secondExtra
    have sourceCount := CrepSteps.steps_seq a b source
    rw [sourceFirst] at sourceCount
    have targetCount := LoopSteps.steps_seq (compileHOLExact ctxt live a) (compileHOLExact ctxt live b)
      {target with clock := target.clock + (firstExtra + secondExtra)}
    have firstLift' : evaluate (compileHOLExact ctxt live a)
        {target with clock := target.clock + (firstExtra + secondExtra)} =
          (none,{firstTarget with clock := firstTarget.clock + secondExtra}) := by
      simpa [Nat.add_assoc] using firstLift
    have stepLift' : LoopSteps.steps (compileHOLExact ctxt live a)
        {target with clock := target.clock + (firstExtra + secondExtra)} =
          LoopSteps.steps (compileHOLExact ctxt live a) {target with clock := target.clock + firstExtra} := by
      simpa [Nat.add_assoc] using stepLift
    refine ⟨firstExtra + secondExtra,targetResult,targetFinal,?_,secondState,secondMem,
      secondGlobals,secondCode,secondResultMap,secondLocals,?_⟩
    · rw [compileHOLExact,evaluate_seq,firstLift']
      exact secondRun
    · rw [firstLift',stepLift'] at targetCount
      simp only at sourceCount targetCount
      simpa only [compileHOLExact] using (by omega :
        LoopSteps.steps (.seq (compileHOLExact ctxt live a) (compileHOLExact ctxt live b))
          {target with clock := target.clock + (firstExtra + secondExtra)} ≤ 2 * CrepSteps.steps (.seq a b) source)
  | some firstValue =>
    have pair : (some firstValue,middle) = (result,sourceFinal) := by simpa using sourceSeq
    have ⟨resultEq,finalEq⟩ := Prod.mk.inj pair
    subst result
    subst sourceFinal
    have firstNonerror : some firstValue ≠ some .error := nonerror
    obtain ⟨extra,targetResult,targetFinal,targetRun,finalState,finalMem,finalGlobals,
      finalCode,resultMap,finalLocals,bound⟩ :=
      first (some firstValue) middle target ctxt live sourceFirst firstNonerror stateRel memRel
        globalsRel codeRel localsRel
    have targetSome : targetResult ≠ none := by
      rw [resultMap]
      cases firstValue <;> simp [resultToLoop]
    refine ⟨extra,targetResult,targetFinal,?_,finalState,finalMem,finalGlobals,finalCode,
      resultMap,finalLocals,?_⟩
    · rw [compileHOLExact,evaluate_seq,targetRun]
      cases targetResult with
      | none => exact (targetSome rfl).elim
      | some r => rfl
    · have sourceCount := CrepSteps.steps_seq a b source
      rw [sourceFirst] at sourceCount
      have targetCount := LoopSteps.steps_seq (compileHOLExact ctxt live a) (compileHOLExact ctxt live b)
        {target with clock := target.clock + extra}
      rw [targetRun] at targetCount
      cases targetResult with
      | none => exact (targetSome rfl).elim
      | some r =>
        simp only at sourceCount targetCount
        simpa only [compileHOLExact] using (by omega :
          LoopSteps.steps (.seq (compileHOLExact ctxt live a) (compileHOLExact ctxt live b))
            {target with clock := target.clock + extra} ≤ 2 * CrepSteps.steps (.seq a b) source)

/-- Quantitative correctness for direct Crep programs, with no conjecture
assumptions about their subprograms. -/
theorem directProgram_correct_with_steps {width : Nat} [NeZero width] {σ : Type}
    {p : CrepProgHOL width} (shape : DirectProgram p) :
    ∀ source : CrepSemHOLState width σ, BoundPropertyAt p source := by
  induction shape with
  | leaf leaf =>
    intro source result sourceFinal target ctxt live run nonerror stateRel memRel globalsRel codeRel localsRel
    obtain ⟨extra,targetResult,targetFinal,he,hs,hm,hg,hc,hr,hl,steps⟩ :=
      directLeaf_correct_with_steps _ leaf source sourceFinal result target ctxt live run nonerror
        stateRel memRel globalsRel codeRel localsRel
    exact ⟨extra,targetResult,targetFinal,he,hs,hm,hg,hc,hr,hl,by omega⟩
  | returnNil =>
    intro source result sourceFinal target ctxt live run nonerror stateRel memRel globalsRel codeRel localsRel
    obtain ⟨extra,targetResult,targetFinal,he,hs,hm,hg,hc,hr,hl⟩ :=
      crepToLoopNcompileCorrectOf (.return []) source result sourceFinal target ctxt live run nonerror
        stateRel memRel globalsRel codeRel localsRel
    refine ⟨extra,targetResult,targetFinal,he,hs,hm,hg,hc,hr,hl,?_⟩
    have sourceOne : CrepSteps.steps (.return []) source = 1 := CrepSteps.steps_leaf _ _ (by rfl)
    rw [sourceOne]
    simp [compileHOLExact, compileExpsHOLExact, genTemps, loopNestedSeqHOL,
      LoopSteps.steps_seq, evaluate, LoopSemStateFiniteExact.getVars, LoopSteps.steps_leaf]
  | @seq a b ha hb iha ihb =>
    intro source
    exact boundedSeq a b ha source (iha source) ihb

end SteppedFlapjack.CrepToLoopSteps
