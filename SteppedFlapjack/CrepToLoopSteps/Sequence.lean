import SteppedFlapjack.CrepToLoopSteps.DirectLeaf
import SteppedFlapjack.LoopSteps.Clock
import SteppedFlapjack.LoopLiveSteps.TailEntryCode

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

/-- Semantic correctness and a visit bound at a fixed source state. -/
def BoundPropertyAt {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (source : CrepSemHOLState width σ) (factor : Nat := 2)
    (tableOk : Spt (List Nat × HolLoopProg width) → Prop := fun _ => True) : Prop :=
  ∀ (result : Option (CrepResultHOLExact width)) (sourceFinal : CrepSemHOLState width σ)
    (target : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (live : NumSet),
    evalCrepSemHOLProgExact source p = (result,sourceFinal) → result ≠ some .error →
    crepToLoopStateRelExact source target →
    crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs →
    crepToLoopGlobalsRelHOLExact source.globals target.globals →
    crepToLoopCodeRelExact ctxt source.code target.code →
    tableOk target.code →
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
        factor * CrepSteps.steps p source

/-- A visit bound remains valid when its program-dependent factor grows. -/
theorem BoundPropertyAt.mono {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (source : CrepSemHOLState width σ) (small large : Nat)
    (tableOk : Spt (List Nat × HolLoopProg width) → Prop)
    (le : small ≤ large) (bound : BoundPropertyAt p source small tableOk) : BoundPropertyAt p source large tableOk := by
  intro result sourceFinal target ctxt live run nonerror stateRel memRel globalsRel codeRel tableGood localsRel
  obtain ⟨extra,targetResult,targetFinal,he,hs,hm,hg,hc,hr,hl,cost⟩ :=
    bound result sourceFinal target ctxt live run nonerror stateRel memRel globalsRel codeRel tableGood localsRel
  exact ⟨extra,targetResult,targetFinal,he,hs,hm,hg,hc,hr,hl,
    Nat.le_trans cost (Nat.mul_le_mul_right _ le)⟩

/-- Existing bounds remain valid when the target-table condition is strengthened. -/
theorem BoundPropertyAt.restrict {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (source : CrepSemHOLState width σ) (factor : Nat)
    (old new : Spt (List Nat × HolLoopProg width) → Prop)
    (h : ∀ code, new code → old code) (bound : BoundPropertyAt p source factor old) :
    BoundPropertyAt p source factor new := by
  intro result sourceFinal target ctxt live run nonerror stateRel memRel globalsRel codeRel tableGood localsRel
  exact bound result sourceFinal target ctxt live run nonerror stateRel memRel globalsRel codeRel (h _ tableGood) localsRel

/-- Sequential composition preserves the quantitative correctness property. -/
theorem boundedSeq {width : Nat} [NeZero width] {σ : Type}
    (a b : CrepProgHOL width) (source : CrepSemHOLState width σ) (factor : Nat) (positive : 1 ≤ factor)
    (tableOk : Spt (List Nat × HolLoopProg width) → Prop)
    (stepShift : ∀ (ctxt : CrepToLoopContextExact) (live : NumSet)
      (target middle : LoopSemStateFiniteExact width σ) (extra : Nat),
      tableOk target.code →
      evaluate (compileHOLExact ctxt live a) target = (none,middle) →
      LoopSteps.steps (compileHOLExact ctxt live a) {target with clock := target.clock + extra} =
        LoopSteps.steps (compileHOLExact ctxt live a) target)
    (first : BoundPropertyAt a source factor tableOk)
    (second : ∀ middle : CrepSemHOLState width σ,
      evalCrepSemHOLProgExact source a = (none,middle) → BoundPropertyAt b middle factor tableOk) :
    BoundPropertyAt (.seq a b) source factor tableOk := by
  intro result sourceFinal target ctxt live run nonerror stateRel memRel globalsRel codeRel tableGood localsRel
  have sourceSeq := run
  rw [evalCrepSemHOLProgExact_seq_holShape] at sourceSeq
  rcases sourceFirst : evalCrepSemHOLProgExact source a with ⟨firstResult,middle⟩
  rw [sourceFirst] at sourceSeq
  cases firstResult with
  | none =>
    simp only at sourceSeq
    obtain ⟨firstExtra,firstTargetResult,firstTarget,firstRun,firstState,firstMem,
      firstGlobals,firstCode,firstResultMap,firstLocals,firstSteps⟩ :=
      first none middle target ctxt live sourceFirst (by simp) stateRel memRel globalsRel codeRel tableGood localsRel
    have firstNone : firstTargetResult = none := by simpa [resultToLoop] using firstResultMap
    subst firstTargetResult
    have codeSame : firstTarget.code = target.code := by
      have h := SteppedFlapjack.LoopLiveSteps.evaluate_code (compileHOLExact ctxt live a)
        {target with clock := target.clock + firstExtra} firstTarget none firstRun
      exact h
    have firstTable : tableOk firstTarget.code := by rw [codeSame]; exact tableGood
    obtain ⟨secondExtra,targetResult,targetFinal,secondRun,secondState,secondMem,
      secondGlobals,secondCode,secondResultMap,secondLocals,secondSteps⟩ :=
      second middle sourceFirst result sourceFinal firstTarget ctxt live sourceSeq nonerror firstState firstMem
        firstGlobals firstCode firstTable firstLocals
    have firstLift := evaluate_add_clock_eq (compileHOLExact ctxt live a)
      {target with clock := target.clock + firstExtra} none firstTarget secondExtra firstRun (by simp)
    have stepLift := stepShift ctxt live {target with clock := target.clock + firstExtra} firstTarget secondExtra
      (by simpa using tableGood) firstRun
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
      simpa only [compileHOLExact] using (by rw [sourceCount]; simp only [Nat.mul_add, Nat.mul_one]; omega :
        LoopSteps.steps (.seq (compileHOLExact ctxt live a) (compileHOLExact ctxt live b))
          {target with clock := target.clock + (firstExtra + secondExtra)} ≤ factor * CrepSteps.steps (.seq a b) source)
  | some firstValue =>
    have pair : (some firstValue,middle) = (result,sourceFinal) := by simpa using sourceSeq
    have ⟨resultEq,finalEq⟩ := Prod.mk.inj pair
    subst result
    subst sourceFinal
    have firstNonerror : some firstValue ≠ some .error := nonerror
    obtain ⟨extra,targetResult,targetFinal,targetRun,finalState,finalMem,finalGlobals,
      finalCode,resultMap,finalLocals,bound⟩ :=
      first (some firstValue) middle target ctxt live sourceFirst firstNonerror stateRel memRel
        globalsRel codeRel tableGood localsRel
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
        simpa only [compileHOLExact] using (by rw [sourceCount]; simp only [Nat.mul_add, Nat.mul_one]; omega :
          LoopSteps.steps (.seq (compileHOLExact ctxt live a) (compileHOLExact ctxt live b))
            {target with clock := target.clock + extra} ≤ factor * CrepSteps.steps (.seq a b) source)

/-- Quantitative correctness for direct Crep programs, with no conjecture
assumptions about their subprograms. -/
theorem directProgram_correct_with_steps {width : Nat} [NeZero width] {σ : Type}
    {p : CrepProgHOL width} (shape : DirectProgram p) :
    ∀ source : CrepSemHOLState width σ, BoundPropertyAt p source := by
  induction shape with
  | leaf leaf =>
    intro source result sourceFinal target ctxt live run nonerror stateRel memRel globalsRel codeRel _ localsRel
    obtain ⟨extra,targetResult,targetFinal,he,hs,hm,hg,hc,hr,hl,steps⟩ :=
      directLeaf_correct_with_steps _ leaf source sourceFinal result target ctxt live run nonerror
        stateRel memRel globalsRel codeRel localsRel
    exact ⟨extra,targetResult,targetFinal,he,hs,hm,hg,hc,hr,hl,by omega⟩
  | returnNil =>
    intro source result sourceFinal target ctxt live run nonerror stateRel memRel globalsRel codeRel _ localsRel
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
    apply boundedSeq a b source 2 (by omega) (fun _ => True) ?_ (iha source) (fun middle _ => ihb middle)
    intro ctxt live target middle extra _ run
    exact LoopSteps.directProgram_steps_add_clock (compile_directProgram ha ctxt live)
      target middle none run (by simp) extra

end SteppedFlapjack.CrepToLoopSteps
