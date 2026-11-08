import SteppedFlapjack.CrepToLoopSteps.ConditionPrefix
import SteppedFlapjack.CrepToLoopSteps.ScalarLoopShape
import SteppedFlapjack.CrepToLoopSteps.ScalarClockShift
import SteppedFlapjack.CrepToLoopSteps.ExplicitFromVisits

/-! Composing quantitative simulations for recursive scalar sequences. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- Two already-proved scalar simulations compose even when the first part
contains loops. The factor is calculated from the two component factors. -/
private theorem scalarSequence_programBound {width : Nat} [NeZero width] {σ : Type}
    (a b : CrepProgHOL width) (aShape : ScalarProgram a)
    (ctxt : CrepToLoopContextExact) (live : NumSet) (aFactor bFactor : Nat)
    (first : @ProgramBound width _ σ a ctxt live aFactor)
    (second : @ProgramBound width _ σ b ctxt live bFactor) :
    @ProgramBound width _ σ (.seq a b) ctxt live (1+aFactor+bFactor) := by
  intro source sourceFinal result target run nonerror stateRel memRel globalsRel codeRel localsRel
  have seqRun := run
  rw [evalCrepSemHOLProgExact_seq_holShape] at seqRun
  rcases firstRun : evalCrepSemHOLProgExact source a with ⟨firstResult,middle⟩
  rw [firstRun] at seqRun
  have sourceCount := CrepSteps.steps_seq a b source
  rw [firstRun] at sourceCount
  have firstNonerror : firstResult ≠ some .error := by
    intro bad
    rw [bad] at seqRun
    simp only [Option.some_ne_none,if_false,Prod.mk.injEq] at seqRun
    exact nonerror seqRun.1.symm
  obtain ⟨firstExtra,firstTarget,firstTargetRun,firstState,firstMem,firstGlobals,
    firstCode,firstLocals,firstBound⟩ :=
    first source middle firstResult target firstRun firstNonerror stateRel memRel globalsRel codeRel localsRel
  cases firstResult with
  | none =>
    simp only at seqRun firstTargetRun firstLocals
    obtain ⟨secondExtra,final,secondRun,secondState,secondMem,secondGlobals,secondCode,secondLocals,secondBound⟩ :=
      second middle sourceFinal result firstTarget seqRun nonerror firstState firstMem firstGlobals firstCode firstLocals
    have lift := evaluate_add_clock_eq (compileHOLExact ctxt live a)
      {target with clock := target.clock+firstExtra} none firstTarget secondExtra firstTargetRun (by simp)
    have firstLift : evaluate (compileHOLExact ctxt live a)
        {target with clock := target.clock+(firstExtra+secondExtra)} =
          (none,{firstTarget with clock := firstTarget.clock+secondExtra}) := by
      simpa [Nat.add_assoc] using lift
    have countLift := scalarLoop_steps_add_clock (compile_scalar_program aShape ctxt live)
      {target with clock := target.clock+firstExtra} firstTarget none firstTargetRun (by simp) secondExtra
    have firstStepLift : LoopSteps.steps (compileHOLExact ctxt live a)
        {target with clock := target.clock+(firstExtra+secondExtra)} =
          LoopSteps.steps (compileHOLExact ctxt live a) {target with clock := target.clock+firstExtra} := by
      simpa [Nat.add_assoc] using countLift
    have count := LoopSteps.steps_seq (compileHOLExact ctxt live a) (compileHOLExact ctxt live b)
      {target with clock := target.clock+(firstExtra+secondExtra)}
    rw [firstLift,firstStepLift] at count
    refine ⟨firstExtra+secondExtra,final,?_,secondState,secondMem,secondGlobals,secondCode,secondLocals,?_⟩
    · rw [compileHOLExact,evaluate_seq,firstLift]
      exact secondRun
    · simp only at sourceCount count
      rw [compileHOLExact]
      nlinarith
  | some r =>
    simp only [Option.some_ne_none,if_false,Prod.mk.injEq] at seqRun
    obtain ⟨rfl,rfl⟩ := seqRun
    have targetSome : resultToLoop (some r) ≠ none := by cases r <;> simp [resultToLoop]
    refine ⟨firstExtra,firstTarget,?_,firstState,firstMem,firstGlobals,firstCode,firstLocals,?_⟩
    · rw [compileHOLExact,evaluate_seq,firstTargetRun]
      cases h : resultToLoop (some r) with
      | none => exact (targetSome h).elim
      | some v => rfl
    · have count := LoopSteps.steps_seq (compileHOLExact ctxt live a) (compileHOLExact ctxt live b)
        {target with clock := target.clock+firstExtra}
      rw [firstTargetRun] at count
      cases h : resultToLoop (some r) with
      | none => exact (targetSome h).elim
      | some v =>
        simp only [h] at count
        simp only at sourceCount count
        rw [compileHOLExact]
        nlinarith
/-- Two consecutive scalar loops have a proved compositional visit bound. -/
private theorem twoScalarLoops_programBound {width : Nat} [NeZero width] {σ : Type}
    (c₁ c₂ : CrepExpHOL width) (body₁ tail₁ body₂ tail₂ : CrepProgHOL width)
    (c₁Shape : CompiledScalar c₁) (c₂Shape : CompiledScalar c₂)
    (body₁Shape : ScalarProgram body₁) (body₁Free : scalarNoWhile body₁ = true)
    (tail₁Shape : ScalarProgram tail₁) (tail₁Free : scalarNoWhile tail₁ = true)
    (body₂Shape : ScalarProgram body₂) (body₂Free : scalarNoWhile body₂ = true)
    (tail₂Shape : ScalarProgram tail₂) (tail₂Free : scalarNoWhile tail₂ = true)
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    let f₁ := 1 + (1 + sizeOf (compileHOLExact ctxt live (.while c₁ body₁))) *
      (sizeOf (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live c₁).1) + sizeOf (compileHOLExact ctxt live body₁)+3) +
        sizeOf (compileHOLExact ctxt live tail₁)
    let f₂ := 1 + (1 + sizeOf (compileHOLExact ctxt live (.while c₂ body₂))) *
      (sizeOf (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live c₂).1) + sizeOf (compileHOLExact ctxt live body₂)+3) +
        sizeOf (compileHOLExact ctxt live tail₂)
    @ProgramBound width _ σ (.seq (.seq (.while c₁ body₁) tail₁) (.seq (.while c₂ body₂) tail₂)) ctxt live (1+f₁+f₂) := by
  exact scalarSequence_programBound _ _ (.seq (.while c₁Shape body₁Shape) tail₁Shape) ctxt live _ _
    (conditionWhileThenBranch_programBound c₁ c₁Shape body₁ tail₁ (.scalar body₁Shape body₁Free) (.scalar tail₁Shape tail₁Free) ctxt live)
    (conditionWhileThenBranch_programBound c₂ c₂Shape body₂ tail₂ (.scalar body₂Shape body₂Free) (.scalar tail₂Shape tail₂Free) ctxt live)

/-- Two consecutive scalar loops execute as optimized Loop code at a clock
calculated from their source visit limit and compiled syntax. -/
theorem twoScalarLoops_explicit {σ : Type}
    (c₁ c₂ : CrepExpHOL 64) (body₁ tail₁ body₂ tail₂ : CrepProgHOL 64)
    (c₁Shape : CompiledScalar c₁) (c₂Shape : CompiledScalar c₂)
    (body₁Shape : ScalarProgram body₁) (body₁Free : scalarNoWhile body₁ = true)
    (tail₁Shape : ScalarProgram tail₁) (tail₁Free : scalarNoWhile tail₁ = true)
    (body₂Shape : ScalarProgram body₂) (body₂Free : scalarNoWhile body₂ = true)
    (tail₂Shape : ScalarProgram tail₂) (tail₂Free : scalarNoWhile tail₂ = true)
    (ctxt : CrepToLoopContextExact) (live : NumSet)
    (source sourceFinal : CrepSemHOLState 64 σ) (result : Option (CrepResultHOLExact 64))
    (target : LoopSemStateFiniteExact 64 σ) (limit : Nat)
    (run : evalCrepSemHOLProgExact source (.seq (.seq (.while c₁ body₁) tail₁) (.seq (.while c₂ body₂) tail₂)) = (result,sourceFinal))
    (sourceBound : CrepSteps.steps (.seq (.seq (.while c₁ body₁) tail₁) (.seq (.while c₂ body₂) tail₂)) source ≤ limit)
    (complete : CompleteCrepResult result)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    let p := CrepProgHOL.seq (.seq (.while c₁ body₁) tail₁) (.seq (.while c₂ body₂) tail₂)
    let f₁ := 1 + (1 + sizeOf (compileHOLExact ctxt live (.while c₁ body₁))) *
      (sizeOf (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live c₁).1) + sizeOf (compileHOLExact ctxt live body₁)+3) +
        sizeOf (compileHOLExact ctxt live tail₁)
    let f₂ := 1 + (1 + sizeOf (compileHOLExact ctxt live (.while c₂ body₂))) *
      (sizeOf (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live c₂).1) + sizeOf (compileHOLExact ctxt live body₂)+3) +
        sizeOf (compileHOLExact ctxt live tail₂)
    let bound := (1+f₁+f₂)*(limit+1)
    let code := compileHOLExact ctxt live p
    ∃ post,
      evaluate (optimiseHOL code) {target with clock := target.clock+2*bound} = (resultToLoop result,post) ∧
      LoopSteps.steps (optimiseHOL code) {target with clock := target.clock+2*bound} ≤
        sizeOf (optimiseScalar code)*(2*bound+1) ∧
      crepToLoopStateRelExact sourceFinal {post with clock := sourceFinal.clock} ∧
      crepToLoopMemRelHOLExact sourceFinal.memory post.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals post.globals ∧
      crepToLoopCodeRelExact ctxt sourceFinal.code post.code := by
  let p := CrepProgHOL.seq (.seq (.while c₁ body₁) tail₁) (.seq (.while c₂ body₂) tail₂)
  let f₁ := 1 + (1 + sizeOf (compileHOLExact ctxt live (.while c₁ body₁))) *
    (sizeOf (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live c₁).1) + sizeOf (compileHOLExact ctxt live body₁)+3) +
      sizeOf (compileHOLExact ctxt live tail₁)
  let f₂ := 1 + (1 + sizeOf (compileHOLExact ctxt live (.while c₂ body₂))) *
    (sizeOf (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live c₂).1) + sizeOf (compileHOLExact ctxt live body₂)+3) +
      sizeOf (compileHOLExact ctxt live tail₂)
  let bound := (1+f₁+f₂)*(limit+1)
  let code := compileHOLExact ctxt live p
  have shape : ScalarProgram p := .seq (.seq (.while c₁Shape body₁Shape) tail₁Shape) (.seq (.while c₂Shape body₂Shape) tail₂Shape)
  obtain ⟨extra,oldPost,oldRun,hs,hm,hg,hc,_,visits⟩ :=
    twoScalarLoops_programBound c₁ c₂ body₁ tail₁ body₂ tail₂ c₁Shape c₂Shape body₁Shape body₁Free
      tail₁Shape tail₁Free body₂Shape body₂Free tail₂Shape tail₂Free ctxt live
      source sourceFinal result target run (completeCrep_nonerror complete) stateRel memRel globalsRel codeRel localsRel
  change CrepSteps.steps p source ≤ limit at sourceBound
  change LoopSteps.steps code {target with clock := target.clock+extra} ≤ (1+f₁+f₂)*(CrepSteps.steps p source+1) at visits
  have visitBound : LoopSteps.steps code {target with clock := target.clock+extra} ≤ bound := by
    exact visits.trans (Nat.mul_le_mul_left _ (by omega))
  have loopShape := compile_scalar_program shape ctxt live
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
