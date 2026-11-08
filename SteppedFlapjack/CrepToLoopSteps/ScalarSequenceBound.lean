import SteppedFlapjack.CrepToLoopSteps.ScalarUnmarked
import SteppedFlapjack.CrepToLoopSteps.ScalarIteBound
import SteppedFlapjack.CrepToLoopSteps.ConditionPrefix
import SteppedFlapjack.CrepToLoopSteps.ScalarDeclBound
import SteppedFlapjack.CrepToLoopSteps.ScalarLoopShape
import SteppedFlapjack.CrepToLoopSteps.ScalarClockShift
import SteppedFlapjack.CrepToLoopSteps.ExplicitFromVisits

/-! Composing quantitative simulations for recursive scalar sequences. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- A proved body simulation gives an outer loop simulation. This is the
induction step used after the body has been proved bottom-up. -/
private theorem scalarWhile_programBound {width : Nat} [NeZero width] {σ : Type}
    (condition : CrepExpHOL width) (conditionShape : CompiledScalar condition)
    (body : CrepProgHOL width) (bodyShape : ScalarProgram body)
    (ctxt : CrepToLoopContextExact) (live : NumSet) (bodyFactor : Nat)
    (bodyBound : @ProgramBound width _ σ body ctxt live bodyFactor) :
    @ProgramBound width _ σ (.while condition body) ctxt live
      (loopVisitWeight (compileHOLExact ctxt live (.while condition body)) *
        (LoopSteps.structuralWeight (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live condition).1) + 2*bodyFactor+3)) := by
  intro source sourceFinal result target run nonerror stateRel memRel globalsRel codeRel localsRel
  let p := CrepProgHOL.while condition body
  let code := compileHOLExact ctxt live p
  let prefixSize : Nat := LoopSteps.structuralWeight (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live condition).1)
  have bodySim := scalar_program_bodySimulation body bodyShape ctxt live bodyFactor bodyBound
  obtain ⟨extra,post,extraBound,targetRun,hs,hm,hg,hc,hl⟩ :=
    branchConditionWhile_bounded_clock condition conditionShape body (2*bodyFactor) source sourceFinal result target ctxt live
      (by simpa [Nat.mul_assoc] using bodySim) run nonerror stateRel memRel globalsRel codeRel localsRel
  have shape : ScalarProgram p := .while conditionShape bodyShape
  have loopShape := compile_scalar_program shape ctxt live
  have visits := scalarLoop_control_consumption_bound loopShape _ post (resultToLoop result) targetRun
  have consumed := CrepSteps.scalarProgram_clock_consumed shape source sourceFinal result run
  have initial := stateRel.2.2.1
  have final := hs.2.2.1
  have sourceClock := evalCrepSemHOLProgExact_clock_le source p
  rw [run] at sourceClock
  simp only at sourceClock
  change LoopSteps.steps code {target with clock := target.clock+extra} ≤
    loopVisitWeight code * (target.clock+extra-post.clock+1) at visits
  change source.clock - sourceFinal.clock ≤ CrepSteps.steps p source at consumed
  change extra ≤ (prefixSize+2*bodyFactor+2)*(CrepSteps.steps p source+1) at extraBound
  have delta : target.clock+extra-post.clock ≤ CrepSteps.steps p source+extra := by omega
  have clockBound : target.clock+extra-post.clock+1 ≤
      (prefixSize+2*bodyFactor+3)*(CrepSteps.steps p source+1) := by nlinarith
  refine ⟨extra,post,targetRun,hs,hm,hg,hc,hl,?_⟩
  change LoopSteps.steps code {target with clock := target.clock+extra} ≤
    (loopVisitWeight code*(prefixSize+2*bodyFactor+3))*(CrepSteps.steps p source+1)
  rw [Nat.mul_assoc]
  exact visits.trans (Nat.mul_le_mul_left _ clockBound)

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

/-- A syntax-derived factor for arbitrary nesting and sequencing of scalar loops. -/
noncomputable def scalarProgramFactor {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (live : NumSet) (p : CrepProgHOL width) : Nat :=
  if scalarNoWhile p then sizeOf (optimiseScalar (compileHOLExact ctxt live p))
  else match p with
    | .seq a b => 1 + scalarProgramFactor ctxt live a + scalarProgramFactor ctxt live b
    | .ite condition a b =>
        loopVisitWeight (compileHOLExact ctxt live p) *
          (LoopSteps.structuralWeight (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live condition).1) +
            2*max (scalarProgramFactor ctxt live a) (scalarProgramFactor ctxt live b)+2)
    | .dec name init body =>
        let tmp := (compileExpHOLExact ctxt (ctxt.vmax+1) live init).2.2.1
        loopVisitWeight (compileHOLExact ctxt live p) *
          (LoopSteps.structuralWeight (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live init).1) +
            2*scalarProgramFactor {ctxt with vars := ctxt.vars.updateEq (name,tmp), vmax := tmp}
              (sptInsert tmp () live) body+1)
    | .while condition body =>
        loopVisitWeight (compileHOLExact ctxt live p) *
          (LoopSteps.structuralWeight (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live condition).1) +
            2*scalarProgramFactor ctxt live body+3)
    | _ => sizeOf (compileHOLExact ctxt live p)

/-- On loop-free scalar programs the factor is exactly the optimized Loop code size. -/
theorem scalarProgramFactor_loopFree {width : Nat} [NeZero width] {p : CrepProgHOL width}
    (shape : ScalarProgram p) (free : scalarNoWhile p = true)
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    scalarProgramFactor ctxt live p = sizeOf (optimiseHOL (compileHOLExact ctxt live p)) := by
  have factor : scalarProgramFactor ctxt live p = sizeOf (optimiseScalar (compileHOLExact ctxt live p)) := by
    cases p <;> simp_all [scalarProgramFactor]
  rw [factor,optimiseScalar_eq (compile_scalar_program shape ctxt live)]

private theorem scalarBranch_programBound {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (shape : ScalarProgram p) (free : scalarNoWhile p = true)
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    @ProgramBound width _ σ p ctxt live (sizeOf (optimiseScalar (compileHOLExact ctxt live p))) := by
  intro source sourceFinal result target run nonerror stateRel memRel globalsRel codeRel localsRel
  obtain ⟨extra,out,final,eval,hs,hm,hg,hc,map,hl,steps,_⟩ :=
    branchProgram_correct_with_bounded_extra p (.scalar shape free) source sourceFinal result target ctxt live
      run nonerror stateRel memRel globalsRel codeRel localsRel
  subst out
  have static := LoopSteps.branchedProgram_structural_bound (compile_loopFreeCrep (.scalar shape free) ctxt live)
    {target with clock := target.clock+extra}
  have weightBound : LoopSteps.structuralWeight (compileHOLExact ctxt live p) ≤
      sizeOf (optimiseScalar (compileHOLExact ctxt live p)) := by
    simpa only [optimiseScalar_eq (compile_scalar_program shape ctxt live)] using
      scalarBranch_structural_le_output shape free ctxt live
  have enough : LoopSteps.structuralWeight (compileHOLExact ctxt live p) ≤
      sizeOf (optimiseScalar (compileHOLExact ctxt live p)) * (CrepSteps.steps p source+1) := by
    have := CrepSteps.steps_pos p source
    nlinarith
  exact ⟨extra,final,eval,hs,hm,hg,hc,hl,static.trans enough⟩

private theorem scalarProgram_programBound {width : Nat} [NeZero width] {σ : Type}
    {p : CrepProgHOL width} (shape : ScalarProgram p) (ctxt : CrepToLoopContextExact) (live : NumSet) :
    @ProgramBound width _ σ p ctxt live (scalarProgramFactor ctxt live p) := by
  induction shape generalizing ctxt live with
  | skip => simpa [scalarProgramFactor,scalarNoWhile] using scalarBranch_programBound (σ := σ) .skip .skip rfl ctxt live
  | «break» n => simpa [scalarProgramFactor,scalarNoWhile] using scalarBranch_programBound (σ := σ) (.break n) (.break n) rfl ctxt live
  | «continue» n => simpa [scalarProgramFactor,scalarNoWhile] using scalarBranch_programBound (σ := σ) (.continue n) (.continue n) rfl ctxt live
  | tick => simpa [scalarProgramFactor,scalarNoWhile] using scalarBranch_programBound (σ := σ) .tick .tick rfl ctxt live
  | @ret e h => simpa [scalarProgramFactor,scalarNoWhile] using scalarBranch_programBound (σ := σ) (.return [e]) (.ret h) rfl ctxt live
  | @assign n e h => simpa [scalarProgramFactor,scalarNoWhile] using scalarBranch_programBound (σ := σ) (.assign n e) (.assign n h) rfl ctxt live
  | @store a b ha hb => simpa [scalarProgramFactor,scalarNoWhile] using scalarBranch_programBound (σ := σ) (.store a b) (.store ha hb) rfl ctxt live
  | @seq a b ha hb iha ihb =>
    by_cases free : scalarNoWhile (.seq a b) = true
    · simpa [scalarProgramFactor,free] using scalarBranch_programBound (σ := σ) (.seq a b) (.seq ha hb) free ctxt live
    · simpa [scalarProgramFactor,free] using scalarSequence_programBound a b ha ctxt live _ _ (iha ctxt live) (ihb ctxt live)
  | @ite condition a b cond ha hb iha ihb =>
    by_cases free : scalarNoWhile (.ite condition a b) = true
    · simpa [scalarProgramFactor,free] using scalarBranch_programBound (σ := σ) (.ite condition a b) (.ite cond ha hb) free ctxt live
    · simpa [scalarProgramFactor,free] using scalarIte_programBound condition cond a b ha hb ctxt live _ _ (iha ctxt live) (ihb ctxt live)
  | @dec name init body initShape bodyShape ih =>
    by_cases free : scalarNoWhile (.dec name init body) = true
    · simpa [scalarProgramFactor,free] using scalarBranch_programBound (σ := σ) (.dec name init body) (.dec name initShape bodyShape) free ctxt live
    · simpa [scalarProgramFactor,free] using scalarDecl_programBound name init initShape body bodyShape ctxt live _ (ih _ _)
  | @«while» condition body cond bodyShape ih =>
    simpa [scalarProgramFactor,scalarNoWhile] using scalarWhile_programBound condition cond body bodyShape ctxt live _ (ih ctxt live)

/-- A completed scalar program executes as optimized Loop code with a
concrete clock and visit bound calculated from source syntax and a Crep limit. -/
theorem scalarProgram_explicit {σ : Type} (p : CrepProgHOL 64) (shape : ScalarProgram p)
    (ctxt : CrepToLoopContextExact) (live : NumSet)
    (source sourceFinal : CrepSemHOLState 64 σ) (result : Option (CrepResultHOLExact 64))
    (target : LoopSemStateFiniteExact 64 σ) (limit : Nat)
    (run : evalCrepSemHOLProgExact source p = (result,sourceFinal))
    (sourceBound : CrepSteps.steps p source ≤ limit) (complete : CompleteCrepResult result)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    let bound := scalarProgramFactor ctxt live p*(limit+1)
    let code := compileHOLExact ctxt live p
    ∃ post,
      evaluate (optimiseHOL code) {target with clock := target.clock+2*bound} = (resultToLoop result,post) ∧
      LoopSteps.steps (optimiseHOL code) {target with clock := target.clock+2*bound} ≤
        sizeOf (optimiseScalar code)*(2*bound+1) ∧
      crepToLoopStateRelExact sourceFinal {post with clock := sourceFinal.clock} ∧
      crepToLoopMemRelHOLExact sourceFinal.memory post.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals post.globals ∧
      crepToLoopCodeRelExact ctxt sourceFinal.code post.code := by
  let bound := scalarProgramFactor ctxt live p*(limit+1)
  let code := compileHOLExact ctxt live p
  have scalar := shape
  obtain ⟨extra,oldPost,oldRun,hs,hm,hg,hc,_,visits⟩ :=
    scalarProgram_programBound shape ctxt live source sourceFinal result target run
      (completeCrep_nonerror complete) stateRel memRel globalsRel codeRel localsRel
  have visitBound : LoopSteps.steps code {target with clock := target.clock+extra} ≤ bound := by
    exact visits.trans (Nat.mul_le_mul_left _ (by omega))
  have loopShape := compile_scalar_program scalar ctxt live
  have extraBound : extra ≤ 2*bound :=
    scalarLoop_extra_le_visits source sourceFinal result target oldPost ctxt live scalar extra bound
      run stateRel hs oldRun visitBound
  have final := hs.2.2.1
  have optimized := scalarLoop_explicit_optimised loopShape target oldPost (resultToLoop result)
    extra (2*bound) bound oldRun (completeCrep_loop complete) extraBound visitBound
  refine ⟨{oldPost with clock := oldPost.clock+(2*bound-extra)},optimized.1,optimized.2,?_,?_,?_,?_⟩
  · simpa [crepToLoopStateRelExact,final] using hs
  · simpa using hm
  · simpa using hg
  · simpa using hc
end SteppedFlapjack.CrepToLoopSteps
