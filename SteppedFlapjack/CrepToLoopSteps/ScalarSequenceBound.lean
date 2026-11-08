import SteppedFlapjack.CrepToLoopSteps.ConditionPrefix
import SteppedFlapjack.CrepToLoopSteps.DeclTerminal
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
      (sizeOf (compileHOLExact ctxt live (.while condition body)) *
        (sizeOf (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live condition).1) + 2*bodyFactor+3)) := by
  intro source sourceFinal result target run nonerror stateRel memRel globalsRel codeRel localsRel
  let p := CrepProgHOL.while condition body
  let code := compileHOLExact ctxt live p
  let prefixSize : Nat := sizeOf (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live condition).1)
  have bodySim := scalar_program_bodySimulation body bodyShape ctxt live bodyFactor bodyBound
  obtain ⟨extra,post,extraBound,targetRun,hs,hm,hg,hc,hl⟩ :=
    branchConditionWhile_bounded_clock condition conditionShape body (2*bodyFactor) source sourceFinal result target ctxt live
      (by simpa [Nat.mul_assoc] using bodySim) run nonerror stateRel memRel globalsRel codeRel localsRel
  have shape : ScalarProgram p := .while conditionShape bodyShape
  have loopShape := compile_scalar_program shape ctxt live
  have visits := scalarLoop_consumption_bound loopShape _ post (resultToLoop result) targetRun
  have consumed := CrepSteps.scalarProgram_clock_consumed shape source sourceFinal result run
  have initial := stateRel.2.2.1
  have final := hs.2.2.1
  have sourceClock := evalCrepSemHOLProgExact_clock_le source p
  rw [run] at sourceClock
  simp only at sourceClock
  change LoopSteps.steps code {target with clock := target.clock+extra} ≤
    sizeOf code * (target.clock+extra-post.clock+1) at visits
  change source.clock - sourceFinal.clock ≤ CrepSteps.steps p source at consumed
  change extra ≤ (prefixSize+2*bodyFactor+2)*(CrepSteps.steps p source+1) at extraBound
  have delta : target.clock+extra-post.clock ≤ CrepSteps.steps p source+extra := by omega
  have clockBound : target.clock+extra-post.clock+1 ≤
      (prefixSize+2*bodyFactor+3)*(CrepSteps.steps p source+1) := by nlinarith
  refine ⟨extra,post,targetRun,hs,hm,hg,hc,hl,?_⟩
  change LoopSteps.steps code {target with clock := target.clock+extra} ≤
    (sizeOf code*(prefixSize+2*bodyFactor+3))*(CrepSteps.steps p source+1)
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

/-- A direct declaration preserves the body simulation, including restored
locals, when its body proof is available at the extended context. -/
private theorem scalarDecl_programBound {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (init : CrepExpHOL width) (initShape : DirectExpression init)
    (body : CrepProgHOL width) (ctxt : CrepToLoopContextExact) (live : NumSet) (factor : Nat)
    (bodyBound : @ProgramBound width _ σ body
      {ctxt with vars := ctxt.vars.updateEq (name,ctxt.vmax+1), vmax := ctxt.vmax+1}
      (sptInsert (ctxt.vmax+1) () live) factor) :
    @ProgramBound width _ σ (.dec name init body) ctxt live (factor+4) := by
  intro source sourceFinal result target run nonerror stateRel memRel globalsRel codeRel localsRel
  let p := CrepProgHOL.dec name init body
  let code := compileHOLExact ctxt live p
  obtain ⟨extra,post,targetRun,hs,hm,hg,hc,bound⟩ :=
    directDecl_terminal_bound name init initShape body ctxt live factor bodyBound source sourceFinal result target
      run nonerror stateRel memRel globalsRel codeRel localsRel
  obtain ⟨other,out,otherPost,otherRun,_,_,_,_,map,otherLocals⟩ :=
    crepToLoop_ncompile_correct p source result sourceFinal target ctxt live
      ⟨run,nonerror,stateRel,memRel,globalsRel,codeRel,localsRel⟩
  subst out
  have locals : localsResultRel ctxt live result sourceFinal post := by
    by_cases nontimeout : resultToLoop result ≠ some .timeOut
    · let reserve := max extra other
      have lift₁ := evaluate_add_clock_eq code {target with clock := target.clock+extra}
        (resultToLoop result) post (reserve-extra) targetRun nontimeout
      have lift₂ := evaluate_add_clock_eq code {target with clock := target.clock+other}
        (resultToLoop result) otherPost (reserve-other) otherRun nontimeout
      have clk₁ : target.clock+extra+(reserve-extra) = target.clock+reserve := by dsimp [reserve]; omega
      have clk₂ : target.clock+other+(reserve-other) = target.clock+reserve := by dsimp [reserve]; omega
      have equalPost : {post with clock := post.clock+(reserve-extra)} =
          {otherPost with clock := otherPost.clock+(reserve-other)} := by
        have h₁ : evaluate code {target with clock := target.clock+reserve} =
            (resultToLoop result,{post with clock := post.clock+(reserve-extra)}) := by simpa [clk₁] using lift₁
        have h₂ : evaluate code {target with clock := target.clock+reserve} =
            (resultToLoop result,{otherPost with clock := otherPost.clock+(reserve-other)}) := by simpa [clk₂] using lift₂
        exact (Prod.mk.inj (h₁.symm.trans h₂)).2
      have localEq : post.locals = otherPost.locals := congrArg (fun s => s.locals) equalPost
      cases result with
      | none => simpa [localsResultRel,localEq] using otherLocals
      | some r => cases r <;> simp [localsResultRel,localEq] at otherLocals ⊢ <;> assumption
    · cases result with
      | none => simp [resultToLoop] at nontimeout
      | some r => cases r <;> simp_all [resultToLoop,localsResultRel]
  exact ⟨extra,post,targetRun,hs,hm,hg,hc,locals,bound⟩

/-- Scalar loops and sequences built around loop-free scalar leaves. -/
inductive ScalarLoopTree {width : Nat} [NeZero width] : CrepProgHOL width → Prop
  | branch {p} : ScalarProgram p → scalarNoWhile p = true → ScalarLoopTree p
  | seq {a b} : ScalarLoopTree a → ScalarLoopTree b → ScalarLoopTree (.seq a b)
  | dec (name) {init body} : DirectExpression init → ScalarLoopTree body → ScalarLoopTree (.dec name init body)
  | while {condition body} : CompiledScalar condition → ScalarLoopTree body → ScalarLoopTree (.while condition body)

theorem scalarLoopTree_scalar {width : Nat} [NeZero width] {p : CrepProgHOL width}
    (shape : ScalarLoopTree p) : ScalarProgram p := by
  induction shape with
  | branch shape _ => exact shape
  | seq _ _ a b => exact .seq a b
  | dec name init _ ih => exact .dec name (.direct init) ih
  | «while» h _ ih => exact .while h ih

/-- A syntax-derived factor for arbitrary nesting and sequencing of scalar loops. -/
noncomputable def scalarLoopTreeFactor {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (live : NumSet) (p : CrepProgHOL width) : Nat :=
  if scalarNoWhile p then sizeOf (compileHOLExact ctxt live p)
  else match p with
    | .seq a b => 1 + scalarLoopTreeFactor ctxt live a + scalarLoopTreeFactor ctxt live b
    | .dec name _ body => 4 + scalarLoopTreeFactor
        {ctxt with vars := ctxt.vars.updateEq (name,ctxt.vmax+1), vmax := ctxt.vmax+1}
        (sptInsert (ctxt.vmax+1) () live) body
    | .while condition body =>
        sizeOf (compileHOLExact ctxt live p) *
          (sizeOf (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live condition).1) +
            2*scalarLoopTreeFactor ctxt live body+3)
    | _ => sizeOf (compileHOLExact ctxt live p)

private theorem scalarBranch_programBound {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (shape : ScalarProgram p) (free : scalarNoWhile p = true)
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    @ProgramBound width _ σ p ctxt live (sizeOf (compileHOLExact ctxt live p)) := by
  intro source sourceFinal result target run nonerror stateRel memRel globalsRel codeRel localsRel
  obtain ⟨extra,out,final,eval,hs,hm,hg,hc,map,hl,steps,_⟩ :=
    branchProgram_correct_with_bounded_extra p (.scalar shape free) source sourceFinal result target ctxt live
      run nonerror stateRel memRel globalsRel codeRel localsRel
  subst out
  exact ⟨extra,final,eval,hs,hm,hg,hc,hl,steps.trans (Nat.mul_le_mul_left _ (by omega))⟩

private theorem scalarLoopTree_programBound {width : Nat} [NeZero width] {σ : Type}
    {p : CrepProgHOL width} (shape : ScalarLoopTree p) (ctxt : CrepToLoopContextExact) (live : NumSet) :
    @ProgramBound width _ σ p ctxt live (scalarLoopTreeFactor ctxt live p) := by
  induction shape generalizing ctxt live with
  | @branch p scalar free =>
    have factorEq : scalarLoopTreeFactor ctxt live p = sizeOf (compileHOLExact ctxt live p) := by
      cases p <;> simp_all [scalarLoopTreeFactor]
    rw [factorEq]
    exact scalarBranch_programBound (σ := σ) p scalar free ctxt live
  | @seq a b ha hb iha ihb =>
    by_cases free : scalarNoWhile (.seq a b) = true
    · simpa [scalarLoopTreeFactor,free] using
        scalarBranch_programBound (σ := σ) (.seq a b) (.seq (scalarLoopTree_scalar ha) (scalarLoopTree_scalar hb)) free ctxt live
    · simpa [scalarLoopTreeFactor,free] using
        scalarSequence_programBound a b (scalarLoopTree_scalar ha) ctxt live _ _ (iha ctxt live) (ihb ctxt live)
  | @dec name init body initShape bodyTree ih =>
    by_cases free : scalarNoWhile (.dec name init body) = true
    · simpa [scalarLoopTreeFactor,free] using
        scalarBranch_programBound (σ := σ) (.dec name init body)
          (.dec name (.direct initShape) (scalarLoopTree_scalar bodyTree)) free ctxt live
    · simpa [scalarLoopTreeFactor,free,Nat.add_comm] using
        scalarDecl_programBound name init initShape body ctxt live _ (ih _ _)
  | @«while» condition body cond bodyTree ih =>
    simpa [scalarLoopTreeFactor,scalarNoWhile] using
      scalarWhile_programBound condition cond body (scalarLoopTree_scalar bodyTree) ctxt live _ (ih ctxt live)

/-- A completed scalar loop tree executes as optimized Loop code with a
concrete clock and visit bound calculated from source syntax and a Crep limit. -/
theorem scalarLoopTree_explicit {σ : Type} (p : CrepProgHOL 64) (shape : ScalarLoopTree p)
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
    let bound := scalarLoopTreeFactor ctxt live p*(limit+1)
    let code := compileHOLExact ctxt live p
    ∃ post,
      evaluate (optimiseHOL code) {target with clock := target.clock+2*bound} = (resultToLoop result,post) ∧
      LoopSteps.steps (optimiseHOL code) {target with clock := target.clock+2*bound} ≤
        sizeOf (optimiseScalar code)*(2*bound+1) ∧
      crepToLoopStateRelExact sourceFinal {post with clock := sourceFinal.clock} ∧
      crepToLoopMemRelHOLExact sourceFinal.memory post.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals post.globals ∧
      crepToLoopCodeRelExact ctxt sourceFinal.code post.code := by
  let bound := scalarLoopTreeFactor ctxt live p*(limit+1)
  let code := compileHOLExact ctxt live p
  have scalar := scalarLoopTree_scalar shape
  obtain ⟨extra,oldPost,oldRun,hs,hm,hg,hc,_,visits⟩ :=
    scalarLoopTree_programBound shape ctxt live source sourceFinal result target run
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
