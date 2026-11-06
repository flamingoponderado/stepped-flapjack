import SteppedFlapjack.CrepToLoopSteps.Sequence

/-! Crep programs with direct expression assignments and sequences. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- Expressions compiled without auxiliary Loop statements. -/
inductive DirectExpression {width : Nat} [NeZero width] : CrepExpHOL width → Prop
  | baseAddr : DirectExpression .baseAddr
  | topAddr : DirectExpression .topAddr
  | const (v) : DirectExpression (.const v)
  | var (v) : DirectExpression (.var v)
  | loadGlob (v) : DirectExpression (.loadGlob v)
  | load {e} : DirectExpression e → DirectExpression (.load e)
  | shift (op) {a b} : DirectExpression a → DirectExpression b → DirectExpression (.shift op a b)
  | op (operator) {a b} : DirectExpression a → DirectExpression b → DirectExpression (.op operator [a,b])

/-- Direct expressions produce no auxiliary Loop code and preserve the
temporary and live-set parameters. -/
theorem directExpression_noCode {width : Nat} [NeZero width]
    {e : CrepExpHOL width} (shape : DirectExpression e)
    (ctxt : CrepToLoopContextExact) (tmp : Nat) (live : NumSet) :
    ∃ value, compileExpHOLExact ctxt tmp live e = ([],value,tmp,live) := by
  induction shape with
  | baseAddr => simp only [compileExpHOLExact]; exact ⟨_,rfl⟩
  | topAddr => simp only [compileExpHOLExact]; exact ⟨_,rfl⟩
  | const v => simp only [compileExpHOLExact]; exact ⟨_,rfl⟩
  | var v => simp only [compileExpHOLExact]; exact ⟨_,rfl⟩
  | loadGlob v => simp only [compileExpHOLExact]; exact ⟨_,rfl⟩
  | load he ih =>
    obtain ⟨value,h⟩ := ih
    exact ⟨.load value, by simp only [compileExpHOLExact,h]⟩
  | shift op ha hb iha ihb =>
    obtain ⟨va,ha⟩ := iha
    obtain ⟨vb,hb⟩ := ihb
    exact ⟨.shift op va vb, by simp only [compileExpHOLExact,ha,hb,List.nil_append]⟩
  | op operator ha hb iha ihb =>
    obtain ⟨va,ha⟩ := iha
    obtain ⟨vb,hb⟩ := ihb
    exact ⟨.op operator [va,vb], by
      simp only [compileExpHOLExact,compileExpsHOLExact,ha,hb,List.nil_append]⟩

/-- Direct control leaves, assignments of direct expressions, and sequences. -/
inductive ExprProgram {width : Nat} [NeZero width] : CrepProgHOL width → Prop
  | leaf {p} : DirectLeaf p → ExprProgram p
  | returnNil : ExprProgram (.return [])
  | returnOne {e} : DirectExpression e → ExprProgram (.return [e])
  | assign (name) {e} : DirectExpression e → ExprProgram (.assign name e)
  | storeGlob (name) {e} : DirectExpression e → ExprProgram (.storeGlob name e)
  | store {dst src} : DirectExpression dst → DirectExpression src → ExprProgram (.store dst src)
  | seq {a b} : ExprProgram a → ExprProgram b → ExprProgram (.seq a b)

/-- Compiled programs have clock-stable Loop counts. -/
theorem compile_exprProgram {width : Nat} [NeZero width]
    {p : CrepProgHOL width} (shape : ExprProgram p)
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    LoopToWordSteps.DirectProgram (compileHOLExact ctxt live p) := by
  induction shape with
  | leaf leaf => cases leaf <;> simp only [compileHOLExact] <;> exact .leaf (by constructor)
  | returnNil =>
    simp only [compileHOLExact, compileExpsHOLExact, genTemps, List.nil_append]
    exact .seq (.leaf (.ret _)) (.leaf .skip)
  | returnOne expr =>
    obtain ⟨value,h⟩ := directExpression_noCode expr ctxt (ctxt.vmax + 1) live
    simp [compileHOLExact,compileExpsHOLExact,h,genTemps,loopNestedSeqHOL]
    exact .seq (.leaf (.assign _ _)) (.seq (.leaf (.ret _)) (.leaf .skip))
  | assign name expr =>
    simp only [compileHOLExact]
    cases found : ctxt.vars.lookup name with
    | none => exact .leaf .skip
    | some mapped =>
      obtain ⟨value,h⟩ := directExpression_noCode expr ctxt (ctxt.vmax + 1) live
      simp only [h,List.nil_append,loopNestedSeqHOL]
      exact .seq (.leaf (.assign _ _)) (.leaf .skip)
  | storeGlob name expr =>
    obtain ⟨value,h⟩ := directExpression_noCode expr ctxt (ctxt.vmax + 1) live
    simp only [compileHOLExact,h,List.nil_append,loopNestedSeqHOL]
    exact .seq (.leaf (.setGlobal _ _)) (.leaf .skip)
  | store dst src =>
    obtain ⟨vd,hd⟩ := directExpression_noCode dst ctxt (ctxt.vmax + 1) live
    obtain ⟨vs,hs⟩ := directExpression_noCode src ctxt (ctxt.vmax + 1) live
    simp only [compileHOLExact,hd,hs,List.nil_append,loopNestedSeqHOL]
    exact .seq (.leaf (.assign _ _)) (.seq (.leaf (.store _ _)) (.leaf .skip))
  | seq ha hb iha ihb => simpa only [compileHOLExact] using LoopToWordSteps.DirectProgram.seq iha ihb

/-- Semantic correctness and a fivefold count bound at a fixed source state. -/
def ExprBoundPropertyAt {width : Nat} [NeZero width] {σ : Type}
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
        5 * CrepSteps.steps p source

/-- Sequential composition preserves the quantitative correctness property. -/
theorem exprBoundedSeq {width : Nat} [NeZero width] {σ : Type}
    (a b : CrepProgHOL width) (shapeA : ExprProgram a)
    (source : CrepSemHOLState width σ)
    (first : ExprBoundPropertyAt a source)
    (second : ∀ middle : CrepSemHOLState width σ, ExprBoundPropertyAt b middle) : ExprBoundPropertyAt (.seq a b) source := by
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
    have stepLift := LoopSteps.directProgram_steps_add_clock (compile_exprProgram shapeA ctxt live)
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
          {target with clock := target.clock + (firstExtra + secondExtra)} ≤ 5 * CrepSteps.steps (.seq a b) source)
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
            {target with clock := target.clock + extra} ≤ 5 * CrepSteps.steps (.seq a b) source)

/-- Two direct statements and the trailing skip cost at most five visits. -/
theorem twoLeaves_steps_bound {width : Nat} [NeZero width] {σ : Type}
    (a b : HolLoopProg width) (s : LoopSemStateFiniteExact width σ)
    (ha : match a with | .seq _ _ | .ite _ _ _ _ _ _ | .mark _ | .loop _ _ _ | .call _ _ _ _ => false | _ => true)
    (hb : match b with | .seq _ _ | .ite _ _ _ _ _ _ | .mark _ | .loop _ _ _ | .call _ _ _ _ => false | _ => true) :
    LoopSteps.steps (.seq a (.seq b .skip)) s ≤ 5 := by
  rw [LoopSteps.steps_seq,LoopSteps.steps_leaf a s ha]
  rcases evaluate a s with ⟨res,t⟩
  cases res with
  | some r => simp only; omega
  | none =>
    simp only [LoopSteps.steps_seq,LoopSteps.steps_leaf b t hb]
    rcases evaluate b t with ⟨res',u⟩
    cases res' <;> simp [LoopSteps.steps_leaf] <;> omega

/-- All subprogram bounds are proved by structural induction. -/
theorem exprProgram_correct_with_steps {width : Nat} [NeZero width] {σ : Type}
    {p : CrepProgHOL width} (shape : ExprProgram p) :
    ∀ source : CrepSemHOLState width σ, ExprBoundPropertyAt p source := by
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
  | @returnOne e expr =>
    intro source result sourceFinal target ctxt live run nonerror stateRel memRel globalsRel codeRel localsRel
    obtain ⟨extra,targetResult,targetFinal,he,hs,hm,hg,hc,hr,hl⟩ :=
      crepToLoopNcompileCorrectOf (.return [e]) source result sourceFinal target ctxt live run nonerror
        stateRel memRel globalsRel codeRel localsRel
    refine ⟨extra,targetResult,targetFinal,he,hs,hm,hg,hc,hr,hl,?_⟩
    rw [CrepSteps.steps_leaf _ _ (by rfl)]
    obtain ⟨value,h⟩ := directExpression_noCode expr ctxt (ctxt.vmax + 1) live
    simp only [compileHOLExact,compileExpsHOLExact,h,List.nil_append,genTemps]
    exact twoLeaves_steps_bound _ _ _ (by rfl) (by rfl)
  | @assign name e expr =>
    intro source result sourceFinal target ctxt live run nonerror stateRel memRel globalsRel codeRel localsRel
    obtain ⟨extra,targetResult,targetFinal,he,hs,hm,hg,hc,hr,hl⟩ :=
      crepToLoopNcompileCorrectOf (.assign name e) source result sourceFinal target ctxt live run nonerror
        stateRel memRel globalsRel codeRel localsRel
    refine ⟨extra,targetResult,targetFinal,he,hs,hm,hg,hc,hr,hl,?_⟩
    have sourceOne : CrepSteps.steps (.assign name e) source = 1 := CrepSteps.steps_leaf _ _ (by rfl)
    rw [sourceOne]
    simp only [compileHOLExact]
    cases found : ctxt.vars.lookup name with
    | none =>
      rw [LoopSteps.steps_leaf _ _ (by rfl)]
      omega
    | some mapped =>
      obtain ⟨value,h⟩ := directExpression_noCode expr ctxt (ctxt.vmax + 1) live
      simp only [h,List.nil_append,loopNestedSeqHOL]
      rw [LoopSteps.steps_seq]
      rw [LoopSteps.steps_leaf _ _ (by rfl)]
      split <;> try omega
      rename_i out st run'
      cases out <;> simp [LoopSteps.steps_leaf] <;> omega
  | @storeGlob name e expr =>
    intro source result sourceFinal target ctxt live run nonerror stateRel memRel globalsRel codeRel localsRel
    obtain ⟨extra,targetResult,targetFinal,he,hs,hm,hg,hc,hr,hl⟩ :=
      crepToLoopNcompileCorrectOf (.storeGlob name e) source result sourceFinal target ctxt live run nonerror
        stateRel memRel globalsRel codeRel localsRel
    refine ⟨extra,targetResult,targetFinal,he,hs,hm,hg,hc,hr,hl,?_⟩
    rw [CrepSteps.steps_leaf _ _ (by rfl)]
    obtain ⟨value,h⟩ := directExpression_noCode expr ctxt (ctxt.vmax + 1) live
    simp only [compileHOLExact,h,List.nil_append,loopNestedSeqHOL]
    rw [LoopSteps.steps_seq,LoopSteps.steps_leaf _ _ (by rfl)]
    split <;> try omega
    rename_i out st run'
    cases out <;> simp [LoopSteps.steps_leaf] <;> omega
  | @store dst src hdst hsrc =>
    intro source result sourceFinal target ctxt live run nonerror stateRel memRel globalsRel codeRel localsRel
    obtain ⟨extra,targetResult,targetFinal,he,hs,hm,hg,hc,hr,hl⟩ :=
      crepToLoopNcompileCorrectOf (.store dst src) source result sourceFinal target ctxt live run nonerror
        stateRel memRel globalsRel codeRel localsRel
    refine ⟨extra,targetResult,targetFinal,he,hs,hm,hg,hc,hr,hl,?_⟩
    rw [CrepSteps.steps_leaf _ _ (by rfl)]
    obtain ⟨vd,hd⟩ := directExpression_noCode hdst ctxt (ctxt.vmax + 1) live
    obtain ⟨vs,hs⟩ := directExpression_noCode hsrc ctxt (ctxt.vmax + 1) live
    simp only [compileHOLExact,hd,hs,List.nil_append,loopNestedSeqHOL]
    exact twoLeaves_steps_bound _ _ _ (by rfl) (by rfl)
  | @seq a b ha hb iha ihb =>
    intro source
    exact exprBoundedSeq a b ha source (iha source) ihb

end SteppedFlapjack.CrepToLoopSteps
