import SteppedFlapjack.CrepToLoopSteps.ConditionInduction
import SteppedFlapjack.CrepToLoopSteps.ResultLocals
import SteppedFlapjack.CrepToLoopSteps.ScalarPrefixOutput
import SteppedFlapjack.LoopLiveSteps.TailEntryCode

/-! Compositional compiler clock bounds, independent of Loop visit bounds. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact SteppedFlapjack.LoopToWordSteps Flapjack.Compiler.Encoders.Asm
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- Run at the calculated clock budget, eliminating the intermediate padding witness. -/
theorem BodySimulationAt.explicit {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (ctxt : CrepToLoopContextExact) (live : NumSet)
    (source sourceFinal : CrepSemHOLState width σ) (result : Option (CrepResultHOLExact width))
    (target : LoopSemStateFiniteExact width σ) (cost : Nat → Nat) (budget : Nat)
    (tableOk : Spt (List Nat × HolLoopProg width) → Prop)
    (sim : BodySimulationAt p ctxt live source cost tableOk)
    (run : evalCrepSemHOLProgExact source p = (result,sourceFinal))
    (nonerror : result ≠ some .error) (nonTimeout : resultToLoop result ≠ some .timeOut)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (table : tableOk target.code)
    (budgetBound : cost (CrepSteps.steps p source) ≤ budget)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    ∃ post, evaluate (compileHOLExact ctxt live p)
        {target with clock := target.clock + budget} = (resultToLoop result,post) ∧
      crepToLoopStateRelExact sourceFinal {post with clock := sourceFinal.clock} ∧
      crepToLoopMemRelHOLExact sourceFinal.memory post.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals post.globals ∧
      crepToLoopCodeRelExact ctxt sourceFinal.code post.code ∧
      localsResultRel ctxt live result sourceFinal post := by
  obtain ⟨extra,out,oldPost,oldRun,hs,hm,hg,hc,outEq,hl,bound⟩ :=
    sim sourceFinal result target run nonerror stateRel memRel globalsRel codeRel table localsRel
  subst out
  let delta := budget - extra
  have shifted := evaluate_add_clock_eq _ _ _ oldPost delta oldRun nonTimeout
  have clockEq : target.clock + extra + delta = target.clock + budget := by
    dsimp [delta]
    omega
  refine ⟨{oldPost with clock := oldPost.clock+delta},?_,?_,?_,?_,?_,?_⟩
  · simpa [clockEq] using shifted
  · have finalClock := hs.2.2.1
    simpa [crepToLoopStateRelExact,finalClock] using hs
  · simpa using hm
  · simpa using hg
  · simpa using hc
  · simpa [localsResultRel] using hl

/-- Compose explicit padding budgets at the source states reached in execution. -/
theorem sequence_clock_at {width : Nat} [NeZero width] {σ : Type}
    (a b : CrepProgHOL width) (ctxt : CrepToLoopContextExact) (live : NumSet)
    (source : CrepSemHOLState width σ) (af bf : Nat)
    (tableOk : Spt (List Nat × HolLoopProg width) → Prop)
    (first : BodySimulationAt a ctxt live source (fun n => af*(n+1)) tableOk)
    (second : ∀ middle, evalCrepSemHOLProgExact source a = (none,middle) →
      BodySimulationAt b ctxt live middle (fun n => bf*(n+1)) tableOk) :
    BodySimulationAt (.seq a b) ctxt live source (fun n => (af+bf)*(n+1)) tableOk := by
  intro sourceFinal result target run nonerror stateRel memRel globalsRel codeRel tableGood localsRel
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
  obtain ⟨firstExtra,firstOut,firstTarget,firstTargetRun,firstState,firstMem,firstGlobals,
    firstCode,firstOutEq,firstLocals,firstBound⟩ :=
    first middle firstResult target firstRun firstNonerror stateRel memRel globalsRel codeRel tableGood localsRel
  subst firstOut
  cases firstResult with
  | none =>
    simp only at seqRun firstTargetRun firstLocals
    have codeSame : firstTarget.code = target.code := by
      have h := SteppedFlapjack.LoopLiveSteps.evaluate_code (compileHOLExact ctxt live a)
        {target with clock := target.clock + firstExtra} firstTarget none firstTargetRun
      exact h
    have firstTable : tableOk firstTarget.code := by rw [codeSame]; exact tableGood
    obtain ⟨secondExtra,secondOut,final,secondRun,secondState,secondMem,secondGlobals,secondCode,
      secondOutEq,secondLocals,secondBound⟩ :=
      second middle firstRun sourceFinal result firstTarget seqRun nonerror firstState firstMem firstGlobals firstCode firstTable firstLocals
    subst secondOut
    have lift := evaluate_add_clock_eq (compileHOLExact ctxt live a)
      {target with clock := target.clock+firstExtra} none firstTarget secondExtra firstTargetRun (by simp)
    have firstLift : evaluate (compileHOLExact ctxt live a)
        {target with clock := target.clock+(firstExtra+secondExtra)} =
          (none,{firstTarget with clock := firstTarget.clock+secondExtra}) := by
      simpa [Nat.add_assoc] using lift
    refine ⟨firstExtra+secondExtra,resultToLoop result,final,?_,secondState,secondMem,secondGlobals,secondCode,rfl,secondLocals,?_⟩
    · rw [compileHOLExact,evaluate_seq,firstLift]
      exact secondRun
    · simp only at sourceCount
      nlinarith
  | some r =>
    simp only [Option.some_ne_none,if_false,Prod.mk.injEq] at seqRun
    obtain ⟨rfl,rfl⟩ := seqRun
    have targetSome : resultToLoop (some r) ≠ none := by cases r <;> simp [resultToLoop]
    refine ⟨firstExtra,resultToLoop (some r),firstTarget,?_,firstState,firstMem,firstGlobals,firstCode,rfl,firstLocals,?_⟩
    · rw [compileHOLExact,evaluate_seq,firstTargetRun]
      cases h : resultToLoop (some r) with
      | none => exact (targetSome h).elim
      | some v => rfl
    · simp only at sourceCount
      nlinarith

/-- Compose extra-clock bounds without converting them to visit bounds. -/
theorem scalarSequence_clock {width : Nat} [NeZero width] {σ : Type}
    (a b : CrepProgHOL width) (ctxt : CrepToLoopContextExact) (live : NumSet)
    (af bf : Nat)
    (first : @BodySimulation width _ σ a ctxt live (fun n => af*(n+1)))
    (second : @BodySimulation width _ σ b ctxt live (fun n => bf*(n+1))) :
    @BodySimulation width _ σ (.seq a b) ctxt live (fun n => (af+bf)*(n+1)) := by
  intro source sourceFinal result target run nonerror stateRel memRel globalsRel codeRel localsRel
  have firstAt := BodySimulation.at a ctxt live (fun n => af*(n+1)) source (fun _ => True) first
  have secondAt : ∀ middle, evalCrepSemHOLProgExact source a = (none,middle) →
      BodySimulationAt b ctxt live middle (fun n => bf*(n+1)) (fun _ => True) := by
    intro middle _
    exact BodySimulation.at b ctxt live (fun n => bf*(n+1)) middle (fun _ => True) second
  exact sequence_clock_at a b ctxt live source af bf (fun _ => True) firstAt secondAt
    sourceFinal result target run nonerror stateRel memRel globalsRel codeRel trivial localsRel

theorem clockSimulation_mono {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (ctxt : CrepToLoopContextExact) (live : NumSet) (a b : Nat)
    (h : @BodySimulation width _ σ p ctxt live (fun n => a*(n+1))) (le : a ≤ b) :
    @BodySimulation width _ σ p ctxt live (fun n => b*(n+1)) := by
  intro source sourceFinal result target run nonerror stateRel memRel globalsRel codeRel localsRel
  obtain ⟨extra,out,post,ev,hs,hm,hg,hc,hr,hl,bound⟩ := h source sourceFinal result target run nonerror stateRel memRel globalsRel codeRel localsRel
  exact ⟨extra,out,post,ev,hs,hm,hg,hc,hr,hl,bound.trans (Nat.mul_le_mul_right _ le)⟩

/-- A conditional is bounded once both of its branches have been proved. -/
theorem scalarIte_clock {width : Nat} [NeZero width] {σ : Type}
    (condition : CrepExpHOL width) (conditionShape : CompiledScalar condition)
    (yes no : CrepProgHOL width)
    (ctxt : CrepToLoopContextExact) (live : NumSet) (yesFactor noFactor : Nat)
    (yesBound : @BodySimulation width _ σ yes ctxt live (fun n => yesFactor*(n+1)))
    (noBound : @BodySimulation width _ σ no ctxt live (fun n => noFactor*(n+1))) :
    @BodySimulation width _ σ (.ite condition yes no) ctxt live
      (fun n => (LoopSteps.structuralWeight (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live condition).1) +
        max yesFactor noFactor+1)*(n+1)) := by
  classical
  intro source sourceFinal result target run nonerror stateRel memRel globalsRel codeRel localsRel
  let p := CrepProgHOL.ite condition yes no
  let factor := max yesFactor noFactor
  let prefixSize := LoopSteps.structuralWeight (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live condition).1)
  let code := compileHOLExact ctxt live p
  rw [evalCrepSemHOLProgExact_ite_holShape] at run
  rcases guard : evalCrepSemHOLExp source condition with _ | ⟨w⟩
  · simp only [guard,Prod.mk.injEq] at run
    exact absurd run.1.symm nonerror
  · cases w with
    | word w =>
      simp only [guard] at run
      rcases compiled : compileExpHOLExact ctxt (ctxt.vmax+1) live condition with ⟨np,value,tmp,outLive⟩
      obtain ⟨ck,st,exprRun,exprValue,exprState,exprMem,exprGlobals,exprCode,exprLocals⟩ :=
        crepToLoop_comp_exp_preserves_eval source condition (.word w) target ctxt (ctxt.vmax+1) live np value tmp outLive
          ⟨guard,stateRel,memRel,globalsRel,codeRel,localsRel,compiled,by omega⟩
      have prefixBound := condition_extraClock_bound source target st np ck (by
        intro q hq
        obtain ⟨_,_,_,_,hc,hbranch,_⟩ := condition_prefix_shape conditionShape ctxt (ctxt.vmax+1) live
        rw [compiled] at hc
        cases hc
        exact hbranch q hq) stateRel exprRun exprState
      obtain ⟨hok,htmp,hlive⟩ := compile_exp_out_rel ctxt (ctxt.vmax+1) live condition np value tmp outLive compiled
      have hsub : ∀ k, sptDomain live k → sptDomain outLive k :=
        fun k hk => hlive ▸ cut_sets_union_domain_subset _ live hok k hk
      let branchTarget := setVar tmp (.word w) st
      have branchLocals : crepToLoopLocalsRelExact ctxt live source.locals branchTarget.locals := by
        exact condition_locals_rel_insert_of ctxt live outLive source.locals target.locals st.locals localsRel exprLocals hsub tmp (by omega) _
      let chosen := if w ≠ 0 then yes else no
      have chosenBound : @BodySimulation width _ σ chosen ctxt live (fun n => factor*(n+1)) := by
        dsimp [chosen,factor]
        split
        · exact clockSimulation_mono yes ctxt live yesFactor _ yesBound (Nat.le_max_left _ _)
        · exact clockSimulation_mono no ctxt live noFactor _ noBound (Nat.le_max_right _ _)
      have chosenRun : evalCrepSemHOLProgExact source chosen = (result,sourceFinal) := by
        simpa [chosen] using run
      obtain ⟨ck',out,post,branchRun,hs,hm,hg,hc,outEq,hl,branchExtra⟩ :=
        chosenBound source sourceFinal result branchTarget chosenRun nonerror exprState exprMem exprGlobals exprCode branchLocals
      subst out
      simp only at branchExtra
      have hcomp : compileHOLExact ctxt live p = loopNestedSeqHOL (np ++
        [.assign tmp value,.ite .notEqual tmp (.imm (0 : BitVec width))
          (compileHOLExact ctxt live yes) (compileHOLExact ctxt live no) live]) := by
        simp only [p,compileHOLExact,compiled]
      have htail : ∀ k, evaluate (loopNestedSeqHOL
          [.assign tmp value,.ite .notEqual tmp (.imm (0 : BitVec width))
            (compileHOLExact ctxt live yes) (compileHOLExact ctxt live no) live])
          {st with clock := st.clock+k} =
        cutRes live (evaluate (compileHOLExact ctxt live chosen) {branchTarget with clock := st.clock+k}) := by
        intro k
        have hv : eval {st with clock := st.clock+k} value = some (.word w) := by
          rw [eval_upd_clock_eq]
          simpa [wlabWlocExact] using exprValue
        simp only [loopNestedSeqHOL,evaluate_seq,evaluate,hv]
        simp only [setVar,sptLookup_sptInsert,if_true,LoopSemStateFiniteExact.getVarImm,wordCmpHOL]
        dsimp only [branchTarget,setVar]
        by_cases hw : w = 0
        · simp only [hw,beq_self_eq_true,Bool.not_true,Bool.false_eq_true,if_false,ne_eq,not_true_eq_false,chosen]
          split <;> rename_i h <;> exact h.symm
        · have hb : (w == 0) = false := by simpa using hw
          simp only [hb,Bool.not_false,if_true,ne_eq,hw,not_false_eq_true,chosen]
          split <;> rename_i h <;> exact h.symm
      have prefixLift : ∀ k, evaluate (loopNestedSeqHOL np) {target with clock := target.clock+(ck+k)} =
          (none,{st with clock := st.clock+k}) := by
        intro k
        have h := evaluate_add_clock_eq _ _ _ _ k exprRun (by simp)
        simpa [Nat.add_assoc] using h
      have sourceCount := CrepSteps.steps_ite condition yes no source
      simp only [guard] at sourceCount
      have chosenCount : CrepSteps.steps chosen source + 1 = CrepSteps.steps p source := by
        by_cases hw : w ≠ 0
        · simp only [if_pos hw] at sourceCount
          dsimp only [chosen,p]
          rw [if_pos hw,sourceCount]
          exact Nat.add_comm _ _
        · simp only [if_neg hw] at sourceCount
          dsimp only [chosen,p]
          rw [if_neg hw,sourceCount]
          exact Nat.add_comm _ _
      have prefixEq : LoopSteps.structuralWeight (loopNestedSeqHOL np) = prefixSize := by
        dsimp [prefixSize]
        rw [compiled]
      rw [prefixEq] at prefixBound
      cases result with
      | none =>
        have branchRun' : evaluate (compileHOLExact ctxt live chosen) {branchTarget with clock := st.clock+ck'} = (none,post) := branchRun
        have branchLift := evaluate_add_clock_eq _ _ _ _ 1 branchRun' (by simp)
        have branchLift' : evaluate (compileHOLExact ctxt live chosen) {branchTarget with clock := st.clock+(ck'+1)} =
            (none,{post with clock := post.clock+1}) := by simpa [branchTarget,Nat.add_assoc] using branchLift
        have hloc : crepToLoopLocalsRelExact ctxt live sourceFinal.locals post.locals := hl
        have cut : cutRes live (none,{post with clock := post.clock+1}) =
            (none,{post with locals := sptInter post.locals live}) := by
          rw [cutRes]
          simp only
          rw [cutState_of_subset live {post with clock := post.clock+1} hloc.2.2.1]
          simp [decClock]
        have targetRun : evaluate code {target with clock := target.clock+(ck+(ck'+1))} =
            (none,{post with locals := sptInter post.locals live}) := by
          change evaluate (compileHOLExact ctxt live p) _ = _
          rw [hcomp,evaluate_nested_seq_append_none np _ _ _ (prefixLift (ck'+1)),htail,branchLift',cut]
        have extraBound : ck+(ck'+1) ≤ (prefixSize+factor+1)*(CrepSteps.steps p source+1) := by
          rw [chosenCount] at branchExtra
          nlinarith
        refine ⟨ck+(ck'+1),none,{post with locals := sptInter post.locals live},targetRun,hs,hm,hg,hc,rfl,?_,?_⟩
        · exact condition_locals_rel_inter ctxt live sourceFinal.locals post.locals hl
        · simpa [p,prefixSize,factor,compiled] using extraBound
      | some r =>
        have mapped : resultToLoop (some r) ≠ none := by cases r <;> simp [resultToLoop]
        have targetRun : evaluate code {target with clock := target.clock+(ck+ck')} =
            (resultToLoop (some r),post) := by
          change evaluate (compileHOLExact ctxt live p) _ = _
          have branchRun' : evaluate (compileHOLExact ctxt live chosen) {branchTarget with clock := st.clock+ck'} =
              (resultToLoop (some r),post) := by simpa [branchTarget,setVar] using branchRun
          rw [hcomp,evaluate_nested_seq_append_none np _ _ _ (prefixLift ck'),htail,branchRun']
          cases h : resultToLoop (some r) with
          | none => exact (mapped h).elim
          | some v => rfl
        have extraBound : ck+ck' ≤ (prefixSize+factor+1)*(CrepSteps.steps p source+1) := by
          rw [chosenCount] at branchExtra
          nlinarith
        refine ⟨ck+ck',resultToLoop (some r),post,targetRun,hs,hm,hg,hc,rfl,hl,?_⟩
        simpa [p,prefixSize,factor,compiled] using extraBound
/-- A scalar declaration is bounded once its body has been proved at the
context and live set produced by compiling the initializer. -/
theorem scalarDecl_clock {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (init : CrepExpHOL width) (initShape : CompiledScalar init)
    (body : CrepProgHOL width)
    (ctxt : CrepToLoopContextExact) (live : NumSet) (bodyFactor : Nat)
    (bodyBound : @BodySimulation width _ σ body
      {ctxt with vars := ctxt.vars.updateEq (name,(compileExpHOLExact ctxt (ctxt.vmax+1) live init).2.2.1), vmax := (compileExpHOLExact ctxt (ctxt.vmax+1) live init).2.2.1}
      (sptInsert (compileExpHOLExact ctxt (ctxt.vmax+1) live init).2.2.1 () live) (fun n => bodyFactor*(n+1))) :
    @BodySimulation width _ σ (.dec name init body) ctxt live
      (fun n => (LoopSteps.structuralWeight (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live init).1) + bodyFactor)*(n+1)) := by
  intro source sourceFinal result target run nonerror stateRel memRel globalsRel codeRel localsRel
  let p := CrepProgHOL.dec name init body
  let code := compileHOLExact ctxt live p
  let prefixSize := LoopSteps.structuralWeight (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live init).1)
  have sourceRun := run
  rw [evalCrepSemHOLProgExact_dec_holShape] at run
  rcases initRun : evalCrepSemHOLExp source init with _ | value
  · simp only [initRun,Prod.mk.injEq] at run
    exact absurd run.1.symm nonerror
  · simp only [initRun] at run
    let sourceBody := CrepSemHOLState.setVar name value source
    rcases bodyRun : evalCrepSemHOLProgExact sourceBody body with ⟨bodyResult,bodyPost⟩
    change evalCrepSemHOLProgExact {source with locals := source.locals.updateEq (name,value)} body = _ at bodyRun
    simp only [bodyRun,Prod.mk.injEq] at run
    obtain ⟨resultEq,finalEq⟩ := run
    have bodyNonerror : bodyResult ≠ some .error := by simpa [resultEq] using nonerror
    rcases compiled : compileExpHOLExact ctxt (ctxt.vmax+1) live init with ⟨np,loopValue,tmp,outLive⟩
    obtain ⟨ck,st,exprRun,exprValue,exprState,exprMem,exprGlobals,exprCode,exprLocals⟩ :=
      crepToLoop_comp_exp_preserves_eval source init value target ctxt (ctxt.vmax+1) live np loopValue tmp outLive
        ⟨initRun,stateRel,memRel,globalsRel,codeRel,localsRel,compiled,by omega⟩
    have prefixBound := condition_extraClock_bound source target st np ck (by
      intro q hq
      obtain ⟨_,_,_,_,hc,hbranch,_⟩ := condition_prefix_shape initShape ctxt (ctxt.vmax+1) live
      rw [compiled] at hc
      cases hc
      exact hbranch q hq) stateRel exprRun exprState
    obtain ⟨hok,htmp,hlive⟩ := compile_exp_out_rel ctxt (ctxt.vmax+1) live init np loopValue tmp outLive compiled
    have hsub : ∀ k, sptDomain live k → sptDomain outLive k :=
      fun k hk => hlive ▸ cut_sets_union_domain_subset _ live hok k hk
    have fresh : ctxt.vmax < tmp := by omega
    have baseLocals : crepToLoopLocalsRelExact ctxt live source.locals st.locals := by
      refine ⟨exprLocals.1,exprLocals.2.1,fun k hk => exprLocals.2.2.1 k (hsub k hk),?_⟩
      intro vn val hval
      obtain ⟨n,hn,hnlive,_⟩ := localsRel.2.2.2 vn val hval
      obtain ⟨n',hn',_,hval'⟩ := exprLocals.2.2.2 vn val hval
      have eq : n' = n := Option.some.inj (hn'.symm.trans hn)
      subst n'
      exact ⟨n,hn,hnlive,hval'⟩
    let bc := {ctxt with vars := ctxt.vars.updateEq (name,tmp), vmax := tmp}
    let bl := sptInsert tmp () live
    let bodyTarget := setVar tmp (wlabWlocExact value) st
    have entered := crepToLoopNcompileDecLocalsEnter ctxt live source.locals st.locals name tmp value baseLocals fresh
    have bodyLocals : crepToLoopLocalsRelExact bc bl sourceBody.locals bodyTarget.locals := by
      simpa [sourceBody,bodyTarget,bc,bl,CrepSemHOLState.setVar,setVar,wlabWlocExact,wlabWlocHOL] using entered
    have bodyState : crepToLoopStateRelExact sourceBody bodyTarget := by
      simpa [sourceBody,CrepSemHOLState.setVar,bodyTarget,setVar,crepToLoopStateRelExact] using exprState
    have bodyMem : crepToLoopMemRelHOLExact sourceBody.memory bodyTarget.memory sourceBody.memaddrs := by
      simpa [sourceBody,CrepSemHOLState.setVar,bodyTarget,setVar] using exprMem
    have bodyGlobals : crepToLoopGlobalsRelHOLExact sourceBody.globals bodyTarget.globals := by
      simpa [sourceBody,CrepSemHOLState.setVar,bodyTarget,setVar] using exprGlobals
    have bodyCode : crepToLoopCodeRelExact bc sourceBody.code bodyTarget.code := by
      simpa [sourceBody,CrepSemHOLState.setVar,bodyTarget,bc,setVar,crepToLoopCodeRelExact] using exprCode
    have bodyBound' : @BodySimulation width _ σ body bc bl (fun n => bodyFactor*(n+1)) := by simpa [bc,bl,compiled] using bodyBound
    obtain ⟨extra,out,post,bodyEval,hs,hm,hg,hc,outEq,_,bodyExtra⟩ :=
      bodyBound' sourceBody bodyPost bodyResult bodyTarget (by simpa [sourceBody,CrepSemHOLState.setVar] using bodyRun)
        bodyNonerror bodyState bodyMem bodyGlobals bodyCode bodyLocals
    subst out
    have prefixLift := evaluate_add_clock_eq _ _ _ _ extra exprRun (by simp)
    have prefixLift' : evaluate (loopNestedSeqHOL np) {target with clock := target.clock+(ck+extra)} =
        (none,{st with clock := st.clock+extra}) := by simpa [Nat.add_assoc] using prefixLift
    have assignRun : evaluate (.assign tmp loopValue) {st with clock := st.clock+extra} =
        (none,{bodyTarget with clock := st.clock+extra}) := by
      rw [evaluate]
      simp [eval_upd_clock_eq,exprValue,bodyTarget,setVar]
    have targetRun : evaluate code {target with clock := target.clock+(ck+extra)} = (resultToLoop result,post) := by
      change evaluate (compileHOLExact ctxt live (.dec name init body)) _ = _
      rw [compileHOLExact,compiled,evaluate_seq,prefixLift']
      simp only
      rw [evaluate_seq,assignRun]
      simp only
      simpa [bc,bl,bodyTarget,setVar,resultEq] using bodyEval
    have finalState : crepToLoopStateRelExact sourceFinal post := by
      rw [← finalEq]
      simpa [crepToLoopStateRelExact] using hs
    have finalMem : crepToLoopMemRelHOLExact sourceFinal.memory post.memory sourceFinal.memaddrs := by
      rw [← finalEq]
      simpa using hm
    have finalGlobals : crepToLoopGlobalsRelHOLExact sourceFinal.globals post.globals := by
      rw [← finalEq]
      simpa using hg
    have finalCode : crepToLoopCodeRelExact ctxt sourceFinal.code post.code := by
      rw [← finalEq]
      simpa [bc,crepToLoopCodeRelExact] using hc
    have finalLocals := compiler_run_locals p source sourceFinal result target post ctxt live (ck+extra)
      sourceRun nonerror stateRel memRel globalsRel codeRel localsRel targetRun
    have sourceCount := CrepSteps.steps_dec name init body source
    simp only [initRun] at sourceCount
    have prefixEq : LoopSteps.structuralWeight (loopNestedSeqHOL np) = prefixSize := by dsimp [prefixSize]; rw [compiled]
    rw [prefixEq] at prefixBound
    refine ⟨ck+extra,resultToLoop result,post,targetRun,finalState,finalMem,finalGlobals,finalCode,rfl,finalLocals,?_⟩
    have bcount : CrepSteps.steps body sourceBody ≤ CrepSteps.steps p source := by
      dsimp [p,sourceBody,CrepSemHOLState.setVar] at *
      omega
    nlinarith

/-- Loop-free compiler execution requires at most its structural visit weight
in added clock, irrespective of the source clock. -/
theorem scalarBranch_clock {width : Nat} [NeZero width] {σ : Type}
    (p : CrepProgHOL width) (shape : ScalarProgram p) (free : scalarNoWhile p = true)
    (ctxt : CrepToLoopContextExact) (live : NumSet) :
    @BodySimulation width _ σ p ctxt live
      (fun n => 3*loopVisitWeight (compileHOLExact ctxt live p)*(n+1)) := by
  intro source sourceFinal result target run nonerror stateRel memRel globalsRel codeRel localsRel
  obtain ⟨extra,out,post,ev,hs,hm,hg,hc,hr,hl,_,_⟩ :=
    branchProgram_correct_with_bounded_extra p (.scalar shape free) source sourceFinal result target ctxt live
      run nonerror stateRel memRel globalsRel codeRel localsRel
  have consumed := LoopSteps.branchedProgram_clock_consumed (compile_loopFreeCrep (.scalar shape free) ctxt live)
    {target with clock := target.clock+extra} post out ev
  have visits := LoopSteps.branchedProgram_structural_bound (compile_loopFreeCrep (.scalar shape free) ctxt live)
    {target with clock := target.clock+extra}
  have sourceClock := evalCrepSemHOLProgExact_clock_le source p
  rw [run] at sourceClock
  have initial := stateRel.2.2.1
  have final := hs.2.2.1
  have eqWeight := branch_visitWeight (compile_scalar_branch shape free ctxt live)
  refine ⟨extra,out,post,ev,hs,hm,hg,hc,hr,hl,?_⟩
  simp only at consumed sourceClock
  simp only [← eqWeight] at visits
  have positive := loopVisitWeight_pos (compileHOLExact ctxt live p)
  have extraSmall : extra ≤ loopVisitWeight (compileHOLExact ctxt live p) := by omega
  simp only
  nlinarith

/-- Added compiler clock is linear in source visits, with a coefficient
computed from the compiled Loop program's control structure. -/
theorem scalarProgram_clock {width : Nat} [NeZero width] {σ : Type}
    {p : CrepProgHOL width} (shape : ScalarProgram p) :
    ∀ (ctxt : CrepToLoopContextExact) (live : NumSet),
      @BodySimulation width _ σ p ctxt live
        (fun n => 3*loopVisitWeight (compileHOLExact ctxt live p)*(n+1)) := by
  induction shape with
  | skip => intro ctxt live; exact scalarBranch_clock .skip .skip rfl ctxt live
  | «break» n => intro ctxt live; exact scalarBranch_clock (.break n) (.break n) rfl ctxt live
  | «continue» n => intro ctxt live; exact scalarBranch_clock (.continue n) (.continue n) rfl ctxt live
  | tick => intro ctxt live; exact scalarBranch_clock .tick .tick rfl ctxt live
  | @ret e h => intro ctxt live; exact scalarBranch_clock (.return [e]) (.ret h) rfl ctxt live
  | @assign n e h => intro ctxt live; exact scalarBranch_clock (.assign n e) (.assign n h) rfl ctxt live
  | @store a b ha hb => intro ctxt live; exact scalarBranch_clock (.store a b) (.store ha hb) rfl ctxt live
  | @seq a b ha hb iha ihb =>
    intro ctxt live
    have sim := scalarSequence_clock a b ctxt live _ _ (iha ctxt live) (ihb ctxt live)
    apply clockSimulation_mono _ ctxt live _ _ sim
    simp only [compileHOLExact,loopVisitWeight]
    omega
  | @ite cond a b hc ha hb iha ihb =>
    intro ctxt live
    have sim := scalarIte_clock cond hc a b ctxt live _ _ (iha ctxt live) (ihb ctxt live)
    apply clockSimulation_mono _ ctxt live _ _ sim
    have weights := ite_prefix_body_weight hc (a := a) (b := b) ctxt live
    omega
  | @dec name init body hi hb ih =>
    intro ctxt live
    let tmp := (compileExpHOLExact ctxt (ctxt.vmax+1) live init).2.2.1
    let bc := {ctxt with vars := ctxt.vars.updateEq (name,tmp), vmax := tmp}
    let bl := sptInsert tmp () live
    have sim := scalarDecl_clock name init hi body ctxt live _ (ih bc bl)
    apply clockSimulation_mono _ ctxt live _ _ sim
    have weights := decl_prefix_body_weight name hi (body := body) ctxt live
    change _ + loopVisitWeight (compileHOLExact bc bl body) ≤ _ at weights
    omega
  | @«while» cond body hc hb ih =>
    intro ctxt live
    let bf := 3*loopVisitWeight (compileHOLExact ctxt live body)
    have sim := ih ctxt live
    intro source sourceFinal result target run nonerror stateRel memRel globalsRel codeRel localsRel
    obtain ⟨extra,post,bound,ev,hs,hm,hg,hcode,hl⟩ :=
      branchConditionWhile_bounded_clock cond hc body bf source sourceFinal result target ctxt live
        sim run nonerror stateRel memRel globalsRel codeRel localsRel
    have weights := while_prefix_body_weight hc (body := body) ctxt live
    have factor : LoopSteps.structuralWeight (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live cond).1) + bf+2 ≤
        3*loopVisitWeight (compileHOLExact ctxt live (.while cond body)) := by dsimp [bf]; omega
    exact ⟨extra,resultToLoop result,post,ev,hs,hm,hg,hcode,rfl,hl,
      bound.trans (Nat.mul_le_mul_right _ factor)⟩

end SteppedFlapjack.CrepToLoopSteps
