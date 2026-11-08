import SteppedFlapjack.CrepToLoopSteps.ScalarIteBound
import SteppedFlapjack.CrepToLoopSteps.ResultLocals

/-! Bottom-up quantitative simulation for scalar declarations. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- A scalar declaration is bounded once its body has been proved at the
context and live set produced by compiling the initializer. -/
theorem scalarDecl_programBound {width : Nat} [NeZero width] {σ : Type}
    (name : Nat) (init : CrepExpHOL width) (initShape : CompiledScalar init)
    (body : CrepProgHOL width) (bodyShape : ScalarProgram body)
    (ctxt : CrepToLoopContextExact) (live : NumSet) (bodyFactor : Nat)
    (bodyBound : @ProgramBound width _ σ body
      {ctxt with vars := ctxt.vars.updateEq (name,(compileExpHOLExact ctxt (ctxt.vmax+1) live init).2.2.1), vmax := (compileExpHOLExact ctxt (ctxt.vmax+1) live init).2.2.1}
      (sptInsert (compileExpHOLExact ctxt (ctxt.vmax+1) live init).2.2.1 () live) bodyFactor) :
    @ProgramBound width _ σ (.dec name init body) ctxt live
      (loopVisitWeight (compileHOLExact ctxt live (.dec name init body)) *
        (LoopSteps.structuralWeight (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live init).1) + 2*bodyFactor+1)) := by
  intro source sourceFinal result target run nonerror stateRel memRel globalsRel codeRel localsRel
  let p := CrepProgHOL.dec name init body
  let code := compileHOLExact ctxt live p
  let prefixSize := LoopSteps.structuralWeight (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live init).1)
  have scalar : ScalarProgram p := .dec name initShape bodyShape
  have loopShape := compile_scalar_program scalar ctxt live
  have sourceConsumed := CrepSteps.scalarProgram_clock_consumed scalar source sourceFinal result run
  have sourceClock := evalCrepSemHOLProgExact_clock_le source p
  rw [run] at sourceClock
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
    have prefixBound := condition_extraClock_control_bound source target st np ck (by
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
    have bodyBound' : @ProgramBound width _ σ body bc bl bodyFactor := by simpa [bc,bl,compiled] using bodyBound
    obtain ⟨extra,post,bodyEval,hs,hm,hg,hc,_,visits⟩ :=
      bodyBound' sourceBody bodyPost bodyResult bodyTarget (by simpa [sourceBody,CrepSemHOLState.setVar] using bodyRun)
        bodyNonerror bodyState bodyMem bodyGlobals bodyCode bodyLocals
    have bodyExtra := scalarLoop_extra_le_visits sourceBody bodyPost bodyResult bodyTarget post bc bl bodyShape extra _
      (by simpa [sourceBody,CrepSemHOLState.setVar] using bodyRun) bodyState hs bodyEval visits
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
    have padding : ck+extra ≤ (prefixSize+2*bodyFactor)*(CrepSteps.steps p source+1) := by
      nlinarith
    have allVisits := scalarLoop_control_consumption_bound loopShape _ post (resultToLoop result) targetRun
    have initial := stateRel.2.2.1
    have final := finalState.2.2.1
    have delta : target.clock+(ck+extra)-post.clock ≤ CrepSteps.steps p source+(ck+extra) := by omega
    have budget : target.clock+(ck+extra)-post.clock+1 ≤
        (prefixSize+2*bodyFactor+1)*(CrepSteps.steps p source+1) := by nlinarith
    refine ⟨ck+extra,post,targetRun,finalState,finalMem,finalGlobals,finalCode,finalLocals,?_⟩
    rw [prefixEq]
    change LoopSteps.steps code {target with clock := target.clock+(ck+extra)} ≤
      (loopVisitWeight code*(prefixSize+2*bodyFactor+1))*(CrepSteps.steps p source+1)
    rw [Nat.mul_assoc]
    exact allVisits.trans (Nat.mul_le_mul_left _ budget)
end SteppedFlapjack.CrepToLoopSteps
