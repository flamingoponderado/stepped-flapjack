import SteppedFlapjack.CrepToLoopSteps.ConditionContinue
import SteppedFlapjack.CrepSteps.ScalarClock

/-! Bottom-up quantitative simulation for scalar conditionals. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.Compiler.Encoders.Asm
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- A conditional is bounded once both of its branches have been proved. -/
theorem scalarIte_programBound {width : Nat} [NeZero width] {σ : Type}
    (condition : CrepExpHOL width) (conditionShape : CompiledScalar condition)
    (yes no : CrepProgHOL width) (yesShape : ScalarProgram yes) (noShape : ScalarProgram no)
    (ctxt : CrepToLoopContextExact) (live : NumSet) (yesFactor noFactor : Nat)
    (yesBound : @ProgramBound width _ σ yes ctxt live yesFactor)
    (noBound : @ProgramBound width _ σ no ctxt live noFactor) :
    @ProgramBound width _ σ (.ite condition yes no) ctxt live
      (loopVisitWeight (compileHOLExact ctxt live (.ite condition yes no)) *
        (LoopSteps.structuralWeight (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live condition).1) +
          2*max yesFactor noFactor+2)) := by
  classical
  intro source sourceFinal result target run nonerror stateRel memRel globalsRel codeRel localsRel
  let p := CrepProgHOL.ite condition yes no
  let factor := max yesFactor noFactor
  let prefixSize := LoopSteps.structuralWeight (loopNestedSeqHOL (compileExpHOLExact ctxt (ctxt.vmax+1) live condition).1)
  let code := compileHOLExact ctxt live p
  have shape : ScalarProgram p := .ite conditionShape yesShape noShape
  have loopShape := compile_scalar_program shape ctxt live
  have sourceConsumed := CrepSteps.scalarProgram_clock_consumed shape source sourceFinal result run
  have sourceClock := evalCrepSemHOLProgExact_clock_le source p
  rw [run] at sourceClock
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
      have chosenShape : ScalarProgram chosen := by
        dsimp [chosen]
        split <;> assumption
      have chosenBound : @ProgramBound width _ σ chosen ctxt live factor := by
        dsimp [chosen,factor]
        split
        · exact programBound_mono yes ctxt live yesFactor _ yesBound (Nat.le_max_left _ _)
        · exact programBound_mono no ctxt live noFactor _ noBound (Nat.le_max_right _ _)
      have chosenRun : evalCrepSemHOLProgExact source chosen = (result,sourceFinal) := by
        simpa [chosen] using run
      obtain ⟨ck',post,branchRun,hs,hm,hg,hc,hl,branchVisits⟩ :=
        chosenBound source sourceFinal result branchTarget chosenRun nonerror exprState exprMem exprGlobals exprCode branchLocals
      have branchExtra := scalarLoop_extra_le_visits source sourceFinal result branchTarget post ctxt live chosenShape ck' _
        chosenRun exprState hs branchRun branchVisits
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
      have clockFinish (extra : Nat) (final : LoopSemStateFiniteExact width σ)
          (targetRun : evaluate code {target with clock := target.clock+extra} = (resultToLoop result,final))
          (stateFinal : crepToLoopStateRelExact sourceFinal final)
          (extraBound : extra ≤ (prefixSize+2*factor+1)*(CrepSteps.steps p source+1)) :
          LoopSteps.steps code {target with clock := target.clock+extra} ≤
            loopVisitWeight code*(prefixSize+2*factor+2)*(CrepSteps.steps p source+1) := by
        have visits := scalarLoop_control_consumption_bound loopShape _ final (resultToLoop result) targetRun
        have initial := stateRel.2.2.1
        have last := stateFinal.2.2.1
        have delta : target.clock+extra-final.clock ≤ CrepSteps.steps p source+extra := by omega
        have budget : target.clock+extra-final.clock+1 ≤
            (prefixSize+2*factor+2)*(CrepSteps.steps p source+1) := by nlinarith
        rw [Nat.mul_assoc]
        exact visits.trans (Nat.mul_le_mul_left _ budget)
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
        have extraBound : ck+(ck'+1) ≤ (prefixSize+2*factor+1)*(CrepSteps.steps p source+1) := by
          rw [chosenCount] at branchExtra
          nlinarith
        refine ⟨ck+(ck'+1),{post with locals := sptInter post.locals live},targetRun,hs,hm,hg,hc,?_,?_⟩
        · exact condition_locals_rel_inter ctxt live sourceFinal.locals post.locals hl
        · simpa [code,p,prefixSize,factor,compiled] using clockFinish _ _ targetRun hs extraBound
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
        have extraBound : ck+ck' ≤ (prefixSize+2*factor+1)*(CrepSteps.steps p source+1) := by
          rw [chosenCount] at branchExtra
          nlinarith
        refine ⟨ck+ck',post,targetRun,hs,hm,hg,hc,hl,?_⟩
        simpa [code,p,prefixSize,factor,compiled] using clockFinish _ _ targetRun hs extraBound
end SteppedFlapjack.CrepToLoopSteps
