import SteppedFlapjack.CrepToLoopSteps.DirectExpressionEval
import SteppedFlapjack.CrepToLoopSteps.WhileClock

/-! Terminating and continuing iterations of a direct Crep while loop. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
variable {width : Nat} [NeZero width] {F : Type}

private theorem loop_step_continue {L L' : NumSet} {B : HolLoopProg width}
    {X X1 s2 : LoopSemStateFiniteExact width F}
    (hc : LoopSemStateFiniteExact.cutRes L (none, X) = (none, X1))
    (hb : LoopSemStateFiniteExact.evaluate B X1 = (some (.continue 0), s2)) :
    LoopSemStateFiniteExact.evaluate (.loop L B L') X = LoopSemStateFiniteExact.evaluate (.loop L B L') s2 := by
  rw [LoopSemStateFiniteExact.evaluate]
  split
  next X1' h =>
    rw [hc] at h
    simp only [Prod.mk.injEq, true_and] at h
    subst h
    split <;> rename_i h2 <;> rw [LoopSemStateFiniteExact.fix_clock_evaluate, hb] at h2 <;>
      simp_all [LoopSemStateFiniteExact.exitLoop]
  next h => exact absurd hc (h X1)

private theorem loop_step_break {L L' : NumSet} {B : HolLoopProg width}
    {X X1 s2 : LoopSemStateFiniteExact width F}
    (hc : LoopSemStateFiniteExact.cutRes L (none, X) = (none, X1))
    (hb : LoopSemStateFiniteExact.evaluate B X1 = (some (.break 0), s2)) :
    LoopSemStateFiniteExact.evaluate (.loop L B L') X = LoopSemStateFiniteExact.cutRes L' (none, s2) := by
  rw [LoopSemStateFiniteExact.evaluate]
  split
  next X1' h =>
    rw [hc] at h
    simp only [Prod.mk.injEq, true_and] at h
    subst h
    split <;> rename_i h2 <;> rw [LoopSemStateFiniteExact.fix_clock_evaluate, hb] at h2 <;>
      simp_all [LoopSemStateFiniteExact.exitLoop]
  next h => exact absurd hc (h X1)

private theorem locals_rel_inter (ctxt : CrepToLoopContextExact) (l : NumSet)
    (sl : HolFiniteMapExact Nat (HolWordLab width)) (tl : Spt (WordLocW width))
    (h : crepToLoopLocalsRelExact ctxt l sl tl) :
    crepToLoopLocalsRelExact ctxt l sl (sptInter tl l) := by
  refine ⟨h.1, h.2.1, fun k hk => ?_, fun vn val hval => ?_⟩
  · have hk' : (sptLookup k l).isSome := hk
    show (sptLookup k (sptInter tl l)).isSome
    rw [sptLookup_sptInter, if_pos hk']
    exact h.2.2.1 k hk
  · obtain ⟨n, hn1, hn2, hn3⟩ := h.2.2.2 vn val hval
    have hnl : (sptLookup n l).isSome := hn2
    refine ⟨n, hn1, hn2, ?_⟩
    show sptLookup n (sptInter tl l) = _
    rw [sptLookup_sptInter, if_pos hnl]
    exact hn3

private theorem seq_continue_none {cC : HolLoopProg width}
    {S s' : LoopSemStateFiniteExact width F}
    (h : LoopSemStateFiniteExact.evaluate cC S = (none, s')) :
    LoopSemStateFiniteExact.evaluate (.seq cC (.continue 0)) S = (some (.continue 0), s') := by
  rw [LoopSemStateFiniteExact.evaluate_seq, h]
  simp only [LoopSemStateFiniteExact.evaluate]

private theorem seq_continue_some {cC : HolLoopProg width}
    {S s' : LoopSemStateFiniteExact width F} {x : LoopSemStateFiniteExact.LoopResultExact width}
    (h : LoopSemStateFiniteExact.evaluate cC S = (some x, s')) :
    LoopSemStateFiniteExact.evaluate (.seq cC (.continue 0)) S = (some x, s') := by
  rw [LoopSemStateFiniteExact.evaluate_seq, h]

private theorem while_body_eval (np : List (HolLoopProg width)) (le : HolLoopExp width)
    (tmp : Nat) (l : NumSet) (cC : HolLoopProg width) (Y st : LoopSemStateFiniteExact width F)
    (w : BitVec width) (h1 : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL np) Y = (none, st))
    (h1v : LoopSemStateFiniteExact.eval st le = some (.word w)) :
    LoopSemStateFiniteExact.evaluate
      (loopNestedSeqHOL (np ++
        [.assign tmp le,
         .ite .notEqual tmp (.imm (0 : BitVec width)) (.seq cC (.continue 0)) (.break 0) l])) Y =
      if w = 0 then (some (.break 0), LoopSemStateFiniteExact.setVar tmp (.word w) st)
      else LoopSemStateFiniteExact.cutRes l
        (LoopSemStateFiniteExact.evaluate (.seq cC (.continue 0))
          (LoopSemStateFiniteExact.setVar tmp (.word w) st)) := by
  generalize (HolLoopProg.seq cC (.continue 0) : HolLoopProg width) = q
  rw [LoopSemStateFiniteExact.evaluate_nested_seq_append_none np _ _ _ h1]
  simp only [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq]
  simp only [LoopSemStateFiniteExact.evaluate, h1v]
  simp only [LoopSemStateFiniteExact.setVar, sptLookup_sptInsert, if_true,
    LoopSemStateFiniteExact.getVarImm, Compiler.Encoders.Asm.wordCmpHOL]
  by_cases hw : w = 0
  · subst hw
    simp only [beq_self_eq_true, Bool.not_true, Bool.false_eq_true, if_false, if_true]
    rfl
  · have hb : (w == 0) = false := by simpa using hw
    simp only [hb, Bool.not_false, if_true, hw, if_false]
    split <;> rename_i h <;> exact h.symm


/-- A false direct condition exits the actual compiled Loop with two additional
clock units, regardless of the loop body or initial clock. -/
theorem directWhile_false_run
    (condition : CrepExpHOL width) (shape : DirectExpression condition)
    (body : CrepProgHOL width) (source : CrepSemHOLState width F)
    (target : LoopSemStateFiniteExact width F) (ctxt : CrepToLoopContextExact) (live : NumSet)
    (guard : evalCrepSemHOLExp source condition = some (.word 0))
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    ∃ post, evaluate (compileHOLExact ctxt live (.while condition body))
      {target with clock := target.clock + 2} = (none,post) ∧
      crepToLoopStateRelExact source post ∧
      crepToLoopMemRelHOLExact source.memory post.memory source.memaddrs ∧
      crepToLoopGlobalsRelHOLExact source.globals post.globals ∧
      crepToLoopCodeRelExact ctxt source.code post.code ∧
      crepToLoopLocalsRelExact ctxt live source.locals post.locals := by
  let initial := {target with locals := sptInter target.locals live}
  have localsInitial : crepToLoopLocalsRelExact ctxt live source.locals initial.locals :=
    locals_rel_inter ctxt live source.locals target.locals localsRel
  have stateInitial : crepToLoopStateRelExact source initial := by simpa [initial,crepToLoopStateRelExact] using stateRel
  obtain ⟨value,compiled,valueEval⟩ := directExpression_preserves_eval condition shape source (.word 0)
    initial ctxt (ctxt.vmax+1) live guard stateInitial memRel globalsRel codeRel localsInitial (by omega)
  let B := directWhileBody ctxt live value body
  have hcomp : compileHOLExact ctxt live (.while condition body) = .loop live B live := by
    simp [compileHOLExact,compiled,B,directWhileBody]
  have subset : LoopSemStateFiniteExact.sptSubsetLive live target.locals := localsRel.2.2.1
  have entry : cutRes live (none, {target with clock := target.clock+2}) =
      (none, {initial with clock := target.clock+1}) := by
    rw [cutRes]
    simp only
    rw [cutState_of_subset live {target with clock := target.clock+2} subset]
    simp [decClock,initial]
  have prefixRun : evaluate (loopNestedSeqHOL ([] : List (HolLoopProg width)))
      {initial with clock := target.clock+1} = (none,{initial with clock := target.clock+1}) := by
    simp [loopNestedSeqHOL,evaluate]
  have evalValue : LoopSemStateFiniteExact.eval {initial with clock := target.clock+1} value = some (.word 0) := by
    rw [eval_upd_clock_eq]
    simpa [wlabWlocExact] using valueEval
  have bodyRun := while_body_eval [] value (ctxt.vmax+1) live (compileHOLExact ctxt live body)
    _ _ 0 prefixRun evalValue
  simp only [List.nil_append] at bodyRun
  have loopRun := loop_step_break (L' := live) entry bodyRun
  have subsetPost : LoopSemStateFiniteExact.sptSubsetLive live
      (setVar (ctxt.vmax+1) (.word 0) {initial with clock := target.clock+1}).locals :=
    fun k hk => (sptMem_sptInsert k _ _ _).mpr (Or.inr (localsInitial.2.2.1 k hk))
  let post := {target with locals := sptInter (sptInsert (ctxt.vmax+1) (.word 0) initial.locals) live}
  have exit : cutRes live (none, setVar (ctxt.vmax+1) (.word 0) {initial with clock := target.clock+1}) =
      (none,post) := by
    rw [cutRes]
    simp only
    rw [cutState_of_subset live _ subsetPost]
    simp [decClock,setVar,post,initial]
  refine ⟨post,?_,?_,?_,?_,?_,?_⟩
  · rw [hcomp]
    exact loopRun.trans exit
  · simpa [post,crepToLoopStateRelExact] using stateRel
  · simpa [post] using memRel
  · simpa [post] using globalsRel
  · simpa [post] using codeRel
  · apply locals_rel_inter ctxt live source.locals _
    refine ⟨localsInitial.1,localsInitial.2.1,?_,?_⟩
    · intro k hk
      exact (sptMem_sptInsert k _ _ _).mpr (Or.inr (localsInitial.2.2.1 k hk))
    · intro vn val hv
      obtain ⟨n,hn,hl,hv⟩ := localsInitial.2.2.2 vn val hv
      have bound := localsInitial.2.1 vn n hn
      refine ⟨n,hn,hl,?_⟩
      rw [sptLookup_sptInsert,if_neg (by omega)]
      exact hv


/-- One continuing source iteration is simulated by the compiled Loop loop.
The extra clock is bounded by the compiled branch body, and the equation holds
for every additional clock reserved for later iterations. -/
theorem directWhile_continue_run
    (condition : CrepExpHOL width) (shape : DirectExpression condition)
    (body : CrepProgHOL width) (bodyShape : BranchProgram body)
    (source sourcePost : CrepSemHOLState width F) (bodyResult : Option (CrepResultHOLExact width))
    (target : LoopSemStateFiniteExact width F) (ctxt : CrepToLoopContextExact) (live : NumSet)
    (w : BitVec width) (guard : evalCrepSemHOLExp source condition = some (.word w))
    (nonzero : w ≠ 0) (clockNonzero : source.clock ≠ 0)
    (bodyRun : evalCrepSemHOLProgExact (decClockCrepSemHOL source) body = (bodyResult,sourcePost))
    (continues : bodyResult = none ∨ bodyResult = some (.continue 0))
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    ∃ extra post,
      extra ≤ sizeOf (compileHOLExact ctxt live body) ∧
      crepToLoopStateRelExact sourcePost post ∧
      crepToLoopMemRelHOLExact sourcePost.memory post.memory sourcePost.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourcePost.globals post.globals ∧
      crepToLoopCodeRelExact ctxt sourcePost.code post.code ∧
      crepToLoopLocalsRelExact ctxt live sourcePost.locals post.locals ∧
      ∀ k, evaluate (compileHOLExact ctxt live (.while condition body))
          {target with clock := target.clock + (extra+k)} =
        evaluate (compileHOLExact ctxt live (.while condition body)) {post with clock := post.clock+k} := by
  have targetNonzero : target.clock ≠ 0 := stateRel.2.2.1 ▸ clockNonzero
  let initial := {target with locals := sptInter target.locals live, clock := target.clock-1}
  have initialLocals : crepToLoopLocalsRelExact ctxt live source.locals initial.locals :=
    locals_rel_inter ctxt live source.locals target.locals localsRel
  have initialState : crepToLoopStateRelExact (decClockCrepSemHOL source) initial := by
    simp only [crepToLoopStateRelExact,decClockCrepSemHOL,initial] at *
    exact ⟨stateRel.1,stateRel.2.1,by omega,stateRel.2.2.2⟩
  have guardDec : evalCrepSemHOLExp (decClockCrepSemHOL source) condition = some (.word w) := by
    simpa only [decClockCrepSemHOL,evalCrepSemHOLExp_upd_clock_eq] using guard
  obtain ⟨value,compiled,valueEval⟩ := directExpression_preserves_eval condition shape
    (decClockCrepSemHOL source) (.word w) initial ctxt (ctxt.vmax+1) live guardDec
    initialState memRel globalsRel codeRel initialLocals (by omega)
  let bodyTarget := setVar (ctxt.vmax+1) (.word w) initial
  have bodyLocals : crepToLoopLocalsRelExact ctxt live (decClockCrepSemHOL source).locals bodyTarget.locals := by
    change crepToLoopLocalsRelExact ctxt live source.locals (sptInsert (ctxt.vmax+1) (.word w) initial.locals)
    refine ⟨initialLocals.1,initialLocals.2.1,?_,?_⟩
    · intro k hk
      exact (sptMem_sptInsert k _ _ _).mpr (Or.inr (initialLocals.2.2.1 k hk))
    · intro vn val hv
      obtain ⟨n,hn,hl,hv⟩ := initialLocals.2.2.2 vn val hv
      have bound := initialLocals.2.1 vn n hn
      refine ⟨n,hn,hl,?_⟩
      rw [sptLookup_sptInsert,if_neg (by omega)]
      exact hv
  have bodyState : crepToLoopStateRelExact (decClockCrepSemHOL source) bodyTarget := by
    simpa [bodyTarget,setVar,crepToLoopStateRelExact] using initialState
  have bodyNonerror : bodyResult ≠ some .error := by rcases continues with h | h <;> simp [h]
  obtain ⟨extra,out,post,hbody,hstate,hmem,hglobals,hcode,hresult,hlocals,_,hextra⟩ :=
    branchProgram_correct_with_bounded_extra body bodyShape (decClockCrepSemHOL source) sourcePost bodyResult
      bodyTarget ctxt live bodyRun bodyNonerror bodyState memRel globalsRel codeRel bodyLocals
  have hlocals' : crepToLoopLocalsRelExact ctxt live sourcePost.locals post.locals := by
    rcases continues with h | h <;> simpa [h,localsResultRel] using hlocals
  refine ⟨extra,post,hextra,hstate,hmem,hglobals,hcode,hlocals',?_⟩
  intro k
  let B := directWhileBody ctxt live value body
  have hcomp : compileHOLExact ctxt live (.while condition body) = .loop live B live := by
    simp [compileHOLExact,compiled,B,directWhileBody]
  have subset : sptSubsetLive live target.locals := localsRel.2.2.1
  have entry : cutRes live (none, {target with clock := target.clock+(extra+k)}) =
      (none, {initial with clock := target.clock-1+(extra+k)}) := by
    rw [cutRes]
    simp only
    rw [cutState_of_subset live {target with clock := target.clock+(extra+k)} subset]
    simp only [decClock,show ¬ target.clock+(extra+k)=0 by omega,if_false]
    simp only [initial,Prod.mk.injEq,true_and]
    congr 1
    omega
  have prefixRun : evaluate (loopNestedSeqHOL ([] : List (HolLoopProg width)))
      {initial with clock := target.clock-1+(extra+k)} =
        (none,{initial with clock := target.clock-1+(extra+k)}) := by simp [loopNestedSeqHOL,evaluate]
  have evalValue : LoopSemStateFiniteExact.eval {initial with clock := target.clock-1+(extra+k)} value = some (.word w) := by
    rw [eval_upd_clock_eq]
    simpa [wlabWlocExact] using valueEval
  have bodyEval := while_body_eval [] value (ctxt.vmax+1) live (compileHOLExact ctxt live body)
    _ _ w prefixRun evalValue
  simp only [List.nil_append,if_neg nonzero] at bodyEval
  have notTimeout : out ≠ some .timeOut := by
    rw [hresult]
    rcases continues with h | h <;> simp [h,resultToLoop]
  have hbodyK : evaluate (compileHOLExact ctxt live body)
      {bodyTarget with clock := bodyTarget.clock+(extra+k)} = (out,{post with clock := post.clock+k}) := by
    have shift := evaluate_add_clock_eq _ _ _ _ k hbody notTimeout
    simpa [Nat.add_assoc] using shift
  have seqRun : evaluate (.seq (compileHOLExact ctxt live body) (.continue 0))
      {bodyTarget with clock := bodyTarget.clock+(extra+k)} =
        (some (.continue 0),{post with clock := post.clock+k}) := by
    rcases continues with h | h
    · have outEq : out = none := by simpa [h,resultToLoop] using hresult
      rw [outEq] at hbodyK
      exact seq_continue_none hbodyK
    · have outEq : out = some (.continue 0) := by simpa [h,resultToLoop] using hresult
      rw [outEq] at hbodyK
      exact seq_continue_some hbodyK
  have bodyLoop : evaluate B {initial with clock := target.clock-1+(extra+k)} =
      (some (.continue 0),{post with clock := post.clock+k}) := by
    change evaluate (loopNestedSeqHOL [.assign (ctxt.vmax+1) value,
      .ite .notEqual (ctxt.vmax+1) (.imm 0) (.seq (compileHOLExact ctxt live body) (.continue 0)) (.break 0) live]) _ = _
    rw [bodyEval]
    have : setVar (ctxt.vmax+1) (.word w) {initial with clock := target.clock-1+(extra+k)} =
        {bodyTarget with clock := bodyTarget.clock+(extra+k)} := by simp [bodyTarget,setVar,initial]
    rw [this,seqRun]
    rfl
  rw [hcomp]
  exact loop_step_continue entry bodyLoop

end SteppedFlapjack.CrepToLoopSteps
