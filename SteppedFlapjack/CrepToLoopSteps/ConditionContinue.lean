import SteppedFlapjack.CrepToLoopSteps.ConditionZero

/-! Continuing iterations for general branch conditions. -/
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

private theorem loop_step_exit {L L' : NumSet} {B : HolLoopProg width}
    {X X1 s2 : LoopSemStateFiniteExact width F} {r : LoopSemStateFiniteExact.LoopResultExact width}
    (hr0 : r ≠ .continue 0) (hr1 : r ≠ .break 0)
    (hc : LoopSemStateFiniteExact.cutRes L (none, X) = (none, X1))
    (hb : LoopSemStateFiniteExact.evaluate B X1 = (some r, s2)) :
    LoopSemStateFiniteExact.evaluate (.loop L B L') X = (LoopSemStateFiniteExact.exitLoop (some r), s2) := by
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

/-- `locals_rel ctxt l` survives the compiled condition (whose output live set
    `nl` contains `l`) and the write of the fresh temporary `tmp > vmax`. -/
private theorem locals_rel_insert_of (ctxt : CrepToLoopContextExact) (l nl : NumSet)
    (sl : HolFiniteMapExact Nat (HolWordLab width)) (tl tl' : Spt (WordLocW width))
    (hl : crepToLoopLocalsRelExact ctxt l sl tl) (h1l : crepToLoopLocalsRelExact ctxt nl sl tl')
    (hsub : ∀ k, sptDomain l k → sptDomain nl k) (tmp : Nat) (htmp : ctxt.vmax < tmp)
    (x : WordLocW width) :
    crepToLoopLocalsRelExact ctxt l sl (sptInsert tmp x tl') := by
  refine ⟨h1l.1, h1l.2.1, fun k hk => ?_, fun vn val hval => ?_⟩
  · exact (sptMem_sptInsert k tmp _ _).mpr (Or.inr (h1l.2.2.1 k (hsub k hk)))
  · obtain ⟨n, hn1, hn2, _⟩ := hl.2.2.2 vn val hval
    obtain ⟨n', hn1', _, hn3'⟩ := h1l.2.2.2 vn val hval
    have hnn : n' = n := Option.some.inj (hn1'.symm.trans hn1)
    subst hnn
    have hle := h1l.2.1 vn n' hn1'
    refine ⟨n', hn1', hn2, ?_⟩
    rw [sptLookup_sptInsert, if_neg (by omega)]
    exact hn3'

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

/-- One run of the compiled While body `nested_seq (np ++ [Assign tmp le;
    If NotEqual tmp (Imm 0w) (Seq c (Continue 0)) (Break 0) l])`. -/
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


private theorem resultToLoop_exitLoop (r : CrepResultHOLExact width)
    (h0 : r ≠ .continue 0) (h1 : r ≠ .break 0) :
    LoopSemStateFiniteExact.exitLoop (resultToLoop (some r)) =
      resultToLoop (exitLoopCrepResult (some r)) := by
  cases r with
  | «continue» n => cases n with
    | zero => exact absurd rfl h0
    | succ n => rfl
  | «break» n => cases n with
    | zero => exact absurd rfl h1
    | succ n => rfl
  | _ => rfl

private theorem localsResultRel_exitLoop (ctxt : CrepToLoopContextExact) (l : NumSet)
    (s : CrepSemHOLState width F) (tt : LoopSemStateFiniteExact width F)
    (r : CrepResultHOLExact width) (h : localsResultRel ctxt l (some r) s tt) :
    localsResultRel ctxt l (exitLoopCrepResult (some r)) s tt := by
  cases r <;> exact h

/-- One continuing iteration of the actual compiled loop, with a bound on both
the condition prefix clock and body clock and arbitrary reserve for later work. -/
theorem branchCondition_continue_run
    (condition : CrepExpHOL width) (conditionShape : CompiledScalar condition)
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
    ∃ code value next outLive extra post,
      compileExpHOLExact ctxt (ctxt.vmax+1) live condition = (code,value,next,outLive) ∧
      extra ≤ sizeOf (loopNestedSeqHOL code) + sizeOf (compileHOLExact ctxt live body) ∧
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
  obtain ⟨code,value,next,outLive,compiled,branch,_⟩ :=
    condition_prefix_shape conditionShape ctxt (ctxt.vmax+1) live
  obtain ⟨hok,htmp,hlive⟩ := compile_exp_out_rel ctxt (ctxt.vmax+1) live condition code value next outLive compiled
  have hsub : ∀ k, sptDomain live k → sptDomain outLive k :=
    fun k hk => hlive ▸ cut_sets_union_domain_subset _ live hok k hk
  have hfresh : ctxt.vmax < next := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) htmp
  obtain ⟨ck,afterCondition,exprRun,exprValue,exprState,exprMem,exprGlobals,exprCode,exprLocals⟩ :=
    crepToLoop_comp_exp_preserves_eval (decClockCrepSemHOL source) condition (.word w) initial ctxt
      (ctxt.vmax+1) live code value next outLive
      ⟨guardDec,initialState,memRel,globalsRel,codeRel,initialLocals,compiled,by omega⟩
  have conditionBound := condition_extraClock_bound (decClockCrepSemHOL source) initial afterCondition
    code ck branch initialState exprRun exprState
  let bodyTarget := setVar next (.word w) afterCondition
  have bodyLocals : crepToLoopLocalsRelExact ctxt live (decClockCrepSemHOL source).locals bodyTarget.locals := by
    exact locals_rel_insert_of ctxt live outLive source.locals _ afterCondition.locals initialLocals exprLocals hsub next hfresh _
  have bodyNonerror : bodyResult ≠ some .error := by rcases continues with h | h <;> simp [h]
  obtain ⟨bodyExtra,out,post,hbody,hstate,hmem,hglobals,hcode,hresult,hlocals,_,hbodyBound⟩ :=
    branchProgram_correct_with_bounded_extra body bodyShape (decClockCrepSemHOL source) sourcePost bodyResult
      bodyTarget ctxt live bodyRun bodyNonerror exprState exprMem exprGlobals exprCode bodyLocals
  have hlocals' : crepToLoopLocalsRelExact ctxt live sourcePost.locals post.locals := by
    rcases continues with h | h <;> simpa [h,localsResultRel] using hlocals
  refine ⟨code,value,next,outLive,ck+bodyExtra,post,compiled,by omega,hstate,hmem,hglobals,hcode,hlocals',?_⟩
  intro k
  let B := branchConditionWhileBody ctxt live code value next body
  have hcomp : compileHOLExact ctxt live (.while condition body) = .loop live B live := by
    simp [compileHOLExact,compiled,B,branchConditionWhileBody]
  have subset : sptSubsetLive live target.locals := localsRel.2.2.1
  have entry : cutRes live (none, {target with clock := target.clock+((ck+bodyExtra)+k)}) =
      (none, {initial with clock := target.clock-1+((ck+bodyExtra)+k)}) := by
    rw [cutRes]
    simp only
    rw [cutState_of_subset live {target with clock := target.clock+((ck+bodyExtra)+k)} subset]
    simp only [decClock,show ¬ target.clock+((ck+bodyExtra)+k)=0 by omega,if_false]
    simp only [initial,Prod.mk.injEq,true_and]
    congr 1
    omega
  have exprShift : evaluate (loopNestedSeqHOL code)
      {initial with clock := target.clock-1+((ck+bodyExtra)+k)} =
        (none,{afterCondition with clock := afterCondition.clock+(bodyExtra+k)}) := by
    have h := evaluate_add_clock_eq _ _ _ _ (bodyExtra+k) exprRun (by simp)
    simpa [initial,Nat.add_assoc] using h
  have evalValue : LoopSemStateFiniteExact.eval
      {afterCondition with clock := afterCondition.clock+(bodyExtra+k)} value = some (.word w) := by
    rw [eval_upd_clock_eq]
    simpa [wlabWlocExact] using exprValue
  have bodyEval := while_body_eval code value next live (compileHOLExact ctxt live body) _ _ w exprShift evalValue
  simp only [if_neg nonzero] at bodyEval
  have notTimeout : out ≠ some .timeOut := by
    rw [hresult]
    rcases continues with h | h <;> simp [h,resultToLoop]
  have hbodyK : evaluate (compileHOLExact ctxt live body)
      {bodyTarget with clock := bodyTarget.clock+(bodyExtra+k)} = (out,{post with clock := post.clock+k}) := by
    have shift := evaluate_add_clock_eq _ _ _ _ k hbody notTimeout
    simpa [Nat.add_assoc] using shift
  have seqRun : evaluate (.seq (compileHOLExact ctxt live body) (.continue 0))
      {bodyTarget with clock := bodyTarget.clock+(bodyExtra+k)} =
        (some (.continue 0),{post with clock := post.clock+k}) := by
    rcases continues with h | h
    · have outEq : out = none := by simpa [h,resultToLoop] using hresult
      rw [outEq] at hbodyK
      exact seq_continue_none hbodyK
    · have outEq : out = some (.continue 0) := by simpa [h,resultToLoop] using hresult
      rw [outEq] at hbodyK
      exact seq_continue_some hbodyK
  have bodyLoop : evaluate B {initial with clock := target.clock-1+((ck+bodyExtra)+k)} =
      (some (.continue 0),{post with clock := post.clock+k}) := by
    change evaluate (loopNestedSeqHOL (code ++ [.assign next value,
      .ite .notEqual next (.imm 0) (.seq (compileHOLExact ctxt live body) (.continue 0)) (.break 0) live])) _ = _
    rw [bodyEval]
    have : setVar next (.word w) {afterCondition with clock := afterCondition.clock+(bodyExtra+k)} =
        {bodyTarget with clock := bodyTarget.clock+(bodyExtra+k)} := by simp [bodyTarget,setVar]
    rw [this,seqRun]
    rfl
  rw [hcomp]
  exact loop_step_continue entry bodyLoop

/-- Break exits with a bounded condition and body clock plus the exit cut. -/
theorem branchCondition_break_run
    (condition : CrepExpHOL width) (conditionShape : CompiledScalar condition)
    (body : CrepProgHOL width) (bodyShape : BranchProgram body)
    (source sourcePost : CrepSemHOLState width F)
    (target : LoopSemStateFiniteExact width F) (ctxt : CrepToLoopContextExact) (live : NumSet)
    (w : BitVec width) (guard : evalCrepSemHOLExp source condition = some (.word w))
    (nonzero : w ≠ 0) (clockNonzero : source.clock ≠ 0)
    (bodyRun : evalCrepSemHOLProgExact (decClockCrepSemHOL source) body = (some (.break 0),sourcePost))
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    ∃ code value next outLive extra post,
      compileExpHOLExact ctxt (ctxt.vmax+1) live condition = (code,value,next,outLive) ∧
      extra ≤ sizeOf (loopNestedSeqHOL code) + sizeOf (compileHOLExact ctxt live body) + 1 ∧
      crepToLoopStateRelExact sourcePost post ∧
      crepToLoopMemRelHOLExact sourcePost.memory post.memory sourcePost.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourcePost.globals post.globals ∧
      crepToLoopCodeRelExact ctxt sourcePost.code post.code ∧
      crepToLoopLocalsRelExact ctxt live sourcePost.locals post.locals ∧
      evaluate (compileHOLExact ctxt live (.while condition body))
          {target with clock := target.clock + extra} = (none,post) := by
  have targetNonzero : target.clock ≠ 0 := stateRel.2.2.1 ▸ clockNonzero
  let initial := {target with locals := sptInter target.locals live, clock := target.clock-1}
  have initialLocals : crepToLoopLocalsRelExact ctxt live source.locals initial.locals :=
    locals_rel_inter ctxt live source.locals target.locals localsRel
  have initialState : crepToLoopStateRelExact (decClockCrepSemHOL source) initial := by
    simp only [crepToLoopStateRelExact,decClockCrepSemHOL,initial] at *
    exact ⟨stateRel.1,stateRel.2.1,by omega,stateRel.2.2.2⟩
  have guardDec : evalCrepSemHOLExp (decClockCrepSemHOL source) condition = some (.word w) := by
    simpa only [decClockCrepSemHOL,evalCrepSemHOLExp_upd_clock_eq] using guard
  obtain ⟨code,value,next,outLive,compiled,branch,_⟩ :=
    condition_prefix_shape conditionShape ctxt (ctxt.vmax+1) live
  obtain ⟨hok,htmp,hlive⟩ := compile_exp_out_rel ctxt (ctxt.vmax+1) live condition code value next outLive compiled
  have hsub : ∀ k, sptDomain live k → sptDomain outLive k :=
    fun k hk => hlive ▸ cut_sets_union_domain_subset _ live hok k hk
  have hfresh : ctxt.vmax < next := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) htmp
  obtain ⟨ck,afterCondition,exprRun,exprValue,exprState,exprMem,exprGlobals,exprCode,exprLocals⟩ :=
    crepToLoop_comp_exp_preserves_eval (decClockCrepSemHOL source) condition (.word w) initial ctxt
      (ctxt.vmax+1) live code value next outLive
      ⟨guardDec,initialState,memRel,globalsRel,codeRel,initialLocals,compiled,by omega⟩
  have conditionBound := condition_extraClock_bound (decClockCrepSemHOL source) initial afterCondition
    code ck branch initialState exprRun exprState
  let bodyTarget := setVar next (.word w) afterCondition
  have bodyLocals : crepToLoopLocalsRelExact ctxt live (decClockCrepSemHOL source).locals bodyTarget.locals := by
    exact locals_rel_insert_of ctxt live outLive source.locals _ afterCondition.locals initialLocals exprLocals hsub next hfresh _
  obtain ⟨bodyExtra,out,post,hbody,hstate,hmem,hglobals,hcode,hresult,hlocals,_,hbodyBound⟩ :=
    branchProgram_correct_with_bounded_extra body bodyShape (decClockCrepSemHOL source) sourcePost (some (.break 0))
      bodyTarget ctxt live bodyRun (by simp) exprState exprMem exprGlobals exprCode bodyLocals
  have outEq : out = some (.break 0) := by simpa [resultToLoop] using hresult
  rw [outEq] at hbody
  have hlocals' : crepToLoopLocalsRelExact ctxt live sourcePost.locals post.locals := by
    simpa [localsResultRel] using hlocals
  let final := {post with locals := sptInter post.locals live}
  refine ⟨code,value,next,outLive,ck+bodyExtra+1,final,compiled,by omega,?_,?_,?_,?_,?_,?_⟩
  · simpa [final,crepToLoopStateRelExact] using hstate
  · simpa [final] using hmem
  · simpa [final] using hglobals
  · simpa [final] using hcode
  · exact locals_rel_inter ctxt live sourcePost.locals post.locals hlocals'
  let k := 1
  let B := branchConditionWhileBody ctxt live code value next body
  have hcomp : compileHOLExact ctxt live (.while condition body) = .loop live B live := by
    simp [compileHOLExact,compiled,B,branchConditionWhileBody]
  have subset : sptSubsetLive live target.locals := localsRel.2.2.1
  have entry : cutRes live (none, {target with clock := target.clock+((ck+bodyExtra)+k)}) =
      (none, {initial with clock := target.clock-1+((ck+bodyExtra)+k)}) := by
    rw [cutRes]
    simp only
    rw [cutState_of_subset live {target with clock := target.clock+((ck+bodyExtra)+k)} subset]
    simp only [decClock,show ¬ target.clock+((ck+bodyExtra)+k)=0 by omega,if_false]
    simp only [initial,Prod.mk.injEq,true_and]
    congr 1
    omega
  have exprShift : evaluate (loopNestedSeqHOL code)
      {initial with clock := target.clock-1+((ck+bodyExtra)+k)} =
        (none,{afterCondition with clock := afterCondition.clock+(bodyExtra+k)}) := by
    have h := evaluate_add_clock_eq _ _ _ _ (bodyExtra+k) exprRun (by simp)
    simpa [initial,Nat.add_assoc] using h
  have evalValue : LoopSemStateFiniteExact.eval
      {afterCondition with clock := afterCondition.clock+(bodyExtra+k)} value = some (.word w) := by
    rw [eval_upd_clock_eq]
    simpa [wlabWlocExact] using exprValue
  have bodyEval := while_body_eval code value next live (compileHOLExact ctxt live body) _ _ w exprShift evalValue
  simp only [if_neg nonzero] at bodyEval
  have hbodyK : evaluate (compileHOLExact ctxt live body)
      {bodyTarget with clock := bodyTarget.clock+(bodyExtra+k)} =
        (some (.break 0),{post with clock := post.clock+k}) := by
    have shift := evaluate_add_clock_eq _ _ _ _ k hbody (by simp)
    simpa [Nat.add_assoc] using shift
  have seqRun : evaluate (.seq (compileHOLExact ctxt live body) (.continue 0))
      {bodyTarget with clock := bodyTarget.clock+(bodyExtra+k)} =
        (some (.break 0),{post with clock := post.clock+k}) := seq_continue_some hbodyK
  have bodyLoop : evaluate B {initial with clock := target.clock-1+((ck+bodyExtra)+k)} =
      (some (.break 0),{post with clock := post.clock+k}) := by
    change evaluate (loopNestedSeqHOL (code ++ [.assign next value,
      .ite .notEqual next (.imm 0) (.seq (compileHOLExact ctxt live body) (.continue 0)) (.break 0) live])) _ = _
    rw [bodyEval]
    have : setVar next (.word w) {afterCondition with clock := afterCondition.clock+(bodyExtra+k)} =
        {bodyTarget with clock := bodyTarget.clock+(bodyExtra+k)} := by simp [bodyTarget,setVar]
    rw [this,seqRun]
    rfl
  have subsetPost : sptSubsetLive live post.locals := hlocals'.2.2.1
  have exit : cutRes live (none, {post with clock := post.clock+k}) = (none,final) := by
    rw [cutRes]
    simp only
    rw [cutState_of_subset live {post with clock := post.clock+k} subsetPost]
    simp [decClock,k,final]
  rw [hcomp]
  exact (loop_step_break entry bodyLoop).trans exit

/-- A nonlocal result propagates with bounded condition and body clock. -/
theorem branchCondition_exit_run
    (condition : CrepExpHOL width) (conditionShape : CompiledScalar condition)
    (body : CrepProgHOL width) (bodyShape : BranchProgram body)
    (source sourcePost : CrepSemHOLState width F) (r : CrepResultHOLExact width)
    (target : LoopSemStateFiniteExact width F) (ctxt : CrepToLoopContextExact) (live : NumSet)
    (w : BitVec width) (guard : evalCrepSemHOLExp source condition = some (.word w))
    (nonzero : w ≠ 0) (clockNonzero : source.clock ≠ 0)
    (bodyRun : evalCrepSemHOLProgExact (decClockCrepSemHOL source) body = (some r,sourcePost))
    (notContinue : r ≠ .continue 0) (notBreak : r ≠ .break 0) (notError : r ≠ .error)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    ∃ code value next outLive extra post,
      compileExpHOLExact ctxt (ctxt.vmax+1) live condition = (code,value,next,outLive) ∧
      extra ≤ sizeOf (loopNestedSeqHOL code) + sizeOf (compileHOLExact ctxt live body) ∧
      crepToLoopStateRelExact sourcePost post ∧
      crepToLoopMemRelHOLExact sourcePost.memory post.memory sourcePost.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourcePost.globals post.globals ∧
      crepToLoopCodeRelExact ctxt sourcePost.code post.code ∧
      localsResultRel ctxt live (exitLoopCrepResult (some r)) sourcePost post ∧
      evaluate (compileHOLExact ctxt live (.while condition body))
          {target with clock := target.clock + extra} = (resultToLoop (exitLoopCrepResult (some r)),post) := by
  have targetNonzero : target.clock ≠ 0 := stateRel.2.2.1 ▸ clockNonzero
  let initial := {target with locals := sptInter target.locals live, clock := target.clock-1}
  have initialLocals : crepToLoopLocalsRelExact ctxt live source.locals initial.locals :=
    locals_rel_inter ctxt live source.locals target.locals localsRel
  have initialState : crepToLoopStateRelExact (decClockCrepSemHOL source) initial := by
    simp only [crepToLoopStateRelExact,decClockCrepSemHOL,initial] at *
    exact ⟨stateRel.1,stateRel.2.1,by omega,stateRel.2.2.2⟩
  have guardDec : evalCrepSemHOLExp (decClockCrepSemHOL source) condition = some (.word w) := by
    simpa only [decClockCrepSemHOL,evalCrepSemHOLExp_upd_clock_eq] using guard
  obtain ⟨code,value,next,outLive,compiled,branch,_⟩ :=
    condition_prefix_shape conditionShape ctxt (ctxt.vmax+1) live
  obtain ⟨hok,htmp,hlive⟩ := compile_exp_out_rel ctxt (ctxt.vmax+1) live condition code value next outLive compiled
  have hsub : ∀ k, sptDomain live k → sptDomain outLive k :=
    fun k hk => hlive ▸ cut_sets_union_domain_subset _ live hok k hk
  have hfresh : ctxt.vmax < next := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) htmp
  obtain ⟨ck,afterCondition,exprRun,exprValue,exprState,exprMem,exprGlobals,exprCode,exprLocals⟩ :=
    crepToLoop_comp_exp_preserves_eval (decClockCrepSemHOL source) condition (.word w) initial ctxt
      (ctxt.vmax+1) live code value next outLive
      ⟨guardDec,initialState,memRel,globalsRel,codeRel,initialLocals,compiled,by omega⟩
  have conditionBound := condition_extraClock_bound (decClockCrepSemHOL source) initial afterCondition
    code ck branch initialState exprRun exprState
  let bodyTarget := setVar next (.word w) afterCondition
  have bodyLocals : crepToLoopLocalsRelExact ctxt live (decClockCrepSemHOL source).locals bodyTarget.locals := by
    exact locals_rel_insert_of ctxt live outLive source.locals _ afterCondition.locals initialLocals exprLocals hsub next hfresh _
  obtain ⟨bodyExtra,out,post,hbody,hstate,hmem,hglobals,hcode,hresult,hlocals,_,hbodyBound⟩ :=
    branchProgram_correct_with_bounded_extra body bodyShape (decClockCrepSemHOL source) sourcePost (some r)
      bodyTarget ctxt live bodyRun (by simpa using notError) exprState exprMem exprGlobals exprCode bodyLocals
  obtain ⟨x,outEq⟩ : ∃ x, out = some x := by
    cases r <;> simp only [resultToLoop] at hresult <;> exact ⟨_,hresult⟩
  have x0 : x ≠ .continue 0 := by
    intro h; subst h; cases r <;> simp_all [resultToLoop]
  have x1 : x ≠ .break 0 := by
    intro h; subst h; cases r <;> simp_all [resultToLoop]
  rw [outEq] at hbody
  refine ⟨code,value,next,outLive,ck+bodyExtra,post,compiled,by omega,hstate,hmem,hglobals,hcode,?_,?_⟩
  · exact localsResultRel_exitLoop ctxt live sourcePost post r hlocals
  let k := 0
  let B := branchConditionWhileBody ctxt live code value next body
  have hcomp : compileHOLExact ctxt live (.while condition body) = .loop live B live := by
    simp [compileHOLExact,compiled,B,branchConditionWhileBody]
  have subset : sptSubsetLive live target.locals := localsRel.2.2.1
  have entry : cutRes live (none, {target with clock := target.clock+((ck+bodyExtra)+k)}) =
      (none, {initial with clock := target.clock-1+((ck+bodyExtra)+k)}) := by
    rw [cutRes]
    simp only
    rw [cutState_of_subset live {target with clock := target.clock+((ck+bodyExtra)+k)} subset]
    simp only [decClock,show ¬ target.clock+((ck+bodyExtra)+k)=0 by omega,if_false]
    simp only [initial,Prod.mk.injEq,true_and]
    congr 1
    omega
  have exprShift : evaluate (loopNestedSeqHOL code)
      {initial with clock := target.clock-1+((ck+bodyExtra)+k)} =
        (none,{afterCondition with clock := afterCondition.clock+(bodyExtra+k)}) := by
    have h := evaluate_add_clock_eq _ _ _ _ (bodyExtra+k) exprRun (by simp)
    simpa [initial,Nat.add_assoc] using h
  have evalValue : LoopSemStateFiniteExact.eval
      {afterCondition with clock := afterCondition.clock+(bodyExtra+k)} value = some (.word w) := by
    rw [eval_upd_clock_eq]
    simpa [wlabWlocExact] using exprValue
  have bodyEval := while_body_eval code value next live (compileHOLExact ctxt live body) _ _ w exprShift evalValue
  simp only [if_neg nonzero] at bodyEval
  have hbodyK : evaluate (compileHOLExact ctxt live body)
      {bodyTarget with clock := bodyTarget.clock+(bodyExtra+k)} = (some x,post) := by
    simpa [k] using hbody
  have seqRun : evaluate (.seq (compileHOLExact ctxt live body) (.continue 0))
      {bodyTarget with clock := bodyTarget.clock+(bodyExtra+k)} = (some x,post) := seq_continue_some hbodyK
  have bodyLoop : evaluate B {initial with clock := target.clock-1+((ck+bodyExtra)+k)} =
      (some x,post) := by
    change evaluate (loopNestedSeqHOL (code ++ [.assign next value,
      .ite .notEqual next (.imm 0) (.seq (compileHOLExact ctxt live body) (.continue 0)) (.break 0) live])) _ = _
    rw [bodyEval]
    have : setVar next (.word w) {afterCondition with clock := afterCondition.clock+(bodyExtra+k)} =
        {bodyTarget with clock := bodyTarget.clock+(bodyExtra+k)} := by simp [bodyTarget,setVar]
    rw [this,seqRun]
    rfl
  rw [hcomp]
  have resultEq : exitLoop (some x) = resultToLoop (exitLoopCrepResult (some r)) := by
    rw [outEq] at hresult
    rw [hresult]
    exact resultToLoop_exitLoop r notContinue notBreak
  simpa [k,resultEq] using (loop_step_exit (L' := live) x0 x1 entry bodyLoop)

end SteppedFlapjack.CrepToLoopSteps
