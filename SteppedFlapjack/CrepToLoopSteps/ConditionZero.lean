import SteppedFlapjack.CrepToLoopSteps.ConditionShape

/-! False-guard simulation for comparison conditions. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
variable {width : Nat} [NeZero width] {F : Type}

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


/-- A false branch condition exits the compiled loop with clock bounded by the
condition-prefix size plus the two loop cuts. -/
theorem branchCondition_false_run
    (condition : CrepExpHOL width) (shape : CompiledScalar condition)
    (body : CrepProgHOL width) (source : CrepSemHOLState width F)
    (target : LoopSemStateFiniteExact width F) (ctxt : CrepToLoopContextExact) (live : NumSet)
    (guard : evalCrepSemHOLExp source condition = some (.word 0))
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    ∃ code value next outLive extra post,
      compileExpHOLExact ctxt (ctxt.vmax+1) live condition = (code,value,next,outLive) ∧
      extra ≤ sizeOf (loopNestedSeqHOL code) + 2 ∧
      evaluate (compileHOLExact ctxt live (.while condition body))
        {target with clock := target.clock+extra} = (none,post) ∧
      crepToLoopStateRelExact source post ∧
      crepToLoopMemRelHOLExact source.memory post.memory source.memaddrs ∧
      crepToLoopGlobalsRelHOLExact source.globals post.globals ∧
      crepToLoopCodeRelExact ctxt source.code post.code ∧
      crepToLoopLocalsRelExact ctxt live source.locals post.locals := by
  obtain ⟨code,value,next,outLive,compiled,branch,_⟩ :=
    condition_prefix_shape shape ctxt (ctxt.vmax+1) live
  obtain ⟨hok,htmp,hlive⟩ := compile_exp_out_rel ctxt (ctxt.vmax+1) live condition code value next outLive compiled
  have hsub : ∀ k, sptDomain live k → sptDomain outLive k :=
    fun k hk => hlive ▸ cut_sets_union_domain_subset _ live hok k hk
  have hfresh : ctxt.vmax < next := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) htmp
  let initial := {target with locals := sptInter target.locals live}
  have initialLocals : crepToLoopLocalsRelExact ctxt live source.locals initial.locals :=
    locals_rel_inter ctxt live source.locals target.locals localsRel
  have initialState : crepToLoopStateRelExact source initial := by
    simpa [initial,crepToLoopStateRelExact] using stateRel
  obtain ⟨ck,post,he,hval,hs,hm,hg,hc,hl⟩ :=
    crepToLoop_comp_exp_preserves_eval source condition (.word 0) initial ctxt (ctxt.vmax+1) live
      code value next outLive ⟨guard,initialState,memRel,globalsRel,codeRel,initialLocals,compiled,by omega⟩
  have ckBound := condition_extraClock_bound source initial post code ck branch initialState he hs
  let B := branchConditionWhileBody ctxt live code value next body
  have hcomp : compileHOLExact ctxt live (.while condition body) = .loop live B live := by
    simp [compileHOLExact,compiled,B,branchConditionWhileBody]
  have subset : LoopSemStateFiniteExact.sptSubsetLive live target.locals := localsRel.2.2.1
  have entry : cutRes live (none, {target with clock := target.clock+(ck+2)}) =
      (none, {initial with clock := target.clock+(ck+1)}) := by
    rw [cutRes]
    simp only
    rw [cutState_of_subset live {target with clock := target.clock+(ck+2)} subset]
    simp [decClock,initial]
  have shifted : evaluate (loopNestedSeqHOL code) {initial with clock := target.clock+(ck+1)} =
      (none,{post with clock := post.clock+1}) := by
    have h := evaluate_add_clock_eq _ _ _ _ 1 he (by simp)
    simpa [initial,Nat.add_assoc] using h
  have bodyRun := while_body_eval code value next live (compileHOLExact ctxt live body) _ _ 0 shifted
    (by rw [eval_upd_clock_eq]; simpa [wlabWlocExact] using hval)
  have loopRun := loop_step_break (L' := live) entry bodyRun
  have subsetPost : LoopSemStateFiniteExact.sptSubsetLive live
      (setVar next (.word 0) {post with clock := post.clock+1}).locals :=
    fun k hk => (sptMem_sptInsert k next _ _).mpr (Or.inr (hl.2.2.1 k (hsub k hk)))
  let final := {post with locals := sptInter (sptInsert next (.word 0) post.locals) live}
  have exit : cutRes live (none,setVar next (.word 0) {post with clock := post.clock+1}) = (none,final) := by
    rw [cutRes]
    simp only
    rw [cutState_of_subset live _ subsetPost]
    simp [decClock,setVar,final]
  refine ⟨code,value,next,outLive,ck+2,final,compiled,by omega,?_,?_,?_,?_,?_,?_⟩
  · rw [hcomp]
    exact loopRun.trans exit
  · simpa [final,crepToLoopStateRelExact] using hs
  · simpa [final] using hm
  · simpa [final] using hg
  · simpa [final] using hc
  · exact locals_rel_inter ctxt live source.locals _
      (locals_rel_insert_of ctxt live outLive source.locals _ post.locals initialLocals hl hsub next hfresh _)

end SteppedFlapjack.CrepToLoopSteps
