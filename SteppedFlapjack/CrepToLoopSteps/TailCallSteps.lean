import SteppedFlapjack.CrepToLoopSteps.ScalarClockCompositional
import Flapjack.Pancake.Proofs.LoopLive.Optimise
import SteppedFlapjack.CrepToLoopSteps.InlineEntry
import SteppedFlapjack.CrepToLoopSteps.DirectExpressionEval
import SteppedFlapjack.LoopSteps.Defs
import SteppedFlapjack.LoopLiveSteps.Consumption
import SteppedFlapjack.LoopLiveSteps.TailEntryCode
import Flapjack.Pancake.CrepToLoop.StateRel
import SteppedFlapjack.CrepToLoopSteps.ConditionPrefix
import SteppedFlapjack.CrepToLoopSteps.WordSimpSequence
import SteppedFlapjack.CrepToLoopSteps.BackendReady

/-! Source-shaped bounds for compiled zero-argument Crep tail calls. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- Direct argument expressions compile without auxiliary Loop code. -/
theorem directExpressions_noCode {width : Nat} [NeZero width]
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, DirectExpression e)
    (ctxt : CrepToLoopContextExact) (tmp : Nat) (live : NumSet) :
    ∃ values, compileExpsHOLExact ctxt tmp live args = ([],values,tmp,live) ∧ values.length = args.length := by
  induction args with
  | nil => exact ⟨[],by simp [compileExpsHOLExact],rfl⟩
  | cons e es ih =>
    obtain ⟨value,head⟩ := directExpression_noCode (shape e (by simp)) ctxt tmp live
    obtain ⟨values,tail,len⟩ := ih (fun x hx => shape x (by simp [hx]))
    refine ⟨value :: values,?_,by simp [len]⟩
    simp [compileExpsHOLExact,head,tail]

/-- Direct call arguments are assigned to fresh Loop temporaries without extra clock. -/
theorem directCall_argumentPrefix {width : Nat} [NeZero width] {σ : Type}
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, DirectExpression e)
    (source : CrepSemHOLState width σ) (values : List (HolWordLab width))
    (target : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (live : NumSet)
    (evaluated : args.mapM (evalCrepSemHOLExp source) = some values)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    ∃ les, compileExpsHOLExact ctxt (ctxt.vmax+1) live args = ([],les,ctxt.vmax+1,live) ∧
      let regs := genTemps (ctxt.vmax+1) args.length
      let vals := values.map wlabWlocExact
      evaluate (loopNestedSeqHOL (regs.zipWith HolLoopProg.assign les)) target =
        (none,{target with locals := sptAlistInsert regs vals target.locals}) ∧
      getVars regs {target with locals := sptAlistInsert regs vals target.locals} = some vals ∧
      sptSubsetLive live (sptAlistInsert regs vals target.locals) := by
  obtain ⟨les,compiled,heval⟩ := directExpressions_preserves_eval args shape source values target ctxt (ctxt.vmax+1) live
    evaluated stateRel memRel globalsRel codeRel localsRel (Nat.lt_succ_self _)
  let regs := genTemps (ctxt.vmax+1) args.length
  let vals := values.map wlabWlocExact
  have len : les.length = args.length := by
    have h1 := congrArg List.length ((optMmapEqSome les _ _).mp heval)
    have h2 := congrArg List.length ((optMmapEqSome args _ _).mp evaluated)
    simp only [List.length_map] at h1 h2
    omega
  have valuesLen : values.length = args.length := by
    have h := congrArg List.length ((optMmapEqSome args _ _).mp evaluated)
    simpa using h.symm
  have nodup : regs.Nodup := by
    simp only [regs,genTemps,List.Nodup,List.pairwise_map]
    exact List.nodup_range.imp (fun h => by omega)
  have disjoint : distinctListsHol regs (les.map holLoopLocalsTouched).flatten = true := by
    simp only [distinctListsHol,List.all_eq_true,decide_eq_true_eq]
    intro x hx hmem
    have hx' : ctxt.vmax+1 ≤ x := by
      simp only [regs,genTemps,List.mem_map,List.mem_range] at hx
      obtain ⟨a,_,rfl⟩ := hx
      omega
    have h := (compile_exps_le_tmp_domain ctxt (ctxt.vmax+1) live args [] les (ctxt.vmax+1) live x
      ⟨localsRel.2.1,compiled,Nat.lt_succ_self _,fun k hk => by
        obtain ⟨w,hw⟩ := crepOptMmapEval_some_var_cexp_local_lookup source args values k ⟨evaluated,hk⟩
        obtain ⟨m,hm1,hm2,_⟩ := localsRel.2.2.2 k w hw
        exact ⟨m,hm1,hm2⟩,hmem⟩).1
    omega
  have regsLen : regs.length = les.length := by simp [regs,genTemps,len]
  have valsLen : regs.length = vals.length := by simp [regs,genTemps,vals,valuesLen]
  have mapped := (optMmapEqSome les _ _).mp heval
  have run := loop_eval_nested_assign_distinct_eq les regs target vals ⟨mapped,disjoint,nodup,regsLen⟩
  have get := get_vars_local_update_some_eq regs vals target nodup valsLen
  have subset : sptSubsetLive live (sptAlistInsert regs vals target.locals) := by
    intro k hk
    have present := localsRel.2.2.1 k hk
    show (sptLookup k (sptAlistInsert regs vals target.locals)).isSome
    rw [lookup_alist_insert_any]
    split
    · exact present
    · rfl
  exact ⟨les,compiled,run,get,subset⟩

/-- Scalar call arguments are evaluated and assigned to the compiler's fresh
registers with an explicit bound for the expression prefix. -/
theorem scalarCall_argumentPrefix {width : Nat} [NeZero width] {σ : Type}
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, CompiledScalar e)
    (source : CrepSemHOLState width σ) (values : List (HolWordLab width))
    (target : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (live : NumSet)
    (evaluated : args.mapM (evalCrepSemHOLExp source) = some values)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    let comp := compileExpsHOLExact ctxt (ctxt.vmax+1) live args
    let regs := genTemps comp.2.2.1 comp.2.1.length
    let vals := values.map wlabWlocExact
    ∃ extra post,
      evaluate (loopNestedSeqHOL comp.1) {target with clock := target.clock+extra} = (none,post) ∧
      evaluate (loopNestedSeqHOL (regs.zipWith HolLoopProg.assign comp.2.1)) post =
        (none,{post with locals := sptAlistInsert regs vals post.locals}) ∧
      getVars regs {post with locals := sptAlistInsert regs vals post.locals} = some vals ∧
      sptSubsetLive live (sptAlistInsert regs vals post.locals) ∧
      crepToLoopStateRelExact source post ∧
      crepToLoopMemRelHOLExact source.memory post.memory source.memaddrs ∧
      crepToLoopGlobalsRelHOLExact source.globals post.globals ∧
      crepToLoopCodeRelExact ctxt source.code post.code ∧
      crepToLoopLocalsRelExact ctxt comp.2.2.2 source.locals post.locals ∧
      extra ≤ LoopSteps.structuralWeight (loopNestedSeqHOL comp.1) := by
  obtain ⟨code,les,next,outLive,compiled,len,prefixShape⟩ :=
    compiledScalars_prefix args shape ctxt (ctxt.vmax+1) live
  obtain ⟨extra,post,run,heval,postState,postMem,postGlobals,postCode,postLocals,bound⟩ :=
    scalarExpressions_preserves_eval_bounded args shape source values target ctxt (ctxt.vmax+1) live
      evaluated stateRel memRel globalsRel codeRel localsRel (Nat.lt_succ_self _)
  simp only [compiled] at run heval postLocals bound
  obtain ⟨syntaxOk,tempLe,liveEq,_⟩ := compile_exp_out_rel_cases.2 ctxt (ctxt.vmax+1) live args code les next outLive compiled
  let regs := genTemps next les.length
  let vals := values.map wlabWlocExact
  have valsLen : vals.length = les.length := by
    have h := congrArg List.length ((optMmapEqSome les _ _).mp heval)
    simpa [vals] using h.symm
  have nodup : regs.Nodup := by
    simp only [regs,genTemps,List.Nodup,List.pairwise_map]
    exact List.nodup_range.imp (fun h => by omega)
  have disjoint : distinctListsHol regs (les.map holLoopLocalsTouched).flatten = true := by
    simp only [distinctListsHol,List.all_eq_true,decide_eq_true_eq]
    intro x hx hmem
    have hx' : next ≤ x := by
      simp only [regs,genTemps,List.mem_map,List.mem_range] at hx
      obtain ⟨a,_,rfl⟩ := hx
      omega
    have h := (compile_exps_le_tmp_domain ctxt (ctxt.vmax+1) live args code les next outLive x
      ⟨localsRel.2.1,compiled,Nat.lt_succ_self _,fun k hk => by
        obtain ⟨w,hw⟩ := crepOptMmapEval_some_var_cexp_local_lookup source args values k ⟨evaluated,hk⟩
        obtain ⟨m,hm1,hm2,_⟩ := localsRel.2.2.2 k w hw
        exact ⟨m,hm1,hm2⟩,hmem⟩).1
    omega
  have regsLen : regs.length = les.length := by simp [regs,genTemps]
  have runAssign := loop_eval_nested_assign_distinct_eq les regs post vals
    ⟨(optMmapEqSome les _ _).mp heval,disjoint,nodup,regsLen⟩
  have get := get_vars_local_update_some_eq regs vals post nodup (by simp [regs,genTemps,valsLen])
  have subset : sptSubsetLive live (sptAlistInsert regs vals post.locals) := by
    intro k hk
    have present := postLocals.2.2.1 k (liveEq ▸ cut_sets_union_domain_subset _ live syntaxOk k hk)
    show (sptLookup k (sptAlistInsert regs vals post.locals)).isSome
    rw [lookup_alist_insert_any]
    split
    · exact present
    · rfl
  simpa only [compiled] using
    (show ∃ extra post, evaluate (loopNestedSeqHOL code) {target with clock := target.clock+extra} = (none,post) ∧
      evaluate (loopNestedSeqHOL (regs.zipWith HolLoopProg.assign les)) post =
        (none,{post with locals := sptAlistInsert regs vals post.locals}) ∧
      getVars regs {post with locals := sptAlistInsert regs vals post.locals} = some vals ∧
      sptSubsetLive live (sptAlistInsert regs vals post.locals) ∧
      crepToLoopStateRelExact source post ∧
      crepToLoopMemRelHOLExact source.memory post.memory source.memaddrs ∧
      crepToLoopGlobalsRelHOLExact source.globals post.globals ∧
      crepToLoopCodeRelExact ctxt source.code post.code ∧
      crepToLoopLocalsRelExact ctxt outLive source.locals post.locals ∧
      extra ≤ LoopSteps.structuralWeight (loopNestedSeqHOL code) from
      ⟨extra,post,run,runAssign,get,subset,postState,postMem,postGlobals,postCode,postLocals,bound⟩)

/-- A concrete clock budget executes the actual call-argument prefix and retains its code table. -/
theorem scalarCall_argumentPrefix_explicit {width : Nat} [NeZero width] {σ : Type}
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, CompiledScalar e)
    (source : CrepSemHOLState width σ) (values : List (HolWordLab width))
    (target : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (live : NumSet)
    (budget : Nat)
    (evaluated : args.mapM (evalCrepSemHOLExp source) = some values)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (budgetBound : LoopSteps.structuralWeight (loopNestedSeqHOL
      (compileExpsHOLExact ctxt (ctxt.vmax+1) live args).1) ≤ budget) :
    let comp := compileExpsHOLExact ctxt (ctxt.vmax+1) live args
    let regs := genTemps comp.2.2.1 comp.2.1.length
    let vals := values.map wlabWlocExact
    ∃ post,
      evaluate (loopNestedSeqHOL comp.1) {target with clock := target.clock+budget} = (none,post) ∧
      evaluate (loopNestedSeqHOL (regs.zipWith HolLoopProg.assign comp.2.1)) post =
        (none,{post with locals := sptAlistInsert regs vals post.locals}) ∧
      getVars regs {post with locals := sptAlistInsert regs vals post.locals} = some vals ∧
      sptSubsetLive live (sptAlistInsert regs vals post.locals) ∧
      source.clock ≤ post.clock ∧
      crepToLoopStateRelExact source {post with clock := source.clock} ∧
      crepToLoopMemRelHOLExact source.memory post.memory source.memaddrs ∧
      crepToLoopGlobalsRelHOLExact source.globals post.globals ∧
      crepToLoopCodeRelExact ctxt source.code post.code ∧
      post.code = target.code ∧
      crepToLoopLocalsRelExact ctxt comp.2.2.2 source.locals post.locals := by
  obtain ⟨extra,post,run,assign,get,subset,st,mem,gl,code,locals,bound⟩ :=
    scalarCall_argumentPrefix args shape source values target ctxt live evaluated stateRel memRel globalsRel codeRel localsRel
  let comp := compileExpsHOLExact ctxt (ctxt.vmax+1) live args
  let regs := genTemps comp.2.2.1 comp.2.1.length
  let vals := values.map wlabWlocExact
  let middle : LoopSemStateFiniteExact width σ := {post with locals := sptAlistInsert regs vals post.locals}
  let delta := budget - extra
  have clockEq : target.clock + extra + delta = target.clock + budget := by
    dsimp [delta]
    omega
  have prefixShift := evaluate_add_clock_eq (loopNestedSeqHOL comp.1)
    {target with clock := target.clock+extra} none post delta run (by simp)
  have assignShift := evaluate_add_clock_eq (loopNestedSeqHOL (regs.zipWith HolLoopProg.assign comp.2.1))
    post none middle delta assign (by simp)
  have getShift : getVars regs {middle with clock := middle.clock + delta} = some vals := by
    rw [getVars_upd_clock]
    exact get
  have codeSame : post.code = target.code := by
    have h := SteppedFlapjack.LoopLiveSteps.evaluate_code (loopNestedSeqHOL comp.1)
      {target with clock := target.clock+extra} post none run
    exact h
  refine ⟨{post with clock := post.clock+delta},?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [clockEq] using prefixShift
  · simpa [middle] using assignShift
  · simpa [middle] using getShift
  · exact subset
  · have clock := st.2.2.1
    simp only
    omega
  · have clock := st.2.2.1
    simpa [crepToLoopStateRelExact,clock] using st
  · exact mem
  · exact gl
  · exact code
  · exact codeSame
  · exact locals

/-- Direct arguments are assigned to temporaries before a tail call. -/
theorem compile_tailCall_direct {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : Flapjack.Basis.Pure.MlString.MlString)
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, DirectExpression e) :
    ∃ values, values.length = args.length ∧
      compileHOLExact ctxt live (.call none name args) =
        loopNestedSeqHOL ((genTemps (ctxt.vmax+1) args.length).zipWith HolLoopProg.assign values ++
          [.call none (some (findLabExact ctxt name)) (genTemps (ctxt.vmax+1) args.length) none]) := by
  obtain ⟨values,compiled,len⟩ := directExpressions_noCode args shape ctxt (ctxt.vmax+1) live
  refine ⟨values,len,?_⟩
  simp [compileHOLExact,compiled,len]

/-- Direct arguments are assigned to temporaries before a returning call. -/
theorem compile_returningCall_direct {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : Flapjack.Basis.Pure.MlString.MlString)
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, DirectExpression e)
    (names returnNames : List Nat) (mapped : names.mapM ctxt.vars.lookup = some returnNames) :
    ∃ values, values.length = args.length ∧
      compileHOLExact ctxt live (.call (some (names,none)) name args) =
        loopNestedSeqHOL ((genTemps (ctxt.vmax+1) args.length).zipWith HolLoopProg.assign values ++
          [.call (some (returnNames,live)) (some (findLabExact ctxt name)) (genTemps (ctxt.vmax+1) args.length)
            (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))]) := by
  obtain ⟨values,compiled,len⟩ := directExpressions_noCode args shape ctxt (ctxt.vmax+1) live
  refine ⟨values,len,?_⟩
  simp [compileHOLExact,compiled,len,mapped]

/-- Generated argument assignments cost at most two visits each, plus the
reached call and its final wrapper. -/
theorem assignmentPrefix_steps {width : Nat} [NeZero width] {F : Type}
    (registers : List Nat) (values : List (HolLoopExp width)) (call : HolLoopProg width)
    (s : LoopSemStateFiniteExact width F) :
    LoopSteps.steps (loopNestedSeqHOL (registers.zipWith HolLoopProg.assign values ++ [call])) s ≤
      2 * (registers.zip values).length + 2 +
        match evaluate (loopNestedSeqHOL (registers.zipWith HolLoopProg.assign values)) s with
        | (none,t) => LoopSteps.steps call t
        | _ => 0 := by
  induction registers generalizing values s with
  | nil =>
    simp only [List.zipWith_nil_left,List.zip_nil_left,List.length_nil,List.nil_append,loopNestedSeqHOL,LoopSteps.steps_seq,evaluate]
    rcases run : evaluate call s with ⟨out,post⟩
    cases out with
    | none =>
      simp only
      have h := LoopSteps.steps_leaf (.skip : HolLoopProg width) post rfl
      omega
    | some r => simp only; omega
  | cons reg rest ih =>
    cases values with
    | nil =>
      simp only [List.zipWith_nil_right,List.zip_nil_right,List.length_nil,List.nil_append,loopNestedSeqHOL,LoopSteps.steps_seq,evaluate]
      rcases run : evaluate call s with ⟨out,post⟩
      cases out with
      | none =>
        simp only
        have h := LoopSteps.steps_leaf (.skip : HolLoopProg width) post rfl
        omega
      | some r => simp only; omega
    | cons exp es =>
      simp only [List.zipWith_cons_cons,List.zip_cons_cons,List.length_cons,List.cons_append,loopNestedSeqHOL,LoopSteps.steps_seq,evaluate_seq]
      have leaf := LoopSteps.steps_leaf (.assign reg exp : HolLoopProg width) s rfl
      rcases run : evaluate (.assign reg exp : HolLoopProg width) s with ⟨out,post⟩
      cases out with
      | none =>
        simp only
        have bound := ih es post
        omega
      | some r => simp only; omega

section ScalarPrefixVisits
open SteppedFlapjack.LoopSteps

/-- A successful nested prefix contributes its visits before the suffix. -/
theorem nestedSeq_append_steps {width : Nat} [NeZero width] {σ : Type}
    (code rest : List (HolLoopProg width)) (s post : LoopSemStateFiniteExact width σ)
    (run : evaluate (loopNestedSeqHOL code) s = (none,post)) :
    steps (loopNestedSeqHOL (code ++ rest)) s ≤
      steps (loopNestedSeqHOL code) s + steps (loopNestedSeqHOL rest) post := by
  induction code generalizing s post with
  | nil =>
    simp only [loopNestedSeqHOL,evaluate,Prod.mk.injEq] at run
    obtain ⟨_,rfl⟩ := run
    simp only [List.nil_append]
    omega
  | cons p ps ih =>
    simp only [loopNestedSeqHOL,evaluate_seq] at run
    rcases first : evaluate p s with ⟨out,middle⟩
    rw [first] at run
    cases out with
    | some result => simp at run
    | none =>
      simp only at run
      have tail := ih middle post run
      simp only [List.cons_append,loopNestedSeqHOL,steps_seq,first]
      omega
/-- A successful scalar argument prefix and its assignments have a concrete
visit cost computed from the generated code and argument count. -/
theorem scalarCall_prefix_visits {width : Nat} [NeZero width] {σ : Type}
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, CompiledScalar e)
    (ctxt : CrepToLoopContextExact) (live : NumSet) (call : HolLoopProg width)
    (s post : LoopSemStateFiniteExact width σ)
    (run : evaluate (loopNestedSeqHOL (compileExpsHOLExact ctxt (ctxt.vmax+1) live args).1) s = (none,post)) :
    let comp := compileExpsHOLExact ctxt (ctxt.vmax+1) live args
    let regs := genTemps comp.2.2.1 comp.2.1.length
    steps (loopNestedSeqHOL (comp.1 ++ regs.zipWith HolLoopProg.assign comp.2.1 ++ [call])) s ≤
      structuralWeight (loopNestedSeqHOL comp.1) + 2*args.length + 2 +
        match evaluate (loopNestedSeqHOL (regs.zipWith HolLoopProg.assign comp.2.1)) post with
        | (none,t) => steps call t
        | _ => 0 := by
  obtain ⟨code,les,next,outLive,compiled,len,prefixShape⟩ :=
    compiledScalars_prefix args shape ctxt (ctxt.vmax+1) live
  simp only [compiled] at run ⊢
  have count := nestedSeq_append_steps code (List.zipWith HolLoopProg.assign (genTemps next les.length) les ++ [call]) s post run
  have static := branchedProgram_structural_bound (nestedSeq_branched code prefixShape.1) s
  have suffix := assignmentPrefix_steps (genTemps next les.length) les call post
  rw [List.append_assoc]
  have zipLen : ((genTemps next les.length).zip les).length = args.length := by simp [genTemps,len]
  simp only [zipLen] at suffix ⊢
  cases h : evaluate (loopNestedSeqHOL (List.zipWith HolLoopProg.assign (genTemps next les.length) les)) post with
  | mk out st => cases out <;> simp only [h] at * <;> omega


end ScalarPrefixVisits

/-- The exact compiler output for tail and ordinary calls has the concrete
argument-prefix visit bound, once that prefix has executed. -/
theorem compiledScalarCall_prefix_steps {width : Nat} [NeZero width] {σ : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : MlString)
    (names : Option (List Nat)) (args : List (CrepExpHOL width))
    (shape : ∀ e ∈ args, CompiledScalar e) (s post : LoopSemStateFiniteExact width σ)
    (run : evaluate (loopNestedSeqHOL (compileExpsHOLExact ctxt (ctxt.vmax+1) live args).1) s = (none,post)) :
    let comp := compileExpsHOLExact ctxt (ctxt.vmax+1) live args
    let regs := genTemps comp.2.2.1 comp.2.1.length
    let call : HolLoopProg width := match names with
      | none => .call none (some (findLabExact ctxt name)) regs none
      | some ns =>
        let returnNames := (ns.mapM ctxt.vars.lookup).getD [ctxt.vmax+2]
        .call (some (returnNames,live)) (some (findLabExact ctxt name)) regs
          (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))
    LoopSteps.steps (compileHOLExact ctxt live (.call (names.map (fun ns => (ns,none))) name args)) s ≤
      LoopSteps.structuralWeight (loopNestedSeqHOL comp.1) + 2*args.length + 2 +
        match evaluate (loopNestedSeqHOL (regs.zipWith HolLoopProg.assign comp.2.1)) post with
        | (none,t) => LoopSteps.steps call t
        | _ => 0 := by
  obtain ⟨code,les,next,outLive,compiled,len,prefixShape⟩ :=
    compiledScalars_prefix args shape ctxt (ctxt.vmax+1) live
  have bound := scalarCall_prefix_visits args shape ctxt live
    (match names with
      | none => .call none (some (findLabExact ctxt name)) (genTemps next les.length) none
      | some ns => .call (some ((ns.mapM ctxt.vars.lookup).getD [ctxt.vmax+2],live))
          (some (findLabExact ctxt name)) (genTemps next les.length)
          (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))) s post run
  simp only [compiled] at bound ⊢
  cases names with
  | none =>
    simp only [Option.map_none,compileHOLExact,compiled] at ⊢
    exact bound
  | some ns =>
    simp only [Option.map_some,compileHOLExact,compiled] at ⊢
    cases h : ns.mapM ctxt.vars.lookup <;> simp only [h,Option.getD] at bound ⊢ <;> exact bound

/-- A scalar-argument call reaches its actual call node after a bounded prefix,
with the source arguments in the fresh target registers. -/
theorem compiledScalarCall_reaches_call {width : Nat} [NeZero width] {σ : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : MlString)
    (names : Option (List Nat)) (args : List (CrepExpHOL width))
    (shape : ∀ e ∈ args, CompiledScalar e)
    (source : CrepSemHOLState width σ) (values : List (HolWordLab width))
    (target : LoopSemStateFiniteExact width σ)
    (evaluated : args.mapM (evalCrepSemHOLExp source) = some values)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    let comp := compileExpsHOLExact ctxt (ctxt.vmax+1) live args
    let regs := genTemps comp.2.2.1 comp.2.1.length
    let vals := values.map wlabWlocExact
    let call : HolLoopProg width := match names with
      | none => .call none (some (findLabExact ctxt name)) regs none
      | some ns => .call (some ((ns.mapM ctxt.vars.lookup).getD [ctxt.vmax+2],live))
          (some (findLabExact ctxt name)) regs (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))
    ∃ (extra : Nat) (post : LoopSemStateFiniteExact width σ),
      let middle : LoopSemStateFiniteExact width σ := {post with locals := sptAlistInsert regs vals post.locals}
      evaluate (loopNestedSeqHOL comp.1) {target with clock := target.clock+extra} = (none,post) ∧
      evaluate (loopNestedSeqHOL (regs.zipWith HolLoopProg.assign comp.2.1)) post = (none,middle) ∧
      getVars regs middle = some vals ∧ sptSubsetLive live middle.locals ∧
      crepToLoopStateRelExact source post ∧
      crepToLoopMemRelHOLExact source.memory post.memory source.memaddrs ∧
      crepToLoopGlobalsRelHOLExact source.globals post.globals ∧
      crepToLoopCodeRelExact ctxt source.code post.code ∧
      crepToLoopLocalsRelExact ctxt comp.2.2.2 source.locals post.locals ∧
      extra ≤ LoopSteps.structuralWeight (loopNestedSeqHOL comp.1) ∧
      LoopSteps.steps (compileHOLExact ctxt live (.call (names.map (fun ns => (ns,none))) name args))
        {target with clock := target.clock+extra} ≤
          LoopSteps.structuralWeight (loopNestedSeqHOL comp.1) + 2*args.length + 2 + LoopSteps.steps call middle := by
  obtain ⟨extra,post,prefixRun,assign,get,subset,state,mem,globals,code,locals,bound⟩ :=
    scalarCall_argumentPrefix args shape source values target ctxt live evaluated stateRel memRel globalsRel codeRel localsRel
  have visits := compiledScalarCall_prefix_steps ctxt live name names args shape
    {target with clock := target.clock+extra} post prefixRun
  dsimp only at visits
  rw [assign] at visits
  simp only at visits
  exact ⟨extra,post,prefixRun,assign,get,subset,state,mem,globals,code,locals,bound,visits⟩

/-- The direct-argument tail-call wrapper has linear cost in its arity. -/
theorem compile_tailCall_direct_steps {width : Nat} [NeZero width] {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : Flapjack.Basis.Pure.MlString.MlString)
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, DirectExpression e)
    (s : LoopSemStateFiniteExact width F) :
    let values := (compileExpsHOLExact ctxt (ctxt.vmax+1) live args).2.1
    let regs := genTemps (ctxt.vmax+1) args.length
      let call : HolLoopProg width := .call none (some (findLabExact ctxt name)) regs none
      LoopSteps.steps (compileHOLExact ctxt live (.call none name args)) s ≤
        2 * args.length + 2 +
          match evaluate (loopNestedSeqHOL (regs.zipWith HolLoopProg.assign values)) s with
          | (none,t) => LoopSteps.steps call t
          | _ => 0 := by
  obtain ⟨values,compiled,len⟩ := directExpressions_noCode args shape ctxt (ctxt.vmax+1) live
  have callShape : compileHOLExact ctxt live (.call none name args) =
      loopNestedSeqHOL ((genTemps (ctxt.vmax+1) args.length).zipWith HolLoopProg.assign values ++
        [.call none (some (findLabExact ctxt name)) (genTemps (ctxt.vmax+1) args.length) none]) := by
    simp [compileHOLExact,compiled,len]
  dsimp only
  rw [compiled,callShape]
  have bound := assignmentPrefix_steps (genTemps (ctxt.vmax+1) args.length) values
    (.call none (some (findLabExact ctxt name)) (genTemps (ctxt.vmax+1) args.length) none) s
  simpa [List.length_zip,genTemps,len] using bound

/-- The direct-argument returning-call wrapper has linear cost in its arity. -/
theorem compile_returningCall_direct_steps {width : Nat} [NeZero width] {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : Flapjack.Basis.Pure.MlString.MlString)
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, DirectExpression e)
    (names returnNames : List Nat) (mapped : names.mapM ctxt.vars.lookup = some returnNames)
    (s : LoopSemStateFiniteExact width F) :
    let values := (compileExpsHOLExact ctxt (ctxt.vmax+1) live args).2.1
    let regs := genTemps (ctxt.vmax+1) args.length
      let call : HolLoopProg width := .call (some (returnNames,live)) (some (findLabExact ctxt name)) regs
        (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))
      LoopSteps.steps (compileHOLExact ctxt live (.call (some (names,none)) name args)) s ≤
        2 * args.length + 2 +
          match evaluate (loopNestedSeqHOL (regs.zipWith HolLoopProg.assign values)) s with
          | (none,t) => LoopSteps.steps call t
          | _ => 0 := by
  obtain ⟨values,compiled,len⟩ := directExpressions_noCode args shape ctxt (ctxt.vmax+1) live
  have callShape : compileHOLExact ctxt live (.call (some (names,none)) name args) =
      loopNestedSeqHOL ((genTemps (ctxt.vmax+1) args.length).zipWith HolLoopProg.assign values ++
        [.call (some (returnNames,live)) (some (findLabExact ctxt name)) (genTemps (ctxt.vmax+1) args.length)
          (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))]) := by
    simp [compileHOLExact,compiled,len,mapped]
  dsimp only
  rw [compiled,callShape]
  have bound := assignmentPrefix_steps (genTemps (ctxt.vmax+1) args.length) values
    (.call (some (returnNames,live)) (some (findLabExact ctxt name)) (genTemps (ctxt.vmax+1) args.length)
      (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))) s
  simpa [List.length_zip,genTemps,len] using bound

/-- The exact Crep compiler emits one Loop call, in its nested-sequence
wrapper, for a zero-argument tail call. -/
theorem compile_tailCall_nil {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : MlString) :
    compileHOLExact ctxt live (.call none name [] : CrepProgHOL width) =
      .seq (.call none (some (findLabExact ctxt name)) [] none) .skip := by
  obtain ⟨values,len,compiled⟩ := compile_tailCall_direct (width := width) ctxt live name [] (by simp)
  have empty : values = [] := by simpa using len
  subst values
  simpa [genTemps,loopNestedSeqHOL] using compiled

/-- The compiler code relation determines the actual callee and its argument
registers for every function arity. -/
theorem call_lookup {width : Nat} [NeZero width] {F : Type}
    (ctxt : CrepToLoopContextExact) (source : CrepSemHOLState width F)
    (target : LoopSemStateFiniteExact width F) (name : MlString) (params : List Nat)
    (body : CrepProgHOL width) (values : List (WordLocW width))
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (found : source.code.lookup name = some (params,body)) (arity : values.length = params.length) :
    findCode (some (findLabExact ctxt name)) values target.code =
      some (sptFromAList ((List.range params.length).zip values),
        ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
          (listToNumSetHOLExact (List.range params.length)) body) := by
  obtain ⟨loc,len,hlab,hlen,hcode⟩ := codeRel.2 name params body found
  subst len
  have label : findLabExact ctxt name = loc := by simp [findLabExact,hlab]
  rw [label]
  simp [findCode,hcode,arity]

/-- The code relation identifies the exact optimized zero-argument callee and
the numeric call target. -/
theorem tailCall_nil_lookup {width : Nat} [NeZero width] {F : Type}
    (ctxt : CrepToLoopContextExact) (source : CrepSemHOLState width F)
    (target : LoopSemStateFiniteExact width F) (name : MlString) (body : CrepProgHOL width)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (found : source.code.lookup name = some ([],body)) :
    findCode (some (findLabExact ctxt name)) [] target.code =
      some (.ln,ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body) := by
  simpa [sptFromAList,listToNumSetHOLExact] using call_lookup ctxt source target name [] body [] codeRel found rfl

/-- A direct call with evaluated arguments counts the actual compiled callee. -/
theorem call_tail_steps {width : Nat} [NeZero width] {F : Type}
    (ctxt : CrepToLoopContextExact) (source : CrepSemHOLState width F)
    (target : LoopSemStateFiniteExact width F) (name : MlString) (params args : List Nat)
    (body : CrepProgHOL width) (values : List (WordLocW width))
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (found : source.code.lookup name = some (params,body)) (arity : values.length = params.length)
    (get : getVars args target = some values) (clock : target.clock ≠ 0) :
    LoopSteps.steps (.call none (some (findLabExact ctxt name)) args none) target =
      1 + LoopSteps.steps
        (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
          (listToNumSetHOLExact (List.range params.length)) body)
        {decClock target with locals := sptFromAList ((List.range params.length).zip values)} := by
  exact LoopSteps.steps_call_tail _ _ _ _ _ _ get (call_lookup ctxt source target name params body values codeRel found arity) clock

/-- A successful returning call counts its compiled callee and normal continuation. -/
theorem call_returning_steps {width : Nat} [NeZero width] {F : Type}
    (ctxt : CrepToLoopContextExact) (source : CrepSemHOLState width F)
    (target cut post : LoopSemStateFiniteExact width F) (name : MlString) (params args names : List Nat)
    (live liveOut : NumSet) (exception : Nat) (handler normal : HolLoopProg width)
    (body : CrepProgHOL width) (values returned : List (WordLocW width))
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (found : source.code.lookup name = some (params,body)) (arity : values.length = params.length)
    (get : getVars args target = some values) (distinct : names.Nodup)
    (cutRun : cutRes live (none,target) = (none,cut))
    (bodyRun : evaluate
      (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
        (listToNumSetHOLExact (List.range params.length)) body)
      {cut with locals := sptFromAList ((List.range params.length).zip values)} = (some (.result returned),post))
    (returnedArity : returned.length = names.length) :
    LoopSteps.steps (.call (some (names,live)) (some (findLabExact ctxt name)) args
      (some (exception,handler,normal,liveOut))) target =
      1 + LoopSteps.steps
        (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
          (listToNumSetHOLExact (List.range params.length)) body)
        {cut with locals := sptFromAList ((List.range params.length).zip values)} +
      LoopSteps.steps normal (setVars names returned {post with locals := cut.locals}) := by
  have h := LoopSteps.steps_call_returning (some (findLabExact ctxt name)) args names live
    (some (exception,handler,normal,liveOut)) target cut post values
    (sptFromAList ((List.range params.length).zip values))
    (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
      (listToNumSetHOLExact (List.range params.length)) body) (some (.result returned))
    get (call_lookup ctxt source target name params body values codeRel found arity) distinct cutRun bodyRun
  simpa [returnedArity] using h

/-- A successful compiled zero-argument tail call visits the actual optimized
callee, with at most two extra Loop wrapper nodes. -/
theorem compile_tailCall_nil_steps {width : Nat} [NeZero width] {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (source : CrepSemHOLState width F)
    (target : LoopSemStateFiniteExact width F) (name : MlString) (body : CrepProgHOL width)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (found : source.code.lookup name = some ([],body)) (clock : target.clock ≠ 0) :
    LoopSteps.steps (compileHOLExact ctxt live (.call none name [])) target ≤
      3 + LoopSteps.steps (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body)
        {decClock target with locals := .ln} := by
  have bound := compile_tailCall_direct_steps (width := width) ctxt live name [] (by simp) target
  have call := call_tail_steps ctxt source target name [] [] body [] codeRel found rfl (by rfl) clock
  simp only [List.length_nil,List.range_zero,List.zip_nil_left,sptFromAList,listToNumSetHOLExact] at call
  simp only [compileExpsHOLExact,genTemps,List.length_nil,List.range_zero,List.map_nil,List.zipWith_nil_left,loopNestedSeqHOL,evaluate] at bound
  rw [call] at bound
  simp only [decClock] at bound ⊢
  omega

/-- A zero-argument returning call without an exception handler compiles to a
Loop call with the compiler-generated normal and exceptional continuations. -/
theorem compile_returningCall_nil {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : MlString)
    (names returnNames : List Nat) (mapped : names.mapM ctxt.vars.lookup = some returnNames) :
    compileHOLExact ctxt live (.call (some (names,none)) name [] : CrepProgHOL width) =
      .seq (.call (some (returnNames,live)) (some (findLabExact ctxt name)) []
        (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))) .skip := by
  obtain ⟨values,len,compiled⟩ := compile_returningCall_direct (width := width) ctxt live name [] (by simp) names returnNames mapped
  have empty : values = [] := by simpa using len
  subst values
  simpa [genTemps,loopNestedSeqHOL] using compiled

/-- A successful compiled returning call counts its reached callee and at most
four call and continuation nodes. The code relation selects the actual callee. -/
theorem compile_returningCall_nil_steps {width : Nat} [NeZero width] {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (source : CrepSemHOLState width F)
    (target cut post : LoopSemStateFiniteExact width F) (name : MlString) (body : CrepProgHOL width)
    (names returnNames : List Nat) (values : List (WordLocW width))
    (mapped : names.mapM ctxt.vars.lookup = some returnNames) (distinct : returnNames.Nodup)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (found : source.code.lookup name = some ([],body))
    (cutRun : cutRes live (none,target) = (none,cut))
    (run : evaluate (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body)
      {cut with locals := .ln} = (some (.result values),post))
    (arity : values.length = returnNames.length) :
    LoopSteps.steps (compileHOLExact ctxt live (.call (some (names,none)) name [])) target ≤
      4 + LoopSteps.steps (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body)
        {cut with locals := .ln} := by
  have bound := compile_returningCall_direct_steps (width := width) ctxt live name [] (by simp) names returnNames mapped target
  have call := call_returning_steps ctxt source target cut post name [] [] returnNames live live
    (ctxt.vmax+1) (.raise (ctxt.vmax+1)) .skip body [] values codeRel found rfl (by rfl)
    distinct cutRun (by simpa [sptFromAList,listToNumSetHOLExact] using run) arity
  simp only [List.length_nil,List.range_zero,List.zip_nil_left,sptFromAList,listToNumSetHOLExact] at call
  simp only [compileExpsHOLExact,genTemps,List.length_nil,List.range_zero,List.map_nil,List.zipWith_nil_left,loopNestedSeqHOL,evaluate] at bound
  rw [call] at bound
  have skip := LoopSteps.steps_leaf (.skip : HolLoopProg width) (setVars returnNames values {post with locals := cut.locals}) rfl
  omega

/-- A completed supported callee execution gives a source-visit bound for its
actual optimized Loop tail call, with a constant call-wrapper overhead. -/
theorem compile_tailCall_nil_optimised_bound {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (source : CrepSemHOLState 64 F)
    (target final : LoopSemStateFiniteExact 64 F) (name : MlString) (body : CrepProgHOL 64)
    (result : Option (LoopResultExact 64)) (limit : Nat)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (found : source.code.lookup name = some ([],body)) (clock : target.clock ≠ 0)
    (shape : SteppedFlapjack.LoopToWordSteps.LoopSequenceSource
      (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body))
    (run : evaluate (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body)
      {decClock target with locals := .ln} = (result,final))
    (complete : SteppedFlapjack.LoopToWordSteps.CompleteLoopResult result)
    (sourceBound : LoopSteps.steps (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body)
      {decClock target with locals := .ln} ≤ limit) :
    LoopSteps.steps (compileHOLExact ctxt live (.call none name [])) target ≤
      3 + sizeOf (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body) * (2 * limit + 1) := by
  have callBound := compile_tailCall_nil_steps ctxt live source target name body codeRel found clock
  obtain ⟨_,_,optBound⟩ := LoopLiveSteps.optimise_complete_source_steps shape
    {decClock target with locals := .ln} final result run complete
  have scaled := Nat.mul_le_mul_left
    (sizeOf (optimiseHOL (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body)))
    (show 2 * LoopSteps.steps (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln body)
      {decClock target with locals := .ln} + 1 ≤ 2 * limit + 1 by omega)
  unfold ocompileHOLExact at callBound ⊢
  omega

/-- A supported completed Crep callee bounds the actual optimized Loop tail
call, after the proved compiler clock extension, by its Crep visits. -/
theorem compile_tailCall_nil_crep_bound {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (callerSource : CrepSemHOLState 64 F)
    (target : LoopSemStateFiniteExact 64 F) (name : MlString)
    (init : CrepProgHOL 64) (initShape : BranchProgram init)
    (condition : CrepExpHOL 64) (conditionShape : BranchCondition condition)
    (body tail : CrepProgHOL 64) (bodyShape : BranchProgram body) (tailShape : BranchProgram tail)
    (source post : CrepSemHOLState 64 F) (result : Option (CrepResultHOLExact 64))
    (codeRel : crepToLoopCodeRelExact ctxt callerSource.code target.code)
    (found : callerSource.code.lookup name = some ([],.seq init (.seq (.while condition body) tail)))
    (clock : target.clock ≠ 0)
    (run : evalCrepSemHOLProgExact source (.seq init (.seq (.while condition body) tail)) = (result,post))
    (complete : CompleteCrepResult result)
    (stateRel : crepToLoopStateRelExact source {decClock target with locals := .ln})
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (calleeCodeRel : crepToLoopCodeRelExact (ctxtFcExact ctxt.target ctxt.funcs [] []) source.code target.code)
    (localsRel : crepToLoopLocalsRelExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln source.locals .ln) :
    let c := ctxtFcExact ctxt.target ctxt.funcs [] []
    let p := .seq init (.seq (.while condition body) tail)
    let factor := 1 + sizeOf (compileHOLExact c .ln init) +
      (1 + (1 + sizeOf (compileHOLExact c .ln (.while condition body))) *
        (sizeOf (loopNestedSeqHOL (compileExpHOLExact c (c.vmax+1) .ln condition).1) +
          sizeOf (compileHOLExact c .ln body)+3) + sizeOf (compileHOLExact c .ln tail))
    ∃ extra final,
      evaluate (compileHOLExact ctxt live (.call none name [])) {target with clock := target.clock+extra} =
        (resultToLoop result,final) ∧
      crepToLoopStateRelExact post final ∧
      LoopSteps.steps (compileHOLExact ctxt live (.call none name [])) {target with clock := target.clock+extra} ≤
        3 + sizeOf (ocompileHOLExact c .ln p) * (2 * (factor * (CrepSteps.steps p source+1)) + 1) := by
  let c := ctxtFcExact ctxt.target ctxt.funcs [] []
  let p : CrepProgHOL 64 := .seq init (.seq (.while condition body) tail)
  let entry : LoopSemStateFiniteExact 64 F := {decClock target with locals := .ln}
  obtain ⟨extra,final,loopRun,postRel,_,_,_,_,loopBound⟩ :=
    branchConditionWhileBranch_programBound init initShape condition conditionShape body tail bodyShape tailShape c .ln
      source post result entry run (completeCrep_nonerror complete) stateRel memRel globalsRel calleeCodeRel localsRel
  have shift : ({decClock {target with clock := target.clock+extra} with locals := .ln} : LoopSemStateFiniteExact 64 F) =
      {entry with clock := entry.clock+extra} := by
    simp only [entry,decClock]
    congr 1
    omega
  have extendedRun : evaluate (compileHOLExact c .ln p) {decClock {target with clock := target.clock+extra} with locals := .ln} =
      (resultToLoop result,final) := by rw [shift]; exact loopRun
  have extendedBound : LoopSteps.steps (compileHOLExact c .ln p) {decClock {target with clock := target.clock+extra} with locals := .ln} ≤
      (1 + sizeOf (compileHOLExact c .ln init) +
        (1 + (1 + sizeOf (compileHOLExact c .ln (.while condition body))) *
          (sizeOf (loopNestedSeqHOL (compileExpHOLExact c (c.vmax+1) .ln condition).1) +
            sizeOf (compileHOLExact c .ln body)+3) + sizeOf (compileHOLExact c .ln tail))) * (CrepSteps.steps p source+1) := by
    rw [shift]; exact loopBound
  have codeRel' : crepToLoopCodeRelExact ctxt callerSource.code {target with clock := target.clock+extra}.code := codeRel
  have optimizedRun := (LoopLiveSteps.optimise_complete_source_steps
    (branchConditionWhileBranch_wordSimpShape init initShape condition conditionShape body tail bodyShape tailShape c .ln)
    {decClock {target with clock := target.clock+extra} with locals := .ln} final (resultToLoop result)
    extendedRun (completeCrep_loop complete)).1
  have callLookup := tailCall_nil_lookup ctxt callerSource {target with clock := target.clock+extra} name p codeRel' found
  have compiledRun : evaluate (compileHOLExact ctxt live (.call none name [])) {target with clock := target.clock+extra} =
      (resultToLoop result,final) := by
    rw [compile_tailCall_nil,evaluate_seq]
    have callRun : evaluate (.call none (some (findLabExact ctxt name)) [] none) {target with clock := target.clock+extra} =
        (resultToLoop result,final) := by
      rw [evaluate]
      simp only [show getVars [] {target with clock := target.clock+extra} = some [] from rfl,
        callLookup,Option.isSome_none,Bool.false_eq_true,if_false]
      have nz : target.clock + extra ≠ 0 := by omega
      simp only [nz, dite_false]
      simp only [ocompileHOLExact]
      rw [optimizedRun]
      cases complete <;> rfl
    rw [callRun]
    cases complete <;> rfl
  refine ⟨extra,final,compiledRun,postRel,?_⟩
  exact compile_tailCall_nil_optimised_bound ctxt live callerSource {target with clock := target.clock+extra} final name p
    (resultToLoop result) _ codeRel' found (by simp; omega)
    (branchConditionWhileBranch_wordSimpShape init initShape condition conditionShape body tail bodyShape tailShape c .ln)
    extendedRun (completeCrep_loop complete) extendedBound

/-- A call with evaluated arguments preserves the compiler relations at the
parameterized callee entry. -/
theorem returnRegisters_of_locals {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (live : NumSet)
    (source : HolFiniteMapExact Nat (HolWordLab width)) (target : Spt (WordLocW width))
    (names : List Nat) (old : List (HolWordLab width))
    (existing : names.mapM source.lookup = some old) (distinct : names.Nodup)
    (related : crepToLoopLocalsRelExact ctxt live source target) :
    ∃ regs, names.mapM ctxt.vars.lookup = some regs ∧ regs.Nodup := by
  have mapped : ∀ ns : List Nat, ∀ vs : List (HolWordLab width),
      ns.mapM source.lookup = some vs → ∃ regs, ns.mapM ctxt.vars.lookup = some regs := by
    intro ns
    induction ns with
    | nil => intro vs h; exact ⟨[],rfl⟩
    | cons n ns ih =>
      intro vs h
      rw [List.mapM_cons] at h
      cases hv : source.lookup n with
      | none => simp [hv] at h
      | some value =>
        cases ht : ns.mapM source.lookup with
        | none => simp [hv,ht] at h
        | some tail =>
          obtain ⟨reg,hreg,_,_⟩ := related.2.2.2 n value hv
          obtain ⟨regs,hregs⟩ := ih tail ht
          refine ⟨reg::regs,?_⟩
          simp [List.mapM_cons,hreg,hregs]
  obtain ⟨regs,hregs⟩ := mapped names old existing
  have h := allDistinctCtxtLookupAllDistinctExact ctxt names (ctxt.vmax+1) distinct related.1
  simp only [rtVars,FLOOKUP] at h
  rw [hregs] at h
  exact ⟨regs,hregs,h⟩

theorem call_entry_relations {width : Nat} [NeZero width] {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (source : CrepSemHOLState width F)
    (target : LoopSemStateFiniteExact width F) (name : MlString) (params : List Nat) (body : CrepProgHOL width)
    (expressions : List (CrepExpHOL width)) (values : List (HolWordLab width))
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (found : source.code.lookup name = some (params,body))
    (distinct : params.Nodup) (arity : values.length = params.length)
    (evaluated : expressions.map (evalCrepSemHOLExp source) = values.map some) :
    let sourceEntry := decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)}
    let regs := List.range params.length
    let targetEntry : LoopSemStateFiniteExact width F := {decClock target with locals := sptFromAList (regs.zip (values.map wlabWlocExact))}
    let calleeCtxt := ctxtFcExact ctxt.target ctxt.funcs params regs
    crepToLoopStateRelExact sourceEntry targetEntry ∧
    crepToLoopMemRelHOLExact sourceEntry.memory targetEntry.memory sourceEntry.memaddrs ∧
    crepToLoopGlobalsRelHOLExact sourceEntry.globals targetEntry.globals ∧
    crepToLoopCodeRelExact calleeCtxt sourceEntry.code targetEntry.code ∧
    crepToLoopLocalsRelExact calleeCtxt (listToNumSetHOLExact regs) sourceEntry.locals targetEntry.locals := by
  obtain ⟨loc,len,hlab,hlen,_⟩ := codeRel.2 name params body found
  subst len
  have preserved := crepToLoopCallPreserveStateCodeLocalsRelExact params (List.range params.length) values source target ctxt live name expressions body loc
    distinct List.nodup_range (by simp) (by simpa using arity) stateRel memRel globalsRel codeRel localsRel found (by simpa using hlab) evaluated
  refine ⟨?_,?_,?_,?_,?_⟩
  · simpa [decClockCrepSemHOL,decClock] using preserved.1
  · simpa [decClockCrepSemHOL,decClock] using memRel
  · simpa [decClockCrepSemHOL,decClock] using globalsRel
  · simpa [decClockCrepSemHOL,decClock] using preserved.2.1
  · simpa [decClockCrepSemHOL,decClock] using preserved.2.2

/-- The concrete argument budget reaches the selected callee with its entry relations. -/
theorem scalarCall_calleeEntry_explicit {width : Nat} [NeZero width] {σ : Type}
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, CompiledScalar e)
    (source : CrepSemHOLState width σ) (values : List (HolWordLab width))
    (target : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (live : NumSet)
    (name : MlString) (params : List Nat) (body : CrepProgHOL width) (budget : Nat)
    (evaluated : args.mapM (evalCrepSemHOLExp source) = some values)
    (found : source.code.lookup name = some (params,body))
    (distinct : params.Nodup) (arity : params.length = values.length)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (budgetBound : LoopSteps.structuralWeight (loopNestedSeqHOL
      (compileExpsHOLExact ctxt (ctxt.vmax+1) live args).1) ≤ budget) :
    let comp := compileExpsHOLExact ctxt (ctxt.vmax+1) live args
    let regs := genTemps comp.2.2.1 comp.2.1.length
    let vals := values.map wlabWlocExact
    let formals := List.range params.length
    let sourceEntry := decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)}
    let calleeCtxt := ctxtFcExact ctxt.target ctxt.funcs params formals
    ∃ post,
      let middle : LoopSemStateFiniteExact width σ := {post with locals := sptAlistInsert regs vals post.locals}
      let entry : LoopSemStateFiniteExact width σ :=
        {decClock {post with clock := source.clock} with locals := sptFromAList (formals.zip vals)}
      evaluate (loopNestedSeqHOL comp.1) {target with clock := target.clock+budget} = (none,post) ∧
      evaluate (loopNestedSeqHOL (regs.zipWith HolLoopProg.assign comp.2.1)) post = (none,middle) ∧
      getVars regs middle = some vals ∧ sptSubsetLive live middle.locals ∧
      source.clock ≤ post.clock ∧ post.code = target.code ∧
      findCode (some (findLabExact ctxt name)) vals middle.code =
        some (sptFromAList (formals.zip vals), ocompileHOLExact calleeCtxt (listToNumSetHOLExact formals) body) ∧
      (source.clock ≠ 0 →
        {decClock middle with locals := sptFromAList (formals.zip vals)} =
          {entry with clock := entry.clock + (post.clock-source.clock)}) ∧
      crepToLoopStateRelExact sourceEntry entry ∧
      crepToLoopMemRelHOLExact sourceEntry.memory entry.memory sourceEntry.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceEntry.globals entry.globals ∧
      crepToLoopCodeRelExact calleeCtxt sourceEntry.code entry.code ∧
      crepToLoopLocalsRelExact calleeCtxt (listToNumSetHOLExact formals) sourceEntry.locals entry.locals := by
  obtain ⟨post,run,assign,get,subset,clock,st,mem,gl,code,codeSame,locals⟩ :=
    scalarCall_argumentPrefix_explicit args shape source values target ctxt live budget evaluated stateRel memRel globalsRel codeRel localsRel budgetBound
  let comp := compileExpsHOLExact ctxt (ctxt.vmax+1) live args
  let regs := genTemps comp.2.2.1 comp.2.1.length
  let vals := values.map wlabWlocExact
  let formals := List.range params.length
  let normalized : LoopSemStateFiniteExact width σ := {post with clock := source.clock}
  have code' : crepToLoopCodeRelExact ctxt source.code normalized.code := code
  have locals' : crepToLoopLocalsRelExact ctxt comp.2.2.2 source.locals normalized.locals := locals
  obtain ⟨loc,len,lab,hlen,_⟩ := codeRel.2 name params body found
  subst len
  have preserve := crepToLoopCallPreserveStateCodeLocalsRelExact params formals values source normalized ctxt comp.2.2.2
    name args body loc distinct (by simpa [formals] using (List.nodup_range : (List.range params.length).Nodup)) (by simp [formals]) (by simp [formals,arity]) st mem gl code' locals' found
    (by simpa [formals] using lab) ((optMmapEqSome args _ _).mp evaluated)
  have lookup := call_lookup ctxt source post name params body vals code found (by simp [vals,arity])
  refine ⟨post,run,assign,get,subset,clock,codeSame,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [comp,regs,vals,formals] using lookup
  · intro nonzero
    simp only [decClock]
    congr 1
    omega
  · simpa [normalized,formals,vals,decClockCrepSemHOL,decClock] using preserve.1
  · simpa [normalized,formals,vals,decClockCrepSemHOL,decClock] using mem
  · simpa [normalized,formals,vals,decClockCrepSemHOL,decClock] using gl
  · simpa [normalized,formals,vals,decClockCrepSemHOL,decClock] using preserve.2.1
  · simpa [normalized,formals,vals,decClockCrepSemHOL,decClock] using preserve.2.2

/-- The ordinary caller state/code/locals relations derive all callee-entry
relations for an empty-argument call, including the actual compiler context. -/
theorem tailCall_nil_entry_relations {width : Nat} [NeZero width] {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (source : CrepSemHOLState width F)
    (target : LoopSemStateFiniteExact width F) (name : MlString) (body : CrepProgHOL width)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (found : source.code.lookup name = some ([],body)) :
    let sourceEntry := decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList []}
    let targetEntry : LoopSemStateFiniteExact width F := {decClock target with locals := .ln}
    let calleeCtxt := ctxtFcExact ctxt.target ctxt.funcs [] []
    crepToLoopStateRelExact sourceEntry targetEntry ∧
    crepToLoopMemRelHOLExact sourceEntry.memory targetEntry.memory sourceEntry.memaddrs ∧
    crepToLoopGlobalsRelHOLExact sourceEntry.globals targetEntry.globals ∧
    crepToLoopCodeRelExact calleeCtxt sourceEntry.code targetEntry.code ∧
    crepToLoopLocalsRelExact calleeCtxt .ln sourceEntry.locals targetEntry.locals := by
  simpa [sptFromAList,listToNumSetHOLExact] using
    call_entry_relations ctxt live source target name [] body [] [] stateRel memRel globalsRel codeRel localsRel
      found (by simp) rfl (by rfl)

/-- At zero clock every Loop call visits only the call node. -/
theorem loopCall_zero_steps {width : Nat} [NeZero width] {σ : Type}
    (ret : Option (List Nat × NumSet)) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × HolLoopProg width × HolLoopProg width × NumSet))
    (s : LoopSemStateFiniteExact width σ) (clock : s.clock = 0) :
    LoopSteps.steps (.call ret dest args handler) s = 1 := by
  rw [LoopSteps.steps.eq_def]
  cases hg : getVars args s with
  | none => simp [hg]
  | some vals =>
    cases hf : findCode dest vals s.code with
    | none => simp [hg,hf]
    | some pair =>
      obtain ⟨env,body⟩ := pair
      cases ret with
      | none => simp [hg,hf,clock]
      | some info =>
        obtain ⟨names,live⟩ := info
        by_cases nd : names.Nodup
        · cases hc : cutState live s with
          | none => simp [hg,hf,nd,cutRes,hc]
          | some cut =>
            have cutClock := cutState_clock hc
            simp [hg,hf,nd,cutRes,hc,cutClock,clock]
        · simp [hg,hf,nd]

/-- A direct tail call inherits its reached callee visit bound. -/
theorem compiledTailCall_bound_from_body {width : Nat} [NeZero width] {σ : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : MlString)
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, DirectExpression e)
    (source : CrepSemHOLState width σ) (target : LoopSemStateFiniteExact width σ)
    (values : List (HolWordLab width)) (params : List Nat) (body : CrepProgHOL width) (B : Nat)
    (hargs : args.mapM (evalCrepSemHOLExp source) = some values)
    (found : source.code.lookup name = some (params,body))
    (arity : params.length = values.length) (distinct : params.Nodup)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (bodyBound : source.clock ≠ 0 → LoopSteps.steps
      (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
        (listToNumSetHOLExact (List.range params.length)) body)
      {decClock target with locals := sptFromAList ((List.range params.length).zip (values.map wlabWlocExact))} ≤
      B * CrepSteps.steps body (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)})) :
    LoopSteps.steps (compileHOLExact ctxt live (.call none name args)) target ≤
      max (2 * args.length + 3) B * CrepSteps.steps (.call none name args) source := by
  by_cases clock : source.clock = 0
  · obtain ⟨les,compiled,prefixRun,get,_⟩ := directCall_argumentPrefix args shape source values target ctxt live hargs stateRel memRel globalsRel codeRel localsRel
    let regs := genTemps (ctxt.vmax+1) args.length
    let middle : LoopSemStateFiniteExact width σ := {target with locals := sptAlistInsert regs (values.map wlabWlocExact) target.locals}
    have zero : middle.clock = 0 := by
      change target.clock = 0
      exact stateRel.2.2.1.symm.trans clock
    have call := loopCall_zero_steps none (some (findLabExact ctxt name)) regs none middle zero
    have wrapper := compile_tailCall_direct_steps ctxt live name args shape target
    dsimp only at wrapper
    rw [compiled] at wrapper
    change evaluate (loopNestedSeqHOL (regs.zipWith HolLoopProg.assign les)) target = (none,middle) at prefixRun
    rw [prefixRun] at wrapper
    simp only at wrapper
    rw [call] at wrapper
    have positive := CrepSteps.steps_pos (.call none name args) source
    have factor := Nat.le_max_left (2 * args.length + 3) B
    nlinarith
  ·
    obtain ⟨les,compiled,prefixRun,get,_⟩ := directCall_argumentPrefix args shape source values target ctxt live hargs stateRel memRel globalsRel codeRel localsRel
    let regs := genTemps (ctxt.vmax+1) args.length
    let vals := values.map wlabWlocExact
    let middle : LoopSemStateFiniteExact width σ := {target with locals := sptAlistInsert regs vals target.locals}
    have targetClock : middle.clock ≠ 0 := by
      change target.clock ≠ 0
      have rel := stateRel.2.2.1
      rw [← rel]
      exact clock
    have targetCode : crepToLoopCodeRelExact ctxt source.code middle.code := by simpa [middle] using codeRel
    have get' : getVars regs middle = some vals := get
    have callCount := call_tail_steps ctxt source middle name params regs body vals targetCode found (by simp [vals,arity]) get' targetClock
    have sourceCount := CrepSteps.steps_call_tail name args source values params body hargs found arity distinct clock
    have wrapper := compile_tailCall_direct_steps ctxt live name args shape target
    dsimp only at wrapper
    rw [compiled] at wrapper
    change evaluate (loopNestedSeqHOL (regs.zipWith HolLoopProg.assign les)) target = (none,middle) at prefixRun
    rw [prefixRun] at wrapper
    simp only at wrapper
    rw [callCount] at wrapper
    have bodyBound' := bodyBound clock
    simp only [middle,decClock] at wrapper bodyBound'
    rw [sourceCount]
    have factorA : 2 * args.length + 3 ≤ max (2 * args.length + 3) B := Nat.le_max_left _ _
    have factorB : B ≤ max (2 * args.length + 3) B := Nat.le_max_right _ _
    nlinarith

/-- Generated raise/skip continuations add at most one visit to a returning call. -/
theorem returningCall_generated_steps {width : Nat} [NeZero width] {σ : Type}
    (dest : Option Nat) (args names : List Nat) (live : NumSet) (exception : Nat)
    (s cut post : LoopSemStateFiniteExact width σ) (values : List (WordLocW width))
    (env : Spt (WordLocW width)) (body : HolLoopProg width) (out : Option (LoopResultExact width))
    (get : getVars args s = some values) (found : findCode dest values s.code = some (env,body))
    (distinct : names.Nodup) (cutRun : cutRes live (none,s) = (none,cut))
    (bodyRun : evaluate body {cut with locals := env} = (out,post)) :
    LoopSteps.steps (.call (some (names,live)) dest args (some (exception,.raise exception,.skip,live))) s ≤
      2 + LoopSteps.steps body {cut with locals := env} := by
  have count := LoopSteps.steps_call_returning dest args names live (some (exception,.raise exception,.skip,live))
    s cut post values env body out get found distinct cutRun bodyRun
  rw [count]
  cases out with
  | none => simp
  | some r =>
    cases r <;> try simp
    case result returned => split <;> simp [LoopSteps.steps_leaf]
    case exception value => simp [LoopSteps.steps_leaf]

/-- A direct returning call inherits the reached callee visit bound. -/
theorem compiledReturningCall_bound_from_body {width : Nat} [NeZero width] {σ : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : MlString)
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, DirectExpression e)
    (names returnNames : List Nat) (mapped : names.mapM ctxt.vars.lookup = some returnNames)
    (source : CrepSemHOLState width σ) (target : LoopSemStateFiniteExact width σ)
    (values : List (HolWordLab width)) (params : List Nat) (body : CrepProgHOL width) (B : Nat)
    (hargs : args.mapM (evalCrepSemHOLExp source) = some values)
    (found : source.code.lookup name = some (params,body))
    (arity : params.length = values.length) (distinct : params.Nodup) (namesDistinct : names.Nodup)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (bodyBound : source.clock ≠ 0 → LoopSteps.steps
      (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
        (listToNumSetHOLExact (List.range params.length)) body)
      {decClock target with locals := sptFromAList ((List.range params.length).zip (values.map wlabWlocExact))} ≤
      B * CrepSteps.steps body (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)})) :
    LoopSteps.steps (compileHOLExact ctxt live (.call (some (names,none)) name args)) target ≤
      max (2 * args.length + 4) B * CrepSteps.steps (.call (some (names,none)) name args) source := by
  by_cases clock : source.clock = 0
  · obtain ⟨les,compiled,prefixRun,get,_⟩ := directCall_argumentPrefix args shape source values target ctxt live hargs stateRel memRel globalsRel codeRel localsRel
    let regs := genTemps (ctxt.vmax+1) args.length
    let middle : LoopSemStateFiniteExact width σ := {target with locals := sptAlistInsert regs (values.map wlabWlocExact) target.locals}
    have zero : middle.clock = 0 := by
      change target.clock = 0
      exact stateRel.2.2.1.symm.trans clock
    have call := loopCall_zero_steps (some (returnNames,live)) (some (findLabExact ctxt name)) regs
      (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live)) middle zero
    have wrapper := compile_returningCall_direct_steps ctxt live name args shape names returnNames mapped target
    dsimp only at wrapper
    rw [compiled] at wrapper
    change evaluate (loopNestedSeqHOL (regs.zipWith HolLoopProg.assign les)) target = (none,middle) at prefixRun
    rw [prefixRun] at wrapper
    simp only at wrapper
    rw [call] at wrapper
    have positive := CrepSteps.steps_pos (.call (some (names,none)) name args) source
    have factor := Nat.le_max_left (2 * args.length + 4) B
    nlinarith
  ·
    obtain ⟨les,compiled,prefixRun,get,subset⟩ := directCall_argumentPrefix args shape source values target ctxt live hargs stateRel memRel globalsRel codeRel localsRel
    let regs := genTemps (ctxt.vmax+1) args.length
    let vals := values.map wlabWlocExact
    let middle : LoopSemStateFiniteExact width σ := {target with locals := sptAlistInsert regs vals target.locals}
    let cut : LoopSemStateFiniteExact width σ := decClock {middle with locals := sptInter middle.locals live}
    have targetClock : middle.clock ≠ 0 := by
      change target.clock ≠ 0
      have rel := stateRel.2.2.1
      rw [← rel]
      exact clock
    have hcut : cutRes live (none,middle) = (none,cut) := by
      rw [cutRes]
      simp only
      rw [cutState_of_subset live middle subset]
      simp [targetClock,cut]
    have targetCode : crepToLoopCodeRelExact ctxt source.code middle.code := by simpa [middle] using codeRel
    have hfind := call_lookup ctxt source middle name params body vals targetCode found (by simp [vals,arity])
    have nd : returnNames.Nodup := by
      have h := allDistinctCtxtLookupAllDistinctExact ctxt names (ctxt.vmax + 1) namesDistinct localsRel.1
      simp only [rtVars,FLOOKUP] at h
      rw [mapped] at h
      exact h
    rcases bodyRun : evaluate
      (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
        (listToNumSetHOLExact (List.range params.length)) body)
      {cut with locals := sptFromAList ((List.range params.length).zip vals)} with ⟨out,post⟩
    have callBound := returningCall_generated_steps (some (findLabExact ctxt name)) regs returnNames live (ctxt.vmax+1)
      middle cut post vals _ _ out get hfind nd hcut bodyRun
    have sourceCount := CrepSteps.steps_call_returning names name args source values params body hargs found arity distinct namesDistinct clock
    have wrapper := compile_returningCall_direct_steps ctxt live name args shape names returnNames mapped target
    dsimp only at wrapper
    rw [compiled] at wrapper
    change evaluate (loopNestedSeqHOL (regs.zipWith HolLoopProg.assign les)) target = (none,middle) at prefixRun
    rw [prefixRun] at wrapper
    simp only at wrapper
    have bodyBound' := bodyBound clock
    simp only [cut,middle,decClock] at callBound bodyBound'
    rw [sourceCount]
    have factorA : 2 * args.length + 4 ≤ max (2 * args.length + 4) B := Nat.le_max_left _ _
    have factorB : B ≤ max (2 * args.length + 4) B := Nat.le_max_right _ _
    nlinarith

/-- One scalar-argument tail-call step inherits the reached callee bound. -/
theorem compiledScalarTail_bound_from_body {width : Nat} [NeZero width] {σ : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : MlString)
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, CompiledScalar e)
    (source : CrepSemHOLState width σ) (target : LoopSemStateFiniteExact width σ)
    (values : List (HolWordLab width)) (params : List Nat) (body : CrepProgHOL width) (B : Nat)
    (hargs : args.mapM (evalCrepSemHOLExp source) = some values)
    (found : source.code.lookup name = some (params,body))
    (arity : params.length = values.length) (distinct : params.Nodup)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (bodyBound : ∀ post : LoopSemStateFiniteExact width σ,
      crepToLoopStateRelExact source post → crepToLoopMemRelHOLExact source.memory post.memory source.memaddrs →
      crepToLoopGlobalsRelHOLExact source.globals post.globals → crepToLoopCodeRelExact ctxt source.code post.code →
      post.code = target.code → source.clock ≠ 0 → LoopSteps.steps
      (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
        (listToNumSetHOLExact (List.range params.length)) body)
      {decClock post with locals := sptFromAList ((List.range params.length).zip (values.map wlabWlocExact))} ≤
      B * CrepSteps.steps body (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)})) :
    let prefixCost := LoopSteps.structuralWeight (loopNestedSeqHOL
      (compileExpsHOLExact ctxt (ctxt.vmax+1) live args).1)
    ∃ extra, extra ≤ prefixCost ∧
      LoopSteps.steps (compileHOLExact ctxt live (.call none name args)) {target with clock := target.clock+extra} ≤
        max (prefixCost + 2*args.length+3) B * CrepSteps.steps (.call none name args) source := by
  obtain ⟨extra,post,prefixRun,assign,get,subset,postState,postMem,postGlobals,postCode,postLocals,extraBound,visits⟩ :=
    compiledScalarCall_reaches_call ctxt live name none args shape source values target hargs stateRel memRel globalsRel codeRel localsRel
  have postCodeEq : post.code = target.code := by
    simpa using SteppedFlapjack.LoopLiveSteps.evaluate_code _ _ post none prefixRun
  dsimp only at visits get extraBound
  let comp := compileExpsHOLExact ctxt (ctxt.vmax+1) live args
  let regs := genTemps comp.2.2.1 comp.2.1.length
  let vals := values.map wlabWlocExact
  let middle : LoopSemStateFiniteExact width σ := {post with locals := sptAlistInsert regs vals post.locals}
  have get' : getVars regs middle = some vals := get
  have targetCode : crepToLoopCodeRelExact ctxt source.code middle.code := by simpa [middle] using postCode
  refine ⟨extra,extraBound,?_⟩
  by_cases clock : source.clock = 0
  · have zero : middle.clock = 0 := by
      change post.clock = 0
      exact postState.2.2.1.symm.trans clock
    have call := loopCall_zero_steps none (some (findLabExact ctxt name)) regs none middle zero
    change LoopSteps.steps (compileHOLExact ctxt live (.call none name args)) _ ≤
      _ + _ + _ + LoopSteps.steps (.call none (some (findLabExact ctxt name)) regs none) middle at visits
    rw [call] at visits
    have positive := CrepSteps.steps_pos (.call none name args) source
    have factor := Nat.le_max_left (LoopSteps.structuralWeight (loopNestedSeqHOL comp.1)+2*args.length+3) B
    nlinarith
  · have nonzero : middle.clock ≠ 0 := by
      change post.clock ≠ 0
      have rel := postState.2.2.1
      rw [← rel]
      exact clock
    have callCount := call_tail_steps ctxt source middle name params regs body vals targetCode found (by simp [vals,arity]) get' nonzero
    have sourceCount := CrepSteps.steps_call_tail name args source values params body hargs found arity distinct clock
    change LoopSteps.steps (compileHOLExact ctxt live (.call none name args)) _ ≤
      _ + _ + _ + LoopSteps.steps (.call none (some (findLabExact ctxt name)) regs none) middle at visits
    rw [callCount] at visits
    have bodyVisits := bodyBound post postState postMem postGlobals postCode postCodeEq clock
    simp only [middle,decClock] at visits bodyVisits
    rw [sourceCount]
    have factorA := Nat.le_max_left (LoopSteps.structuralWeight (loopNestedSeqHOL comp.1)+2*args.length+3) B
    have factorB := Nat.le_max_right (LoopSteps.structuralWeight (loopNestedSeqHOL comp.1)+2*args.length+3) B
    nlinarith
/-- One scalar-argument returning call inherits the reached callee bound. -/
theorem compiledScalarReturning_bound_from_body {width : Nat} [NeZero width] {σ : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (name : MlString)
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, CompiledScalar e)
    (names returnNames : List Nat) (mapped : names.mapM ctxt.vars.lookup = some returnNames)
    (source : CrepSemHOLState width σ) (target : LoopSemStateFiniteExact width σ)
    (values : List (HolWordLab width)) (params : List Nat) (body : CrepProgHOL width) (B : Nat)
    (hargs : args.mapM (evalCrepSemHOLExp source) = some values)
    (found : source.code.lookup name = some (params,body))
    (arity : params.length = values.length) (distinct : params.Nodup) (namesDistinct : names.Nodup)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (bodyBound : ∀ post : LoopSemStateFiniteExact width σ,
      crepToLoopStateRelExact source post → crepToLoopMemRelHOLExact source.memory post.memory source.memaddrs →
      crepToLoopGlobalsRelHOLExact source.globals post.globals → crepToLoopCodeRelExact ctxt source.code post.code →
      post.code = target.code → source.clock ≠ 0 → LoopSteps.steps
      (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
        (listToNumSetHOLExact (List.range params.length)) body)
      {decClock post with locals := sptFromAList ((List.range params.length).zip (values.map wlabWlocExact))} ≤
      B * CrepSteps.steps body (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)})) :
    let prefixCost := LoopSteps.structuralWeight (loopNestedSeqHOL
      (compileExpsHOLExact ctxt (ctxt.vmax+1) live args).1)
    ∃ extra, extra ≤ prefixCost ∧
      LoopSteps.steps (compileHOLExact ctxt live (.call (some (names,none)) name args)) {target with clock := target.clock+extra} ≤
        max (prefixCost + 2*args.length+4) B * CrepSteps.steps (.call (some (names,none)) name args) source := by
  obtain ⟨extra,st,prefixRun,assign,get,subset,postState,postMem,postGlobals,postCode,postLocals,extraBound,visits⟩ :=
    compiledScalarCall_reaches_call ctxt live name (some names) args shape source values target hargs stateRel memRel globalsRel codeRel localsRel
  have postCodeEq : st.code = target.code := by
    simpa using SteppedFlapjack.LoopLiveSteps.evaluate_code _ _ st none prefixRun
  dsimp only at visits get extraBound
  simp only [mapped,Option.getD] at visits
  let comp := compileExpsHOLExact ctxt (ctxt.vmax+1) live args
  let regs := genTemps comp.2.2.1 comp.2.1.length
  let vals := values.map wlabWlocExact
  let middle : LoopSemStateFiniteExact width σ := {st with locals := sptAlistInsert regs vals st.locals}
  have get' : getVars regs middle = some vals := get
  have subset' : sptSubsetLive live middle.locals := subset
  have targetCode : crepToLoopCodeRelExact ctxt source.code middle.code := by simpa [middle] using postCode
  refine ⟨extra,extraBound,?_⟩
  by_cases clock : source.clock = 0
  · have zero : middle.clock = 0 := by
      change st.clock = 0
      exact postState.2.2.1.symm.trans clock
    have call := loopCall_zero_steps (some (returnNames,live)) (some (findLabExact ctxt name)) regs
      (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live)) middle zero
    change LoopSteps.steps (compileHOLExact ctxt live (.call (some (names,none)) name args)) _ ≤
      _ + _ + _ + LoopSteps.steps (.call (some (returnNames,live)) (some (findLabExact ctxt name)) regs
        (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))) middle at visits
    rw [call] at visits
    have positive := CrepSteps.steps_pos (.call (some (names,none)) name args) source
    have factor := Nat.le_max_left (LoopSteps.structuralWeight (loopNestedSeqHOL comp.1)+2*args.length+4) B
    nlinarith
  · let cut : LoopSemStateFiniteExact width σ := decClock {middle with locals := sptInter middle.locals live}
    have nonzero : middle.clock ≠ 0 := by
      change st.clock ≠ 0
      have rel := postState.2.2.1
      rw [← rel]
      exact clock
    have hcut : cutRes live (none,middle) = (none,cut) := by
      rw [cutRes]
      simp only
      rw [cutState_of_subset live middle subset']
      simp [nonzero,cut]
    have hfind := call_lookup ctxt source middle name params body vals targetCode found (by simp [vals,arity])
    have nd : returnNames.Nodup := by
      have h := allDistinctCtxtLookupAllDistinctExact ctxt names (ctxt.vmax + 1) namesDistinct localsRel.1
      simp only [rtVars,FLOOKUP] at h
      rw [mapped] at h
      exact h
    rcases bodyRun : evaluate
      (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
        (listToNumSetHOLExact (List.range params.length)) body)
      {cut with locals := sptFromAList ((List.range params.length).zip vals)} with ⟨out,post⟩
    have callBound := returningCall_generated_steps (some (findLabExact ctxt name)) regs returnNames live (ctxt.vmax+1)
      middle cut post vals _ _ out get' hfind nd hcut bodyRun
    have sourceCount := CrepSteps.steps_call_returning names name args source values params body hargs found arity distinct namesDistinct clock
    change LoopSteps.steps (compileHOLExact ctxt live (.call (some (names,none)) name args)) _ ≤
      _ + _ + _ + LoopSteps.steps (.call (some (returnNames,live)) (some (findLabExact ctxt name)) regs
        (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))) middle at visits
    have bodyVisits := bodyBound st postState postMem postGlobals postCode postCodeEq clock
    simp only [cut,middle,decClock] at callBound bodyVisits
    rw [sourceCount]
    have factorA := Nat.le_max_left (LoopSteps.structuralWeight (loopNestedSeqHOL comp.1)+2*args.length+4) B
    have factorB := Nat.le_max_right (LoopSteps.structuralWeight (loopNestedSeqHOL comp.1)+2*args.length+4) B
    nlinarith


private theorem loopTail_explicit_run {width : Nat} [NeZero width] {F : Type}
    (s entry post : LoopSemStateFiniteExact width F) (loc : Nat) (regs : List Nat)
    (vals : List (WordLocW width)) (env : Spt (WordLocW width)) (body : HolLoopProg width)
    (out : LoopResultExact width) (slack budget : Nat)
    (get : getVars regs s = some vals)
    (found : findCode (some loc) vals s.code = some (env,body))
    (nonzero : s.clock ≠ 0)
    (sync : {decClock s with locals := env} = {entry with clock := entry.clock+slack})
    (bodyRun : evaluate body {entry with clock := entry.clock+(slack+budget)} = (some out,post))
    (notBreak : ∀ n, out ≠ .break n) (notContinue : ∀ n, out ≠ .continue n) :
    evaluate (.call none (some loc) regs none) {s with clock := s.clock+budget} = (some out,post) := by
  have get' : getVars regs {s with clock := s.clock+budget} = some vals := by
    rw [getVars_upd_clock,get]
  have align : {decClock {s with clock := s.clock+budget} with locals := env} =
      {{decClock s with locals := env} with clock := (decClock s).clock+budget} := by
    simp only [decClock]
    congr 1
    omega
  have inner : {decClock {s with clock := s.clock+budget} with locals := env} =
      {entry with clock := entry.clock+(slack+budget)} := by
    have syncClock := congrArg LoopSemStateFiniteExact.clock sync
    simp only at syncClock
    rw [align,sync]
    simp only
    congr 1
    omega
  rw [evaluate]
  simp only [get',found,Option.isSome_none,Bool.false_eq_true,if_false]
  have nz : s.clock + budget ≠ 0 := by omega
  simp only [nz,inner,bodyRun]
  cases out <;> simp_all
/-- The concrete prefix and callee budgets execute the actual compiled tail call. -/
theorem compiledScalarTail_explicit_from_body {width : Nat} [NeZero width] {σ : Type}
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, CompiledScalar e)
    (source sourceFinal : CrepSemHOLState width σ) (values : List (HolWordLab width))
    (target : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (live : NumSet)
    (name : MlString) (params : List Nat) (body : CrepProgHOL width) (result : CrepResultHOLExact width)
    (out : LoopResultExact width) (prefixBudget bodyBudget : Nat) (cost : Nat → Nat)
    (tableOk : Spt (List Nat × HolLoopProg width) → Prop)
    (evaluated : args.mapM (evalCrepSemHOLExp source) = some values)
    (found : source.code.lookup name = some (params,body))
    (distinct : params.Nodup) (arity : params.length = values.length) (nonzero : source.clock ≠ 0)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (table : tableOk target.code)
    (prefixBound : LoopSteps.structuralWeight (loopNestedSeqHOL
      (compileExpsHOLExact ctxt (ctxt.vmax+1) live args).1) ≤ prefixBudget)
    (bodySim : BodySimulationAt body (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
      (listToNumSetHOLExact (List.range params.length))
      (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)}) cost tableOk)
    (bodyRun : evalCrepSemHOLProgExact
      (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)}) body = (some result,sourceFinal))
    (bodyBudgetBound : cost (CrepSteps.steps body
      (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)})) ≤ bodyBudget)
    (resultMap : resultToLoop (some result) = some out)
    (notError : out ≠ .error) (notTimeout : out ≠ .timeOut)
    (notBreak : ∀ n, out ≠ .break n) (notContinue : ∀ n, out ≠ .continue n) :
    evalCrepSemHOLProgExact source (.call none name args) = (some result,CrepSemHOLState.emptyLocals sourceFinal) ∧
    ∃ final, evaluate (compileHOLExact ctxt live (.call none name args))
        {target with clock := target.clock+(prefixBudget+bodyBudget)} = (some out,final) ∧
      crepToLoopStateRelExact (CrepSemHOLState.emptyLocals sourceFinal) {final with clock := sourceFinal.clock} ∧
      crepToLoopMemRelHOLExact sourceFinal.memory final.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals final.globals ∧
      crepToLoopCodeRelExact ctxt sourceFinal.code final.code := by
  let comp := compileExpsHOLExact ctxt (ctxt.vmax+1) live args
  let regs := genTemps comp.2.2.1 comp.2.1.length
  let vals := values.map wlabWlocExact
  let formals := List.range params.length
  let sourceEntry := decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)}
  let calleeCtxt := ctxtFcExact ctxt.target ctxt.funcs params formals
  obtain ⟨post,pre,assign,get,_,clock,codeSame,lookup,sync,st,mem,gl,code,locals⟩ :=
    scalarCall_calleeEntry_explicit args shape source values target ctxt live name params body prefixBudget
      evaluated found distinct arity stateRel memRel globalsRel codeRel localsRel prefixBound
  let middle : LoopSemStateFiniteExact width σ := {post with locals := sptAlistInsert regs vals post.locals}
  let entry : LoopSemStateFiniteExact width σ :=
    {decClock {post with clock := source.clock} with locals := sptFromAList (formals.zip vals)}
  let slack := post.clock-source.clock
  have tableEntry : tableOk entry.code := by simpa [entry,decClock,codeSame] using table
  have bodyNonerror : some result ≠ some .error := by
    intro h
    have : resultToLoop (some result) = some .error := by rw [h]; rfl
    rw [resultMap] at this
    exact notError (Option.some.inj this)
  have bodyNoTimeout : resultToLoop (some result) ≠ some .timeOut := by
    rw [resultMap]
    simpa using notTimeout
  obtain ⟨bodyPost,bodyEval,bodySt,bodyMem,bodyGl,bodyCode,_⟩ :=
    BodySimulationAt.explicit body calleeCtxt (listToNumSetHOLExact formals) sourceEntry sourceFinal
      (some result) entry cost bodyBudget tableOk bodySim bodyRun bodyNonerror bodyNoTimeout
      st mem gl code tableEntry bodyBudgetBound locals
  rw [resultMap] at bodyEval
  have bodyShift := evaluate_add_clock_eq _ _ _ bodyPost slack bodyEval (by simpa using notTimeout)
  have bodyShift' : evaluate (compileHOLExact calleeCtxt (listToNumSetHOLExact formals) body)
      {entry with clock := entry.clock+(slack+bodyBudget)} =
      (some out,{bodyPost with clock := bodyPost.clock+slack}) := by
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using bodyShift
  have optRun : evaluate (optimiseHOL (compileHOLExact calleeCtxt (listToNumSetHOLExact formals) body))
      {entry with clock := entry.clock+(slack+bodyBudget)} = (some out,{bodyPost with clock := bodyPost.clock+slack}) := by
    apply optimise_correct
    exact ⟨bodyShift',by simpa using notError,by simpa using notBreak,by simpa using notContinue,by simp⟩
  have sync' : {decClock middle with locals := sptFromAList (formals.zip vals)} =
      {entry with clock := entry.clock+slack} := sync nonzero
  have middleNonzero : middle.clock ≠ 0 := by dsimp [middle]; omega
  have tailRun := loopTail_explicit_run middle entry {bodyPost with clock := bodyPost.clock+slack}
    (findLabExact ctxt name) regs vals (sptFromAList (formals.zip vals))
    (ocompileHOLExact calleeCtxt (listToNumSetHOLExact formals) body) out slack bodyBudget
    get lookup middleNonzero sync' (by simpa [ocompileHOLExact] using optRun) notBreak notContinue
  have prefixShift := evaluate_add_clock_eq (loopNestedSeqHOL comp.1)
    {target with clock := target.clock+prefixBudget} none post bodyBudget pre (by simp)
  have assignShift := evaluate_add_clock_eq (loopNestedSeqHOL (regs.zipWith HolLoopProg.assign comp.2.1))
    post none middle bodyBudget assign (by simp)
  have compiled : compileHOLExact ctxt live (.call none name args) =
      loopNestedSeqHOL (comp.1 ++ (regs.zipWith HolLoopProg.assign comp.2.1) ++
        [.call none (some (findLabExact ctxt name)) regs none]) := by
    simp [compileHOLExact,comp,regs,List.append_assoc]
  have sourceTail : evalCrepSemHOLProgExact source (.call none name args) = (some result,CrepSemHOLState.emptyLocals sourceFinal) := by
    rw [evalCrepSemHOLProgExact_call_holShape]
    simp only [evaluated,lookupCodeFiniteHOL,found,arity,distinct,true_and,if_true,
      crepReturnInfoNodupError,nonzero,if_false]
    simp only [decClockCrepSemHOL] at bodyRun ⊢
    rw [bodyRun]
    cases result with
    | «break» n =>
      simp only [resultToLoop,Option.some.injEq] at resultMap
      exact False.elim (notBreak n resultMap.symm)
    | «continue» n =>
      simp only [resultToLoop,Option.some.injEq] at resultMap
      exact False.elim (notContinue n resultMap.symm)
    | «return» _ | exception _ | timeOut | finalFfi _ | error => rfl
  refine ⟨sourceTail,{bodyPost with clock := bodyPost.clock+slack},?_,?_,?_,?_,?_⟩
  · rw [compiled,List.append_assoc]
    rw [evaluate_nested_seq_append_none comp.1 _ _ _ (by simpa [Nat.add_assoc] using prefixShift)]
    rw [evaluate_nested_seq_append_none _ _ _ _ assignShift]
    simp only [loopNestedSeqHOL,evaluate_seq,tailRun]
  · simpa [crepToLoopStateRelExact,CrepSemHOLState.emptyLocals] using bodySt
  · exact bodyMem
  · exact bodyGl
  · simpa [crepToLoopCodeRelExact,calleeCtxt,ctxtFcExact] using bodyCode

private theorem returningLocals_live {width : Nat} [NeZero width]
    (live : NumSet) (locals : Spt (WordLocW width)) (names : List Nat) (values : List (WordLocW width))
    (subset : sptSubsetLive live locals) :
    sptSubsetLive live (sptAlistInsert names values (sptInter locals live)) := by
  intro k hk
  have present : (sptLookup k locals).isSome := subset k hk
  have hkLive : (sptLookup k live).isSome := hk
  show (sptLookup k (sptAlistInsert names values (sptInter locals live))).isSome
  rw [lookup_alist_insert_any]
  split
  · rw [sptLookup_sptInter, if_pos hkLive]
    exact present
  · rfl
private theorem loopReturning_normal_run {width : Nat} [NeZero width] {F : Type}
    (s post : LoopSemStateFiniteExact width F) (loc : Nat) (args names : List Nat)
    (live : NumSet) (exc : Nat) (body : HolLoopProg width)
    (values returned : List (WordLocW width)) (env : Spt (WordLocW width))
    (get : getVars args s = some values) (found : findCode (some loc) values s.code = some (env,body))
    (namesDistinct : names.Nodup) (subset : sptSubsetLive live s.locals) (clock : s.clock ≠ 0)
    (bodyRun : evaluate body {decClock {s with locals := sptInter s.locals live} with locals := env} =
      (some (.result returned),post))
    (arity : returned.length = names.length) (postClock : post.clock ≠ 0) :
    let cut := decClock {s with locals := sptInter s.locals live}
    let after := setVars names returned {post with locals := cut.locals}
    (evaluate (.call (some (names,live)) (some loc) args (some (exc,.raise exc,.skip,live))) s).1 = none ∧
    evaluate (.call (some (names,live)) (some loc) args (some (exc,.raise exc,.skip,live))) s =
      (none,decClock {after with locals := sptInter after.locals live}) := by
  let cut := decClock {s with locals := sptInter s.locals live}
  let after := setVars names returned {post with locals := cut.locals}
  have cutRun : cutRes live (none,s) = (none,cut) := by
    simp [cutRes,cutState_of_subset live s subset,cut,decClock,clock]
  have h := SteppedFlapjack.LoopSteps.evaluate_call_returning_success (some loc) args names live live exc
    (.raise exc) .skip s cut post values returned env body get found namesDistinct cutRun bodyRun arity
  have afterSubset : sptSubsetLive live after.locals := by
    simpa [after,cut,decClock,setVars] using returningLocals_live live s.locals names returned subset
  have finalCut : cutRes live (none,after) = (none,decClock {after with locals := sptInter after.locals live}) := by
    rw [cutRes]
    simp only
    rw [cutState_of_subset live after afterSubset]
    simp [decClock,after,setVars,postClock]
  have run : evaluate (.call (some (names,live)) (some loc) args (some (exc,.raise exc,.skip,live))) s =
      (none,decClock {after with locals := sptInter after.locals live}) := by
    rw [h]
    simpa [evaluate] using finalCut
  exact ⟨by rw [run],run⟩

private theorem returning_callee_prepare {width : Nat} [NeZero width] {σ : Type}
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, CompiledScalar e)
    (source sourceFinal : CrepSemHOLState width σ) (values : List (HolWordLab width))
    (target : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (live : NumSet)
    (name : MlString) (params names returnNames : List Nat) (body : CrepProgHOL width)
    (result : CrepResultHOLExact width) (out : LoopResultExact width)
    (prefixBudget bodyBudget : Nat) (cost : Nat → Nat)
    (tableOk : Spt (List Nat × HolLoopProg width) → Prop)
    (evaluated : args.mapM (evalCrepSemHOLExp source) = some values)
    (found : source.code.lookup name = some (params,body))
    (distinct : params.Nodup) (arity : params.length = values.length) (nonzero : source.clock ≠ 0)
    (namesDistinct : names.Nodup) (mapped : names.mapM ctxt.vars.lookup = some returnNames)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (table : tableOk target.code)
    (prefixBound : LoopSteps.structuralWeight (loopNestedSeqHOL
      (compileExpsHOLExact ctxt (ctxt.vmax+1) live args).1) ≤ prefixBudget)
    (bodySim : BodySimulationAt body (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
      (listToNumSetHOLExact (List.range params.length))
      (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)}) cost tableOk)
    (bodyRun : evalCrepSemHOLProgExact
      (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)}) body =
        (some result,sourceFinal))
    (bodyBudgetBound : cost (CrepSteps.steps body
      (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)})) ≤ bodyBudget) (resultMap : resultToLoop (some result) = some out)
    (notError : out ≠ .error) (notTimeout : out ≠ .timeOut)
    (notBreak : ∀ n, out ≠ .break n) (notContinue : ∀ n, out ≠ .continue n) :
    let comp := compileExpsHOLExact ctxt (ctxt.vmax+1) live args
    let regs := genTemps comp.2.2.1 comp.2.1.length
    let vals := values.map wlabWlocExact
    let formals := List.range params.length
    let calleeCtxt := ctxtFcExact ctxt.target ctxt.funcs params formals
    let extra := bodyBudget+1
    ∃ (post bodyPost : LoopSemStateFiniteExact width σ),
      let middle : LoopSemStateFiniteExact width σ := {post with locals := sptAlistInsert regs vals post.locals}
      let shifted : LoopSemStateFiniteExact width σ := {middle with clock := middle.clock+extra}
      evaluate (loopNestedSeqHOL comp.1) {target with clock := target.clock+(prefixBudget+extra)} =
        (none,{post with clock := post.clock+extra}) ∧
      evaluate (loopNestedSeqHOL (regs.zipWith HolLoopProg.assign comp.2.1))
        {post with clock := post.clock+extra} = (none,shifted) ∧
      getVars regs shifted = some vals ∧
      findCode (some (findLabExact ctxt name)) vals shifted.code =
        some (sptFromAList (formals.zip vals),ocompileHOLExact calleeCtxt (listToNumSetHOLExact formals) body) ∧
      returnNames.Nodup ∧ sptSubsetLive live shifted.locals ∧ shifted.clock ≠ 0 ∧
      evaluate (ocompileHOLExact calleeCtxt (listToNumSetHOLExact formals) body)
        {decClock {shifted with locals := sptInter shifted.locals live} with
          locals := sptFromAList (formals.zip vals)} = (some out,bodyPost) ∧ bodyPost.clock ≠ 0 := by
  let comp := compileExpsHOLExact ctxt (ctxt.vmax+1) live args
  let regs := genTemps comp.2.2.1 comp.2.1.length
  let vals := values.map wlabWlocExact
  let formals := List.range params.length
  let sourceEntry := decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)}
  let calleeCtxt := ctxtFcExact ctxt.target ctxt.funcs params formals
  obtain ⟨post,pre,assign,get,subset,clock,codeSame,lookup,sync,st,mem,gl,code,locals⟩ :=
    scalarCall_calleeEntry_explicit args shape source values target ctxt live name params body prefixBudget
      evaluated found distinct arity stateRel memRel globalsRel codeRel localsRel prefixBound
  let middle : LoopSemStateFiniteExact width σ := {post with locals := sptAlistInsert regs vals post.locals}
  let entry : LoopSemStateFiniteExact width σ :=
    {decClock {post with clock := source.clock} with locals := sptFromAList (formals.zip vals)}
  let slack := post.clock-source.clock
  have tableEntry : tableOk entry.code := by simpa [entry,decClock,codeSame] using table
  have bodyNonerror : some result ≠ some .error := by
    intro h
    have : resultToLoop (some result) = some .error := by rw [h]; rfl
    rw [resultMap] at this
    exact notError (Option.some.inj this)
  have bodyNoTimeout : resultToLoop (some result) ≠ some .timeOut := by rw [resultMap]; simpa using notTimeout
  obtain ⟨bodyPost,bodyEval,_,_,_,_,_⟩ :=
    BodySimulationAt.explicit body calleeCtxt (listToNumSetHOLExact formals) sourceEntry sourceFinal
      (some result) entry cost bodyBudget tableOk bodySim bodyRun bodyNonerror bodyNoTimeout
      st mem gl code tableEntry bodyBudgetBound locals
  rw [resultMap] at bodyEval
  have bodyShift := evaluate_add_clock_eq _ _ _ bodyPost (slack+1) bodyEval (by simpa using notTimeout)
  have bodyShift' : evaluate (compileHOLExact calleeCtxt (listToNumSetHOLExact formals) body)
      {entry with clock := entry.clock+(slack+(bodyBudget+1))} =
      (some out,{bodyPost with clock := bodyPost.clock+(slack+1)}) := by
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using bodyShift
  have optRun : evaluate (optimiseHOL (compileHOLExact calleeCtxt (listToNumSetHOLExact formals) body))
      {entry with clock := entry.clock+(slack+(bodyBudget+1))} =
      (some out,{bodyPost with clock := bodyPost.clock+(slack+1)}) := by
    apply optimise_correct
    exact ⟨bodyShift',by simpa using notError,by simpa using notBreak,by simpa using notContinue,by simp⟩
  have nd : returnNames.Nodup := by
    have h := allDistinctCtxtLookupAllDistinctExact ctxt names (ctxt.vmax + 1) namesDistinct localsRel.1
    simp only [rtVars,FLOOKUP] at h
    rw [mapped] at h
    exact h
  let extra := bodyBudget+1
  let shifted : LoopSemStateFiniteExact width σ := {middle with clock := middle.clock+extra}
  have shiftedGet : getVars regs shifted = some vals := by simpa [shifted,getVars_upd_clock] using get
  have shiftedFind : findCode (some (findLabExact ctxt name)) vals shifted.code =
      some (sptFromAList (formals.zip vals),ocompileHOLExact calleeCtxt (listToNumSetHOLExact formals) body) := by
    simpa [shifted,middle] using lookup
  have shiftedSubset : sptSubsetLive live shifted.locals := by simpa [shifted,middle] using subset
  have shiftedNonzero : shifted.clock ≠ 0 := by dsimp [shifted,middle,extra]; omega
  have entryEq : {decClock {shifted with locals := sptInter shifted.locals live} with
        locals := sptFromAList (formals.zip vals)} = {entry with clock := entry.clock+(slack+extra)} := by
    have base := sync nonzero
    have baseClock := congrArg LoopSemStateFiniteExact.clock base
    change (decClock middle).clock = entry.clock + slack at baseClock
    have aligned : {decClock shifted with locals := sptFromAList (formals.zip vals)} =
        {{decClock middle with locals := sptFromAList (formals.zip vals)} with
          clock := (decClock middle).clock + extra} := by
      simp only [shifted,decClock]
      congr 1
      dsimp [middle]
      omega
    change {decClock shifted with locals := sptFromAList (formals.zip vals)} = _
    rw [aligned,base]
    simp only
    congr 1
    omega
  have optRun' : evaluate (ocompileHOLExact calleeCtxt (listToNumSetHOLExact formals) body)
      {decClock {shifted with locals := sptInter shifted.locals live} with locals := sptFromAList (formals.zip vals)} =
      (some out,{bodyPost with clock := bodyPost.clock+(slack+1)}) := by
    rw [entryEq]
    simpa [extra,ocompileHOLExact] using optRun
  have prefixShift := evaluate_add_clock_eq (loopNestedSeqHOL comp.1)
    {target with clock := target.clock+prefixBudget} none post extra pre (by simp)
  have assignShift := evaluate_add_clock_eq (loopNestedSeqHOL (regs.zipWith HolLoopProg.assign comp.2.1))
    post none middle extra assign (by simp)
  refine ⟨post,{bodyPost with clock := bodyPost.clock+(slack+1)},?_,?_,shiftedGet,shiftedFind,nd,shiftedSubset,shiftedNonzero,optRun',?_⟩
  · simpa [Nat.add_assoc] using prefixShift
  · exact assignShift
  · simp [slack]


/-- Terminal outcomes propagated through an ordinary call. -/
inductive CallTerminal {width : Nat} [NeZero width] : CrepResultHOLExact width → LoopResultExact width → Prop
 | exception (eid : BitVec width) : CallTerminal (.exception eid) (.exception (.word eid))
 | ffi (event : HolFinalEvent) : CallTerminal (.finalFfi event) (.finalFfi event)

private theorem loopReturning_terminal_run {width : Nat} [NeZero width] {F : Type}
    (s post : LoopSemStateFiniteExact width F) (loc : Nat) (args names : List Nat)
    (live : NumSet) (exc : Nat) (body : HolLoopProg width)
    (values : List (WordLocW width)) (result : CrepResultHOLExact width) (out : LoopResultExact width)
    (terminal : CallTerminal result out) (env : Spt (WordLocW width))
    (get : getVars args s = some values) (found : findCode (some loc) values s.code = some (env,body))
    (namesDistinct : names.Nodup) (subset : sptSubsetLive live s.locals) (clock : s.clock ≠ 0)
    (bodyRun : evaluate body {decClock {s with locals := sptInter s.locals live} with locals := env} =
      (some out,post)) :
    (evaluate (.call (some (names,live)) (some loc) args (some (exc,.raise exc,.skip,live))) s).1 = some out := by
  let cut := decClock {s with locals := sptInter s.locals live}
  have cutRun : cutRes live (none,s) = (none,cut) := by
    simp [cutRes,cutState_of_subset live s subset,cut,decClock,clock]
  rw [evaluate]
  simp only [get,found,namesDistinct,not_true_eq_false,if_false]
  rw [cutRun]
  simp only
  rw [fix_clock_evaluate,bodyRun]
  cases terminal <;> simp [evaluate,cutRes,setVar,sptLookup_sptInsert]

/-- A returning call runs at the sum of the prefix, callee, and continuation budgets. -/
theorem compiledScalarReturning_explicit_from_body {width : Nat} [NeZero width] {σ : Type}
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, CompiledScalar e)
    (source sourceFinal : CrepSemHOLState width σ) (values returned : List (HolWordLab width))
    (target : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (live : NumSet)
    (name : MlString) (params names : List Nat) (body : CrepProgHOL width)
    (prefixBudget bodyBudget : Nat) (cost : Nat → Nat)
    (tableOk : Spt (List Nat × HolLoopProg width) → Prop)
    (evaluated : args.mapM (evalCrepSemHOLExp source) = some values)
    (found : source.code.lookup name = some (params,body))
    (distinct : params.Nodup) (arity : params.length = values.length) (nonzero : source.clock ≠ 0)
    (namesDistinct : names.Nodup)
    (existing : ∃ old, names.mapM source.locals.lookup = some old) (retArity : returned.length = names.length)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (table : tableOk target.code)
    (prefixBound : LoopSteps.structuralWeight (loopNestedSeqHOL
      (compileExpsHOLExact ctxt (ctxt.vmax+1) live args).1) ≤ prefixBudget)
    (bodySim : BodySimulationAt body (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
      (listToNumSetHOLExact (List.range params.length))
      (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)}) cost tableOk)
    (bodyRun : evalCrepSemHOLProgExact
      (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)}) body =
        (some (.return returned),sourceFinal))
    (bodyBudgetBound : cost (CrepSteps.steps body
      (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)})) ≤ bodyBudget) :
    let finalSource := {sourceFinal with locals := source.locals.updateListEq (names.zip returned)}
    evalCrepSemHOLProgExact source (.call (some (names,none)) name args) = (none,finalSource) ∧
    ∃ final, evaluate (compileHOLExact ctxt live (.call (some (names,none)) name args))
        {target with clock := target.clock+(prefixBudget+(bodyBudget+1))} = (none,final) ∧
      crepToLoopStateRelExact finalSource {final with clock := finalSource.clock} ∧
      crepToLoopMemRelHOLExact finalSource.memory final.memory finalSource.memaddrs ∧
      crepToLoopGlobalsRelHOLExact finalSource.globals final.globals ∧
      crepToLoopCodeRelExact ctxt finalSource.code final.code ∧
      crepToLoopLocalsRelExact ctxt live finalSource.locals final.locals := by
  obtain ⟨old, oldLookup⟩ := existing
  obtain ⟨returnNames, mapped, _⟩ :=
    returnRegisters_of_locals ctxt live source.locals target.locals names old oldLookup namesDistinct localsRel
  let comp := compileExpsHOLExact ctxt (ctxt.vmax+1) live args
  let regs := genTemps comp.2.2.1 comp.2.1.length
  let vals := values.map wlabWlocExact
  let formals := List.range params.length
  let calleeCtxt := ctxtFcExact ctxt.target ctxt.funcs params formals
  let extra := bodyBudget+1
  obtain ⟨post,bodyPost,pre,assign,get,lookup,nd,subset,nz,optRun,postClock⟩ :=
    returning_callee_prepare args shape source sourceFinal values target ctxt live name params names returnNames body
      (.return returned) (.result (returned.map wlabWlocExact)) prefixBudget bodyBudget cost tableOk evaluated found distinct arity nonzero
      namesDistinct mapped stateRel memRel globalsRel codeRel localsRel table prefixBound bodySim bodyRun bodyBudgetBound
      (by simp [resultToLoop]) (by simp) (by simp) (by simp) (by simp)
  let middle : LoopSemStateFiniteExact width σ := {post with locals := sptAlistInsert regs vals post.locals}
  let shifted : LoopSemStateFiniteExact width σ := {middle with clock := middle.clock+extra}
  have returnLen : (returned.map wlabWlocExact).length = returnNames.length := by
    have h := opt_mmap_length_eq names _ returnNames mapped
    simp only [List.length_map]
    omega
  have targetCall := loopReturning_normal_run shifted bodyPost
    (findLabExact ctxt name) regs returnNames live (ctxt.vmax+1)
    (ocompileHOLExact calleeCtxt (listToNumSetHOLExact formals) body) vals
    (returned.map wlabWlocExact) (sptFromAList (formals.zip vals)) get lookup nd subset nz
    optRun returnLen postClock
  let targetFinal := (evaluate (.call (some (returnNames,live)) (some (findLabExact ctxt name)) regs
    (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))) shifted).2
  have callRun : evaluate (.call (some (returnNames,live)) (some (findLabExact ctxt name)) regs
    (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))) shifted = (none,targetFinal) := by
    exact Prod.ext targetCall.1 rfl
  have compiled : compileHOLExact ctxt live (.call (some (names,none)) name args) =
      loopNestedSeqHOL (comp.1 ++ (regs.zipWith HolLoopProg.assign comp.2.1) ++
        [.call (some (returnNames,live)) (some (findLabExact ctxt name)) regs
          (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))]) := by
    simp [compileHOLExact,comp,regs,mapped,List.append_assoc]
  have targetRun : evaluate (compileHOLExact ctxt live (.call (some (names,none)) name args))
      {target with clock := target.clock+(prefixBudget+extra)} = (none,targetFinal) := by
    rw [compiled,List.append_assoc]
    rw [evaluate_nested_seq_append_none comp.1 _ _ _ pre]
    rw [evaluate_nested_seq_append_none _ _ _ _ assign]
    simp only [loopNestedSeqHOL,evaluate_seq]
    have callRun' : evaluate (.call (some (returnNames,live)) (some (findLabExact ctxt name)) regs
      (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live)))
      {middle with clock := middle.clock+extra} = (none,targetFinal) := callRun
    rw [callRun']
    simp [evaluate]
  let finalSource := {sourceFinal with locals := source.locals.updateListEq (names.zip returned)}
  have sourceRun : evalCrepSemHOLProgExact source (.call (some (names,none)) name args) = (none,finalSource) := by
    rw [evalCrepSemHOLProgExact_call_holShape]
    simp only [evaluated,lookupCodeFiniteHOL,found,arity,distinct,true_and,if_true,
      crepReturnInfoNodupError,namesDistinct,not_true_eq_false,if_false,nonzero]
    simp only [decClockCrepSemHOL] at bodyRun ⊢
    rw [bodyRun]
    simp [retArity,oldLookup,finalSource]
  have rel := compiler_run_relations (.call (some (names,none)) name args) source finalSource none target targetFinal
    ctxt live (prefixBudget+extra) sourceRun (by simp) (by simp [resultToLoop]) stateRel memRel globalsRel codeRel localsRel
    (by simpa [resultToLoop] using targetRun)
  refine ⟨sourceRun,targetFinal,?_,rel.1,rel.2.1,rel.2.2.1,rel.2.2.2.1,?_⟩
  · simpa [extra] using targetRun
  · simpa [localsResultRel] using rel.2.2.2.2



/-- Ordinary calls propagate exceptions and final FFI events at a concrete clock budget. -/
theorem compiledScalarReturning_terminal_explicit_from_body {width : Nat} [NeZero width] {σ : Type}
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, CompiledScalar e)
    (source sourceFinal : CrepSemHOLState width σ) (values : List (HolWordLab width))
    (target : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (live : NumSet)
    (name : MlString) (params names returnNames : List Nat) (body : CrepProgHOL width)
    (result : CrepResultHOLExact width) (out : LoopResultExact width) (terminal : CallTerminal result out)
    (prefixBudget bodyBudget : Nat) (cost : Nat → Nat)
    (tableOk : Spt (List Nat × HolLoopProg width) → Prop)
    (evaluated : args.mapM (evalCrepSemHOLExp source) = some values)
    (found : source.code.lookup name = some (params,body))
    (distinct : params.Nodup) (arity : params.length = values.length) (nonzero : source.clock ≠ 0)
    (namesDistinct : names.Nodup) (mapped : names.mapM ctxt.vars.lookup = some returnNames)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals)
    (table : tableOk target.code)
    (prefixBound : LoopSteps.structuralWeight (loopNestedSeqHOL
      (compileExpsHOLExact ctxt (ctxt.vmax+1) live args).1) ≤ prefixBudget)
    (bodySim : BodySimulationAt body (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
      (listToNumSetHOLExact (List.range params.length))
      (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)}) cost tableOk)
    (bodyRun : evalCrepSemHOLProgExact
      (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)}) body =
        (some result,sourceFinal))
    (bodyBudgetBound : cost (CrepSteps.steps body
      (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)})) ≤ bodyBudget) :
    let finalSource := CrepSemHOLState.emptyLocals sourceFinal
    evalCrepSemHOLProgExact source (.call (some (names,none)) name args) = (some result,finalSource) ∧
    ∃ final, evaluate (compileHOLExact ctxt live (.call (some (names,none)) name args))
        {target with clock := target.clock+(prefixBudget+(bodyBudget+1))} = (some out,final) ∧
      crepToLoopStateRelExact finalSource {final with clock := finalSource.clock} ∧
      crepToLoopMemRelHOLExact finalSource.memory final.memory finalSource.memaddrs ∧
      crepToLoopGlobalsRelHOLExact finalSource.globals final.globals ∧
      crepToLoopCodeRelExact ctxt finalSource.code final.code := by
  let comp := compileExpsHOLExact ctxt (ctxt.vmax+1) live args
  let regs := genTemps comp.2.2.1 comp.2.1.length
  let vals := values.map wlabWlocExact
  let formals := List.range params.length
  let calleeCtxt := ctxtFcExact ctxt.target ctxt.funcs params formals
  let extra := bodyBudget+1
  obtain ⟨post,bodyPost,pre,assign,get,lookup,nd,subset,nz,optRun,_⟩ :=
    returning_callee_prepare args shape source sourceFinal values target ctxt live name params names returnNames body
      result out prefixBudget bodyBudget cost tableOk evaluated found distinct arity nonzero
      namesDistinct mapped stateRel memRel globalsRel codeRel localsRel table prefixBound bodySim bodyRun bodyBudgetBound
      (by cases terminal <;> simp [resultToLoop]) (by cases terminal <;> simp) (by cases terminal <;> simp) (by cases terminal <;> simp) (by cases terminal <;> simp)
  let middle : LoopSemStateFiniteExact width σ := {post with locals := sptAlistInsert regs vals post.locals}
  let shifted : LoopSemStateFiniteExact width σ := {middle with clock := middle.clock+extra}
  have targetResult := loopReturning_terminal_run shifted bodyPost (findLabExact ctxt name) regs returnNames live (ctxt.vmax+1)
    (ocompileHOLExact calleeCtxt (listToNumSetHOLExact formals) body) vals result out terminal
    (sptFromAList (formals.zip vals)) get lookup nd subset nz optRun
  let targetFinal := (evaluate (.call (some (returnNames,live)) (some (findLabExact ctxt name)) regs
    (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))) shifted).2
  have callRun : evaluate (.call (some (returnNames,live)) (some (findLabExact ctxt name)) regs
    (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))) shifted = (some out,targetFinal) := by
    exact Prod.ext targetResult rfl
  have compiled : compileHOLExact ctxt live (.call (some (names,none)) name args) =
      loopNestedSeqHOL (comp.1 ++ (regs.zipWith HolLoopProg.assign comp.2.1) ++
        [.call (some (returnNames,live)) (some (findLabExact ctxt name)) regs
          (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))]) := by
    simp [compileHOLExact,comp,regs,mapped,List.append_assoc]
  have targetRun : evaluate (compileHOLExact ctxt live (.call (some (names,none)) name args))
      {target with clock := target.clock+(prefixBudget+extra)} = (some out,targetFinal) := by
    rw [compiled,List.append_assoc]
    rw [evaluate_nested_seq_append_none comp.1 _ _ _ pre]
    rw [evaluate_nested_seq_append_none _ _ _ _ assign]
    simp only [loopNestedSeqHOL,evaluate_seq]
    have callRun' : evaluate (.call (some (returnNames,live)) (some (findLabExact ctxt name)) regs
      (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live)))
      {middle with clock := middle.clock+extra} = (some out,targetFinal) := callRun
    rw [callRun']
  let finalSource := CrepSemHOLState.emptyLocals sourceFinal
  have sourceRun : evalCrepSemHOLProgExact source (.call (some (names,none)) name args) =
      (some result,finalSource) := by
    rw [evalCrepSemHOLProgExact_call_holShape]
    simp only [evaluated,lookupCodeFiniteHOL,found,arity,distinct,true_and,if_true,
      crepReturnInfoNodupError,namesDistinct,not_true_eq_false,if_false,nonzero]
    simp only [decClockCrepSemHOL] at bodyRun ⊢
    rw [bodyRun]
    cases terminal <;> rfl
  have rel := compiler_run_relations (.call (some (names,none)) name args) source finalSource (some result) target targetFinal
    ctxt live (prefixBudget+extra) sourceRun (by cases terminal <;> simp) (by cases terminal <;> simp [resultToLoop]) stateRel memRel globalsRel codeRel localsRel
    (by cases terminal <;> simpa [resultToLoop] using targetRun)
  exact ⟨sourceRun,targetFinal,by simpa [extra] using targetRun,rel.1,rel.2.1,rel.2.2.1,rel.2.2.2.1⟩



end SteppedFlapjack.CrepToLoopSteps
