import SteppedFlapjack.CrepToLoopSteps.ScalarClockCompositional
import SteppedFlapjack.CrepSteps.CallClock
import SteppedFlapjack.CrepToLoopSteps.CallCost
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

/-- Initialized source return variables have distinct compiler registers. -/
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

/-- At zero source clock, ordinary and tail calls simulate the immediate timeout within the syntax-derived budget. -/
theorem call_zeroClock_sim {width : Nat} [NeZero width] {σ : Type}
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, CompiledScalar e)
    (ret : Option (List Nat)) (source : CrepSemHOLState width σ) (ctxt ref : CrepToLoopContextExact) (live : NumSet)
    (name : MlString) (factor : Nat) (tableOk : Spt (List Nat × HolLoopProg width) → Prop)
    (zero : source.clock = 0) (syntaxBound : callSyntaxCost ref (.call (ret.map (fun ns => (ns,none))) name args) ≤ factor) :
    BodySimulationAt (.call (ret.map (fun ns => (ns,none))) name args) ctxt live source (fun n => factor*(n+1)) tableOk := by
  intro sourceFinal result target run nonerror stateRel memRel globalsRel codeRel table localsRel
  obtain ⟨values,params,body,evaluated,found,arity,distinct,retDistinct,branch⟩ :=
    CrepSteps.nonerrorCall_reaches_callee ret name args source sourceFinal result run nonerror
  rcases branch with ⟨_,rfl,rfl⟩ | ⟨_,_,nz,_,_,_,_,_,_⟩
  case inr => exact (nz zero).elim
  case inl =>
    let comp := compileExpsHOLExact ctxt (ctxt.vmax+1) live args
    let regs := genTemps comp.2.2.1 comp.2.1.length
    let vals := values.map wlabWlocExact
    obtain ⟨extra,post,pre,assign,get,subset,st,mem,gl,code,locals,bound⟩ :=
      scalarCall_argumentPrefix args shape source values target ctxt live evaluated stateRel memRel globalsRel codeRel localsRel
    let middle : LoopSemStateFiniteExact width σ := {post with locals := sptAlistInsert regs vals post.locals}
    have middleClock : middle.clock = 0 := by
      change post.clock = 0
      exact st.2.2.1.symm.trans zero
    have get' : getVars regs middle = some vals := get
    have cRel : crepToLoopCodeRelExact ctxt source.code middle.code := by simpa [middle] using code
    have lookup := call_lookup ctxt source middle name params body vals cRel found (by simp [vals,arity])
    have targetRun : evaluate (compileHOLExact ctxt live (.call (ret.map (fun ns => (ns,none))) name args))
        {target with clock := target.clock+extra} = (some .timeOut,{middle with locals := .ln}) := by
      cases ret with
      | none =>
        have callRun : evaluate (.call none (some (findLabExact ctxt name)) regs none) middle =
            (some .timeOut,{middle with locals := .ln}) := by
          rw [evaluate]
          simp [get',lookup,middleClock]
        have compiled : compileHOLExact ctxt live (.call none name args) =
          loopNestedSeqHOL (comp.1 ++ (regs.zipWith HolLoopProg.assign comp.2.1) ++
            [.call none (some (findLabExact ctxt name)) regs none]) := by
          simp [compileHOLExact,comp,regs,List.append_assoc]
        have targetRun' : evaluate (compileHOLExact ctxt live (.call none name args))
            {target with clock := target.clock+extra} = (some .timeOut,{middle with locals := .ln}) := by
          rw [compiled,List.append_assoc]
          rw [evaluate_nested_seq_append_none comp.1 _ _ _ pre]
          rw [evaluate_nested_seq_append_none _ _ _ _ assign]
          change evaluate (.seq (.call none (some (findLabExact ctxt name)) regs none) .skip) middle = _
          rw [evaluate_seq,callRun]
        exact targetRun'
      | some names =>
        have namesDistinct := retDistinct names rfl
        let returnNames := rtVars ctxt.vars.lookup names (ctxt.vmax+1)
        have returnDistinct : returnNames.Nodup :=
          allDistinctCtxtLookupAllDistinctExact ctxt names (ctxt.vmax+1) namesDistinct localsRel.1
        have cut : cutRes live (none,middle) = (some .timeOut,{middle with locals := .ln}) := by
          rw [cutRes]
          simp only
          rw [cutState_of_subset live middle subset]
          simp [middleClock]
        have callRun : evaluate (.call (some (returnNames,live)) (some (findLabExact ctxt name)) regs
            (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))) middle =
            (some .timeOut,{middle with locals := .ln}) := by
          rw [evaluate]
          simp [get',lookup,returnDistinct,cut]
        have compiled : compileHOLExact ctxt live (.call (some (names,none)) name args) =
          loopNestedSeqHOL (comp.1 ++ (regs.zipWith HolLoopProg.assign comp.2.1) ++
            [.call (some (returnNames,live)) (some (findLabExact ctxt name)) regs
              (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))]) := by
          simp [compileHOLExact,comp,regs,returnNames,rtVars,FLOOKUP,Nat.add_assoc,List.append_assoc]
          cases names.mapM ctxt.vars.lookup <;> simp
        have targetRun' : evaluate (compileHOLExact ctxt live (.call (some (names,none)) name args))
            {target with clock := target.clock+extra} = (some .timeOut,{middle with locals := .ln}) := by
          rw [compiled,List.append_assoc]
          rw [evaluate_nested_seq_append_none comp.1 _ _ _ pre]
          rw [evaluate_nested_seq_append_none _ _ _ _ assign]
          change evaluate (.seq (.call (some (returnNames,live)) (some (findLabExact ctxt name)) regs
            (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))) .skip) middle = _
          rw [evaluate_seq,callRun]
        exact targetRun'
    have prefixBound : LoopSteps.structuralWeight (loopNestedSeqHOL comp.1) ≤ factor := by
      have eq := scalarArgumentWeight args shape ctxt ref (ctxt.vmax+1) (ref.vmax+1) live .ln
      change _ = callArgumentsCost ref args at eq
      simp only [callSyntaxCost] at syntaxBound
      dsimp [comp]
      omega
    refine ⟨extra,some .timeOut,{middle with locals := .ln},targetRun,?_,?_,?_,?_,rfl,?_,?_⟩
    · simpa [CrepSemHOLState.emptyLocals,middle,crepToLoopStateRelExact] using st
    · simpa [CrepSemHOLState.emptyLocals,middle] using mem
    · simpa [CrepSemHOLState.emptyLocals,middle] using gl
    · simpa [CrepSemHOLState.emptyLocals,middle] using code
    · simp [localsResultRel]
    · have positive := CrepSteps.steps_pos (.call (ret.map (fun ns => (ns,none))) name args) source
      nlinarith

/-- Tail calls and ordinary calls with terminal results preserve exact clock relations within the syntax-derived budget. -/
theorem call_terminal_sim {width : Nat} [NeZero width] {σ : Type}
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, CompiledScalar e)
    (ret : Option (List Nat)) (source : CrepSemHOLState width σ) (ctxt ref : CrepToLoopContextExact) (live : NumSet)
    (name : MlString) (factor : Nat) (tableOk : Spt (List Nat × HolLoopProg width) → Prop)
    (syntaxBound : callSyntaxCost ref (.call (ret.map (fun ns => (ns,none))) name args) ≤ factor)
    (tailOrTerminal : ret = none ∨ (evalCrepSemHOLProgExact source (.call (ret.map (fun ns => (ns,none))) name args)).1 ≠ none)
    (bodySim : ∀ values params body,
      args.mapM (evalCrepSemHOLExp source) = some values → source.code.lookup name = some (params,body) →
      (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)}).clock < source.clock →
      BodySimulationAt body (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
        (listToNumSetHOLExact (List.range params.length))
        (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)})
        (fun n => factor*(n+1)) tableOk) :
    BodySimulationAt (.call (ret.map (fun ns => (ns,none))) name args) ctxt live source (fun n => factor*(n+1)) tableOk := by
  by_cases zero : source.clock = 0
  · exact call_zeroClock_sim args shape ret source ctxt ref live name factor tableOk zero syntaxBound
  · intro sourceFinal result target run nonerror stateRel memRel globalsRel codeRel table localsRel
    have only : ret = none ∨ result ≠ none := by simpa [run] using tailOrTerminal
    obtain ⟨values,params,body,evaluated,found,arity,distinct,retDistinct,branch⟩ :=
      CrepSteps.nonerrorCall_reaches_callee ret name args source sourceFinal _ run nonerror
    rcases branch with ⟨z,_,_⟩ | ⟨r,bodyFinal,nz,smaller,bodyRun,notError,notBreak,notContinue,outcome⟩
    · exact (zero z).elim
    have outcomeEq : result = some r ∧ sourceFinal = CrepSemHOLState.emptyLocals bodyFinal := by
      rcases only with tail | timeout
      · subst ret
        cases r <;> simp_all [CrepSteps.CallNonerrorOutcome]
      · cases ret <;> cases r <;> simp_all [CrepSteps.CallNonerrorOutcome]
    obtain ⟨rfl,rfl⟩ := outcomeEq
    obtain ⟨outValue,map,outNe,outBreak,outContinue⟩ : ∃ outValue : LoopResultExact width,
        resultToLoop (some r) = some outValue ∧ outValue ≠ .error ∧
        (∀ n, outValue ≠ .break n) ∧ (∀ n, outValue ≠ .continue n) := by
      cases r <;> simp_all [resultToLoop]

    let comp := compileExpsHOLExact ctxt (ctxt.vmax+1) live args
    let regs := genTemps comp.2.2.1 comp.2.1.length
    let vals := values.map wlabWlocExact
    let formals := List.range params.length
    let calleeCtxt := ctxtFcExact ctxt.target ctxt.funcs params formals
    let sourceEntry := decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)}
    obtain ⟨extra,post,pre,assign,get,subset,st,mem,gl,code,locals,bound⟩ :=
      scalarCall_argumentPrefix args shape source values target ctxt live evaluated stateRel memRel globalsRel codeRel localsRel
    let middle : LoopSemStateFiniteExact width σ := {post with locals := sptAlistInsert regs vals post.locals}
    let entry : LoopSemStateFiniteExact width σ := {decClock post with locals := sptFromAList (formals.zip vals)}
    have ent := call_entry_relations ctxt comp.2.2.2 source post name params body args values st mem gl code locals
      found distinct (by omega) ((optMmapEqSome args _ _).mp evaluated)
    have entState : crepToLoopStateRelExact sourceEntry entry := by simpa [sourceEntry,entry,formals,vals] using ent.1
    have entMem : crepToLoopMemRelHOLExact sourceEntry.memory entry.memory sourceEntry.memaddrs := by simpa [sourceEntry,entry] using ent.2.1
    have entGl : crepToLoopGlobalsRelHOLExact sourceEntry.globals entry.globals := by simpa [sourceEntry,entry] using ent.2.2.1
    have entCode : crepToLoopCodeRelExact calleeCtxt sourceEntry.code entry.code := by simpa [sourceEntry,entry,calleeCtxt,formals,vals] using ent.2.2.2.1
    have entLocals : crepToLoopLocalsRelExact calleeCtxt (listToNumSetHOLExact formals) sourceEntry.locals entry.locals := by simpa [sourceEntry,entry,calleeCtxt,formals,vals] using ent.2.2.2.2
    have entTable : tableOk entry.code := by
      have same := SteppedFlapjack.LoopLiveSteps.evaluate_code _ _ post none pre
      simpa [entry,decClock,same] using table
    obtain ⟨bodyExtra,out,bodyPost,bodyEval,bodySt,bodyMem,bodyGl,bodyCode,outEq,_,bodyBound⟩ :=
      bodySim values params body evaluated found smaller bodyFinal (some r) entry bodyRun (by simpa using notError)
        entState entMem entGl entCode entTable entLocals
    have outEq' : out = some outValue := outEq.trans map
    subst out
    have optRun : evaluate (ocompileHOLExact calleeCtxt (listToNumSetHOLExact formals) body)
      {entry with clock := entry.clock+bodyExtra} = (some outValue,bodyPost) := by
      unfold ocompileHOLExact
      apply optimise_correct
      rw [map] at bodyEval
      exact ⟨bodyEval,by simpa using outNe,by simpa using outBreak,by simpa using outContinue,by simp⟩
    have preShift := evaluate_add_clock_eq _ _ _ post bodyExtra pre (by simp)
    have assignShift := evaluate_add_clock_eq _ _ _ middle bodyExtra assign (by simp)
    let shifted : LoopSemStateFiniteExact width σ := {middle with clock := middle.clock+bodyExtra}
    have get' : getVars regs shifted = some vals := by simpa [shifted,getVars_upd_clock] using get
    have code' : crepToLoopCodeRelExact ctxt source.code shifted.code := by simpa [shifted,middle] using code
    have lookup := call_lookup ctxt source shifted name params body vals code' found (by simp [vals,arity])
    have shiftNonzero : shifted.clock ≠ 0 := by dsimp [shifted,middle]; have := st.2.2.1; omega
    have entryEq : {decClock shifted with locals := sptFromAList (formals.zip vals)} =
        {entry with clock := entry.clock+bodyExtra} := by
      simp only [shifted,entry,middle,decClock]
      congr 1
      have := st.2.2.1
      omega
    have bodyRun' : evaluate (ocompileHOLExact calleeCtxt (listToNumSetHOLExact formals) body)
      {decClock shifted with locals := sptFromAList (formals.zip vals)} = (some outValue,bodyPost) := by
      rw [entryEq]; exact optRun
    let callFinal : LoopSemStateFiniteExact width σ :=
      match ret,r with
      | some _, .exception _ => {bodyPost with locals := .ln}
      | _,_ => bodyPost
    have targetCall : evaluate (compileHOLExact ctxt live (.call (ret.map (fun ns => (ns,none))) name args))
        {target with clock := target.clock+(extra+bodyExtra)} = (some outValue,callFinal) := by
      have preShift' : evaluate (loopNestedSeqHOL comp.1) {target with clock := target.clock+(extra+bodyExtra)} =
          (none,{post with clock := post.clock+bodyExtra}) := by
        simpa [comp,Nat.add_assoc] using preShift
      have assignShift' : evaluate (loopNestedSeqHOL (regs.zipWith HolLoopProg.assign comp.2.1))
          {post with clock := post.clock+bodyExtra} = (none,shifted) := by
        simpa [shifted,middle,comp,regs,vals] using assignShift
      cases ret with
      | none =>
        simp only [callFinal]
        have callRun : evaluate (.call none (some (findLabExact ctxt name)) regs none) shifted =
            (some outValue,bodyPost) := by
          rw [evaluate]
          simp only [get',lookup,Option.isSome_none,Bool.false_eq_true,if_false,shiftNonzero]
          rw [show evaluate (ocompileHOLExact (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
            (listToNumSetHOLExact (List.range params.length)) body)
            {decClock shifted with locals := sptFromAList ((List.range params.length).zip vals)} = (some outValue,bodyPost) by
              simpa [calleeCtxt,formals] using bodyRun']
          cases outValue <;> simp_all
        have compiled : compileHOLExact ctxt live (.call none name args) =
          loopNestedSeqHOL (comp.1 ++ (regs.zipWith HolLoopProg.assign comp.2.1) ++
            [.call none (some (findLabExact ctxt name)) regs none]) := by
          simp [compileHOLExact,comp,regs,List.append_assoc]
        change evaluate (compileHOLExact ctxt live (.call none name args)) _ = _
        rw [compiled,List.append_assoc]
        rw [evaluate_nested_seq_append_none comp.1 _ _ _ preShift']
        rw [evaluate_nested_seq_append_none _ _ _ _ assignShift']
        change evaluate (.seq (.call none (some (findLabExact ctxt name)) regs none) .skip) shifted = _
        rw [evaluate_seq,callRun]
      | some names =>
        have namesDistinct := retDistinct names rfl
        let returnNames := rtVars ctxt.vars.lookup names (ctxt.vmax+1)
        have returnDistinct : returnNames.Nodup :=
          allDistinctCtxtLookupAllDistinctExact ctxt names (ctxt.vmax+1) namesDistinct localsRel.1
        have subset' : sptSubsetLive live shifted.locals := by simpa [shifted,middle] using subset
        let cut := decClock {shifted with locals := sptInter shifted.locals live}
        have cutRun : cutRes live (none,shifted) = (none,cut) := by
          rw [cutRes]
          simp only
          rw [cutState_of_subset live shifted subset']
          simp [shiftNonzero,cut,decClock]
        have bodyRun'' : evaluate (ocompileHOLExact calleeCtxt (listToNumSetHOLExact formals) body)
            {cut with locals := sptFromAList (formals.zip vals)} = (some outValue,bodyPost) := by
          simpa [cut,decClock] using bodyRun'
        have callRun : evaluate (.call (some (returnNames,live)) (some (findLabExact ctxt name)) regs
            (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))) shifted = (some outValue,callFinal) := by
          rw [evaluate]
          simp only [get',lookup,returnDistinct,not_true_eq_false,if_false]
          rw [cutRun]
          simp only
          rw [fix_clock_evaluate,bodyRun'']
          cases r with
          | «return» values => simp [CrepSteps.CallNonerrorOutcome] at outcome
          | exception eid =>
            have outId : outValue = .exception (.word eid) := by simpa [resultToLoop] using map.symm
            subst outValue
            simp [callFinal,evaluate,cutRes,setVar,sptLookup_sptInsert,LoopSemStateFiniteExact.callEnv,LoopSemStateFiniteExact.sptFromList]
          | finalFfi event =>
            have outId : outValue = .finalFfi event := by simpa [resultToLoop] using map.symm
            subst outValue
            rfl
          | timeOut =>
            have outId : outValue = .timeOut := by simpa [resultToLoop] using map.symm
            subst outValue
            rfl
          | error => exact (notError rfl).elim
          | «break» n => exact (notBreak n rfl).elim
          | «continue» n => exact (notContinue n rfl).elim
        have compiled : compileHOLExact ctxt live (.call (some (names,none)) name args) =
          loopNestedSeqHOL (comp.1 ++ (regs.zipWith HolLoopProg.assign comp.2.1) ++
            [.call (some (returnNames,live)) (some (findLabExact ctxt name)) regs
              (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))]) := by
          simp [compileHOLExact,comp,regs,returnNames,rtVars,FLOOKUP,Nat.add_assoc,List.append_assoc]
          cases names.mapM ctxt.vars.lookup <;> simp
        change evaluate (compileHOLExact ctxt live (.call (some (names,none)) name args)) _ = _
        rw [compiled,List.append_assoc]
        rw [evaluate_nested_seq_append_none comp.1 _ _ _ preShift']
        rw [evaluate_nested_seq_append_none _ _ _ _ assignShift']
        change evaluate (.seq (.call (some (returnNames,live)) (some (findLabExact ctxt name)) regs
          (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))) .skip) shifted = _
        rw [evaluate_seq,callRun]
    have prefixBound : LoopSteps.structuralWeight (loopNestedSeqHOL comp.1) ≤ factor := by
      have eq := scalarArgumentWeight args shape ctxt ref (ctxt.vmax+1) (ref.vmax+1) live .ln
      change _ = callArgumentsCost ref args at eq
      simp only [callSyntaxCost] at syntaxBound
      dsimp [comp]
      omega
    have bodyCount : CrepSteps.steps body sourceEntry + 1 =
        CrepSteps.steps (.call (ret.map (fun ns => (ns,none))) name args) source := by
      cases ret with
      | none => simpa [sourceEntry,Nat.add_comm] using (CrepSteps.steps_call_tail name args source values params body evaluated found arity distinct nz).symm
      | some ns => simpa [sourceEntry,Nat.add_comm] using (CrepSteps.steps_call_returning ns name args source values params body evaluated found arity distinct (retDistinct ns rfl) nz).symm
    refine ⟨extra+bodyExtra,some outValue,callFinal,targetCall,?_,?_,?_,?_,map.symm,?_,?_⟩
    · cases ret <;> cases r <;> simpa [callFinal,CrepSemHOLState.emptyLocals,crepToLoopStateRelExact] using bodySt
    · cases ret <;> cases r <;> simpa [callFinal,CrepSemHOLState.emptyLocals] using bodyMem
    · cases ret <;> cases r <;> simpa [callFinal,CrepSemHOLState.emptyLocals] using bodyGl
    · cases ret <;> cases r <;> simpa [callFinal,CrepSemHOLState.emptyLocals,calleeCtxt,ctxtFcExact,crepToLoopCodeRelExact] using bodyCode
    · cases r with
      | error => exact (notError rfl).elim
      | «break» n => exact (notBreak n rfl).elim
      | «continue» n => exact (notContinue n rfl).elim
      | «return» _ | exception _ | finalFfi _ | timeOut => trivial
    · nlinarith [bodyCount]

/-- A normally returning ordinary call preserves exact caller relations within the syntax-derived budget. -/
theorem call_returningNormal_sim {width : Nat} [NeZero width] {σ : Type}
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, CompiledScalar e)
    (names : List Nat) (source : CrepSemHOLState width σ) (ctxt ref : CrepToLoopContextExact) (live : NumSet)
    (name : MlString) (factor : Nat) (tableOk : Spt (List Nat × HolLoopProg width) → Prop)
    (normal : (evalCrepSemHOLProgExact source (.call (some (names,none)) name args)).1 = none)
    (syntaxBound : callSyntaxCost ref (.call (some (names,none)) name args) ≤ factor)
    (bodySim : ∀ values params body,
      args.mapM (evalCrepSemHOLExp source) = some values → source.code.lookup name = some (params,body) →
      (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)}).clock < source.clock →
      BodySimulationAt body (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
        (listToNumSetHOLExact (List.range params.length))
        (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)})
        (fun n => factor*(n+1)) tableOk) :
    BodySimulationAt (.call (some (names,none)) name args) ctxt live source (fun n => factor*(n+1)) tableOk := by
  intro sourceFinal result target run nonerror stateRel memRel globalsRel codeRel table localsRel
  rw [run] at normal
  simp only at normal
  subst result
  obtain ⟨values,params,body,evaluated,found,arity,distinct,retDistinct,branch⟩ :=
    CrepSteps.nonerrorCall_reaches_callee (some names) name args source sourceFinal _ run nonerror
  rcases branch with ⟨_,bad,_⟩ | ⟨r,bodyFinal,nz,smaller,bodyRun,notError,notBreak,notContinue,outcome⟩
  · contradiction
  have rReturn : ∃ returned, r = .return returned := by
    cases r <;> simp_all [CrepSteps.CallNonerrorOutcome]
  obtain ⟨returned,rfl⟩ := rReturn
  simp only [CrepSteps.CallNonerrorOutcome] at outcome
  obtain ⟨namesDistinct,retArity,⟨old,oldLookup⟩,_,finalEq⟩ := outcome
  obtain ⟨returnNames,mapped,returnDistinct⟩ :=
    returnRegisters_of_locals ctxt live source.locals target.locals names old oldLookup namesDistinct localsRel
  let comp := compileExpsHOLExact ctxt (ctxt.vmax+1) live args
  let regs := genTemps comp.2.2.1 comp.2.1.length
  let vals := values.map wlabWlocExact
  let formals := List.range params.length
  let calleeCtxt := ctxtFcExact ctxt.target ctxt.funcs params formals
  let sourceEntry := decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)}
  obtain ⟨extra,post,pre,assign,get,subset,st,mem,gl,code,locals,bound⟩ :=
    scalarCall_argumentPrefix args shape source values target ctxt live evaluated stateRel memRel globalsRel codeRel localsRel
  let middle : LoopSemStateFiniteExact width σ := {post with locals := sptAlistInsert regs vals post.locals}
  let entry : LoopSemStateFiniteExact width σ := {decClock post with locals := sptFromAList (formals.zip vals)}
  have ent := call_entry_relations ctxt comp.2.2.2 source post name params body args values st mem gl code locals
    found distinct (by omega) ((optMmapEqSome args _ _).mp evaluated)
  have entState : crepToLoopStateRelExact sourceEntry entry := by simpa [sourceEntry,entry,formals,vals] using ent.1
  have entMem : crepToLoopMemRelHOLExact sourceEntry.memory entry.memory sourceEntry.memaddrs := by simpa [sourceEntry,entry] using ent.2.1
  have entGl : crepToLoopGlobalsRelHOLExact sourceEntry.globals entry.globals := by simpa [sourceEntry,entry] using ent.2.2.1
  have entCode : crepToLoopCodeRelExact calleeCtxt sourceEntry.code entry.code := by simpa [sourceEntry,entry,calleeCtxt,formals,vals] using ent.2.2.2.1
  have entLocals : crepToLoopLocalsRelExact calleeCtxt (listToNumSetHOLExact formals) sourceEntry.locals entry.locals := by simpa [sourceEntry,entry,calleeCtxt,formals,vals] using ent.2.2.2.2
  have entTable : tableOk entry.code := by
    have same := SteppedFlapjack.LoopLiveSteps.evaluate_code _ _ post none pre
    simpa [entry,decClock,same] using table
  obtain ⟨bodyExtra,out,bodyPost,bodyEval,bodySt,bodyMem,bodyGl,bodyCode,outEq,_,bodyBound⟩ :=
    bodySim values params body evaluated found smaller bodyFinal (some (.return returned)) entry bodyRun (by simp)
      entState entMem entGl entCode entTable entLocals
  have outEq' : out = some (.result (returned.map wlabWlocExact)) := by simpa [resultToLoop] using outEq
  subst out
  simp only [resultToLoop] at bodyEval
  have bodyShift := evaluate_add_clock_eq _ _ _ bodyPost 1 bodyEval (by simp)
  have bodyShift' : evaluate (compileHOLExact calleeCtxt (listToNumSetHOLExact formals) body)
      {entry with clock := entry.clock+(bodyExtra+1)} =
        (some (.result (returned.map wlabWlocExact)),{bodyPost with clock := bodyPost.clock+1}) := by
    simpa [Nat.add_assoc] using bodyShift
  have optRun : evaluate (ocompileHOLExact calleeCtxt (listToNumSetHOLExact formals) body)
      {entry with clock := entry.clock+(bodyExtra+1)} =
        (some (.result (returned.map wlabWlocExact)),{bodyPost with clock := bodyPost.clock+1}) := by
    unfold ocompileHOLExact
    apply optimise_correct
    exact ⟨bodyShift',by simp,by simp,by simp,by simp⟩
  let k := bodyExtra+1
  have preShift := evaluate_add_clock_eq _ _ _ post k pre (by simp)
  have assignShift := evaluate_add_clock_eq _ _ _ middle k assign (by simp)
  let shifted : LoopSemStateFiniteExact width σ := {middle with clock := middle.clock+k}
  have get' : getVars regs shifted = some vals := by simpa [shifted,getVars_upd_clock] using get
  have code' : crepToLoopCodeRelExact ctxt source.code shifted.code := by simpa [shifted,middle] using code
  have lookup := call_lookup ctxt source shifted name params body vals code' found (by simp [vals,arity])
  have subset' : sptSubsetLive live shifted.locals := by simpa [shifted,middle] using subset
  have shiftNonzero : shifted.clock ≠ 0 := by dsimp [shifted,middle,k]; have := st.2.2.1; omega
  have entryEq : {decClock shifted with locals := sptFromAList (formals.zip vals)} =
      {entry with clock := entry.clock+k} := by
    simp only [shifted,entry,middle,decClock]
    congr 1
    have := st.2.2.1
    omega
  let cut := decClock {shifted with locals := sptInter shifted.locals live}
  have bodyRun' : evaluate (ocompileHOLExact calleeCtxt (listToNumSetHOLExact formals) body)
    {cut with locals := sptFromAList (formals.zip vals)} =
      (some (.result (returned.map wlabWlocExact)),{bodyPost with clock := bodyPost.clock+1}) := by
    have h : {cut with locals := sptFromAList (formals.zip vals)} = {entry with clock := entry.clock+k} := by
      simpa [cut,decClock] using entryEq
    rw [h]
    simpa [k] using optRun
  have retLength : (returned.map wlabWlocExact).length = returnNames.length := by
    have h := opt_mmap_length_eq names _ returnNames mapped
    simp only [List.length_map]
    omega
  let outPost : LoopSemStateFiniteExact width σ := {bodyPost with clock := bodyPost.clock+1}
  have postNonzero : outPost.clock ≠ 0 := by simp [outPost]
  have loopRun := loopReturning_normal_run shifted outPost (findLabExact ctxt name) regs returnNames live (ctxt.vmax+1)
    (ocompileHOLExact calleeCtxt (listToNumSetHOLExact formals) body) vals (returned.map wlabWlocExact)
    (sptFromAList (formals.zip vals)) get' lookup returnDistinct subset' shiftNonzero (by simpa [cut,outPost] using bodyRun') retLength postNonzero
  let targetFinal := (evaluate (.call (some (returnNames,live)) (some (findLabExact ctxt name)) regs
    (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))) shifted).2
  have callRun : evaluate (.call (some (returnNames,live)) (some (findLabExact ctxt name)) regs
      (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))) shifted = (none,targetFinal) :=
    Prod.ext loopRun.1 rfl
  have targetClock : targetFinal.clock = bodyFinal.clock := by
    have eq := congrArg (fun x => x.2.clock) loopRun.2
    change targetFinal.clock = (bodyPost.clock+1)-1 at eq
    have bodyClock := bodySt.2.2.1
    omega
  have compiled : compileHOLExact ctxt live (.call (some (names,none)) name args) =
    loopNestedSeqHOL (comp.1 ++ (regs.zipWith HolLoopProg.assign comp.2.1) ++
      [.call (some (returnNames,live)) (some (findLabExact ctxt name)) regs
        (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))]) := by
    simp [compileHOLExact,comp,regs,mapped,List.append_assoc]
  have targetRun : evaluate (compileHOLExact ctxt live (.call (some (names,none)) name args))
      {target with clock := target.clock+(extra+k)} = (none,targetFinal) := by
    rw [compiled,List.append_assoc]
    rw [evaluate_nested_seq_append_none comp.1 _ _ _ (by simpa [Nat.add_assoc] using preShift)]
    rw [evaluate_nested_seq_append_none _ _ _ _ (by simpa [shifted,middle,comp,regs,vals] using assignShift)]
    change evaluate (.seq (.call (some (returnNames,live)) (some (findLabExact ctxt name)) regs
      (some (ctxt.vmax+1,.raise (ctxt.vmax+1),.skip,live))) .skip) shifted = _
    rw [evaluate_seq,callRun]
    simp [evaluate]
  have rel := compiler_run_relations (.call (some (names,none)) name args) source sourceFinal none target targetFinal
    ctxt live (extra+k) run (by simp) (by simp [resultToLoop]) stateRel memRel globalsRel codeRel localsRel
    (by simpa [resultToLoop] using targetRun)
  have state : crepToLoopStateRelExact sourceFinal targetFinal := by
    have hclock : targetFinal.clock = sourceFinal.clock := by simpa [finalEq] using targetClock
    simpa [crepToLoopStateRelExact,hclock] using rel.1
  have prefixBound : LoopSteps.structuralWeight (loopNestedSeqHOL comp.1) + 1 ≤ factor := by
    have eq := scalarArgumentWeight args shape ctxt ref (ctxt.vmax+1) (ref.vmax+1) live .ln
    change _ = callArgumentsCost ref args at eq
    simp only [callSyntaxCost] at syntaxBound
    dsimp [comp]
    omega
  have count := CrepSteps.steps_call_returning names name args source values params body evaluated found arity distinct namesDistinct nz
  refine ⟨extra+k,none,targetFinal,targetRun,state,rel.2.1,rel.2.2.1,rel.2.2.2.1,rfl,rel.2.2.2.2,?_⟩
  dsimp [k]
  rw [count]
  dsimp [sourceEntry] at bodyBound
  nlinarith

/-- Every direct ordinary or tail call satisfies the reached-state clock simulation. -/
theorem call_full_sim {width : Nat} [NeZero width] {σ : Type}
    (args : List (CrepExpHOL width)) (shape : ∀ e ∈ args, CompiledScalar e)
    (ret : Option (List Nat)) (source : CrepSemHOLState width σ) (ctxt ref : CrepToLoopContextExact) (live : NumSet)
    (name : MlString) (factor : Nat) (tableOk : Spt (List Nat × HolLoopProg width) → Prop)
    (syntaxBound : callSyntaxCost ref (.call (ret.map (fun ns => (ns,none))) name args) ≤ factor)
    (bodySim : ∀ values params body,
      args.mapM (evalCrepSemHOLExp source) = some values → source.code.lookup name = some (params,body) →
      (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)}).clock < source.clock →
      BodySimulationAt body (ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length))
        (listToNumSetHOLExact (List.range params.length))
        (decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)})
        (fun n => factor*(n+1)) tableOk) :
    BodySimulationAt (.call (ret.map (fun ns => (ns,none))) name args) ctxt live source (fun n => factor*(n+1)) tableOk := by
  cases ret with
  | none => exact call_terminal_sim args shape none source ctxt ref live name factor tableOk syntaxBound (Or.inl rfl) bodySim
  | some names =>
    cases h : (evalCrepSemHOLProgExact source (.call (some (names,none)) name args)).1 with
    | none =>
      exact call_returningNormal_sim args shape names source ctxt ref live name factor tableOk h syntaxBound bodySim
    | some result =>
      apply call_terminal_sim args shape (some names) source ctxt ref live name factor tableOk syntaxBound
      · right
        simp [h]
      · exact bodySim

section WholeTableClock
open SteppedFlapjack.CrepSteps
variable {width : Nat} [NeZero width]

/-- Concrete clock factor from the function table, source clock, and program syntax. -/
def callClockFactor (ref : CrepToLoopContextExact) (rows : List (List Nat × CrepProgHOL width))
    (clock : Nat) (p : CrepProgHOL width) : Nat :=
  3 * (callTableCost ref rows + 3)^(clock+1) * callSyntaxCost ref p

private theorem simAt_mono {σ : Type} (p : CrepProgHOL width) (ctxt : CrepToLoopContextExact) (live : NumSet)
    (source : CrepSemHOLState width σ) (tableOk : Spt (List Nat × HolLoopProg width) → Prop) (a b : Nat)
    (ab : a ≤ b) (sim : BodySimulationAt p ctxt live source (fun n => a*(n+1)) tableOk) :
    BodySimulationAt p ctxt live source (fun n => b*(n+1)) tableOk := by
  intro sourceFinal result target run nonerror sr mr gr cr tb lr
  obtain ⟨extra,out,post,ev,hs,hm,hg,hcode,hr,hl,bound⟩ :=
    sim sourceFinal result target run nonerror sr mr gr cr tb lr
  exact ⟨extra,out,post,ev,hs,hm,hg,hcode,hr,hl,bound.trans (Nat.mul_le_mul_right _ ab)⟩

private theorem cost_pos (ref : CrepToLoopContextExact) (p : CrepProgHOL width) : 1 ≤ callSyntaxCost ref p := by
  cases p <;> simp only [callSyntaxCost] <;> omega

private theorem factor_mono (ref : CrepToLoopContextExact) (rows : List (List Nat × CrepProgHOL width))
    (p : CrepProgHOL width) (a b : Nat) (h : a ≤ b) : callClockFactor ref rows a p ≤ callClockFactor ref rows b p := by
  unfold callClockFactor
  have scale := Nat.pow_le_pow_right (n := callTableCost ref rows+3) (by omega) (show a+1 ≤ b+1 by omega)
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ scale)

private theorem factor_call (ref : CrepToLoopContextExact) (rows : List (List Nat × CrepProgHOL width))
    (callee caller : CrepProgHOL width) (params : List Nat) (member : (params,callee) ∈ rows)
    (a b : Nat) (h : a < b) : callClockFactor ref rows a callee ≤ callClockFactor ref rows b caller := by
  let T := callTableCost ref rows
  let K := T+3
  have hcost : callSyntaxCost ref callee ≤ T := callSyntaxCost_le_table ref rows params callee member
  have callerPos : 1 ≤ callSyntaxCost ref caller := cost_pos ref caller
  have scale : K^(a+1) ≤ K^b := Nat.pow_le_pow_right (by dsimp [K]; omega) (by omega)
  have step : K^(a+1) * callSyntaxCost ref callee ≤ K^(b+1) := by
    calc
      K^(a+1) * callSyntaxCost ref callee ≤ K^b * K := Nat.mul_le_mul scale (by dsimp [K]; omega)
      _ = K^(b+1) := by rw [Nat.pow_succ]
  have step' : K^(b+1) ≤ K^(b+1) * callSyntaxCost ref caller := by
    simpa using Nat.mul_le_mul_left (K^(b+1)) callerPos
  dsimp [callClockFactor]
  change 3 * K^(a+1) * callSyntaxCost ref callee ≤ 3 * K^(b+1) * callSyntaxCost ref caller
  nlinarith [step,step']

set_option maxHeartbeats 4000000 in
/-- Whole-table call-aware simulation with a program- and configuration-derived factor. -/
theorem callWholeClock {σ : Type}
    (ref : CrepToLoopContextExact) (rows : List (List Nat × CrepProgHOL width))
    (tableOk : Spt (List Nat × HolLoopProg width) → Prop)
    (p : CrepProgHOL width) (source : CrepSemHOLState width σ)
    (shape : CallScalarProgram p) (table : CallScalarTable source.code)
    (cover : ∀ name params body, source.code.lookup name = some (params,body) → (params,body) ∈ rows) :
    ∀ ctxt live, BodySimulationAt p ctxt live source (fun n => callClockFactor ref rows source.clock p*(n+1)) tableOk := by
  have key : ∀ (x : Nat × Nat) (p : CrepProgHOL width) (source : CrepSemHOLState width σ),
      (source.clock,sizeOf p) = x → CallScalarProgram p → CallScalarTable source.code →
      (∀ name params body, source.code.lookup name = some (params,body) → (params,body) ∈ rows) →
      ∀ ctxt live, BodySimulationAt p ctxt live source (fun n => callClockFactor ref rows source.clock p*(n+1)) tableOk := by
    intro x
    induction x using (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf.induction with
    | h x ih0 =>
      intro p source hx shape table cover ctxt live
      have ih : ∀ (q : CrepProgHOL width) (entry : CrepSemHOLState width σ),
          Prod.Lex (· < ·) (· < ·) (entry.clock,sizeOf q) (source.clock,sizeOf p) →
          CallScalarProgram q → entry.code = source.code → ∀ cc ll,
          BodySimulationAt q cc ll entry (fun n => callClockFactor ref rows entry.clock q*(n+1)) tableOk := by
        intro q entry smaller qshape same cc ll
        have table' : CallScalarTable entry.code := by rw [same]; exact table
        have cover' : ∀ name params body, entry.code.lookup name = some (params,body) → (params,body) ∈ rows := by
          intro name params body found
          apply cover name params body
          simpa [same] using found
        exact ih0 _ (hx ▸ smaller) q entry rfl qshape table' cover' cc ll
      clear ih0 hx
      cases shape with
      | base h =>
        have sim := BodySimulation.at p ctxt live _ source tableOk (scalarProgram_clock h ctxt live)
        apply simAt_mono p ctxt live source tableOk _ _ ?_ sim
        have weight := callScalar_syntaxCost (CallScalarProgram.base h) ref ctxt live
        have scale : 1 ≤ (callTableCost ref rows + 3)^(source.clock+1) := by
          exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.pow_pos (by omega)))
        dsimp [callClockFactor]
        nlinarith
      | @dec name e body he hb =>
        let bf := callClockFactor ref rows source.clock body
        let tmp := (compileExpHOLExact ctxt (ctxt.vmax+1) live e).2.2.1
        let bc := {ctxt with vars := ctxt.vars.updateEq (name,tmp), vmax := tmp}
        let bl := sptInsert tmp () live
        have child : ∀ value, evalCrepSemHOLExp source e = some value →
            BodySimulationAt body bc bl (CrepSemHOLState.setVar name value source) (fun n => bf*(n+1)) tableOk := by
          intro value _
          have smaller : Prod.Lex (· < ·) (· < ·)
              ((CrepSemHOLState.setVar name value source).clock,sizeOf body)
              (source.clock,sizeOf (.dec name e body : CrepProgHOL width)) := by
            apply Prod.Lex.right
            simp_wf
          simpa [bf,CrepSemHOLState.setVar] using ih body (CrepSemHOLState.setVar name value source)
            smaller hb (by rfl) bc bl
        have sim := scalarDecl_clock name e he body ctxt live source tableOk bf child
        apply simAt_mono _ ctxt live source tableOk _ _ ?_ sim
        have eq := scalarExpressionWeight he ctxt ref (ctxt.vmax+1) (ref.vmax+1) live .ln
        change _ = callExpressionCost ref e at eq
        rw [eq]
        have scale : 1 ≤ (callTableCost ref rows+3)^(source.clock+1) := by
          exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.pow_pos (by omega)))
        dsimp [bf,callClockFactor,callSyntaxCost]
        nlinarith
      | @seq a b ha hb =>
        let af := callClockFactor ref rows source.clock a
        let bf := callClockFactor ref rows source.clock b
        have first := ih a source (Prod.Lex.right _ (by simp_wf; omega)) ha rfl ctxt live
        have second : ∀ middle, evalCrepSemHOLProgExact source a = (none,middle) →
            BodySimulationAt b ctxt live middle (fun n => bf*(n+1)) tableOk := by
          intro middle run
          have clock := evalCrepSemHOLProgExact_clock_le source a
          rw [run] at clock
          have same := evaluateCodeInvariantHOL a source none middle run
          have smaller : Prod.Lex (· < ·) (· < ·) (middle.clock,sizeOf b)
              (source.clock,sizeOf (.seq a b : CrepProgHOL width)) := by
            by_cases eq : middle.clock = source.clock
            · rw [eq]; apply Prod.Lex.right; simp_wf
            · apply Prod.Lex.left; simp only at clock; omega
          have child := ih b middle smaller hb same ctxt live
          apply simAt_mono b ctxt live middle tableOk _ _ ?_ child
          exact factor_mono ref rows b middle.clock source.clock (by simpa using clock)
        have sim := sequence_clock_at a b ctxt live source af bf tableOk (by simpa [af] using first) second
        apply simAt_mono _ ctxt live source tableOk _ _ ?_ sim
        dsimp [af,bf,callClockFactor,callSyntaxCost]
        simp only [Nat.mul_add,Nat.mul_one]
        omega
      | @ite e a b he ha hb =>
        let af := callClockFactor ref rows source.clock a
        let bf := callClockFactor ref rows source.clock b
        have left := ih a source (Prod.Lex.right _ (by simp_wf; omega)) ha rfl ctxt live
        have right := ih b source (Prod.Lex.right _ (by simp_wf)) hb rfl ctxt live
        have sim := scalarIte_clock e he a b ctxt live source tableOk af bf (by simpa [af] using left) (by simpa [bf] using right)
        apply simAt_mono _ ctxt live source tableOk _ _ ?_ sim
        have eq := scalarExpressionWeight he ctxt ref (ctxt.vmax+1) (ref.vmax+1) live .ln
        change _ = callExpressionCost ref e at eq
        rw [eq]
        have maxBound : max af bf ≤ af+bf := max_le (by omega) (by omega)
        have scale : 1 ≤ (callTableCost ref rows+3)^(source.clock+1) := by
          exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.pow_pos (by omega)))
        dsimp [af,bf,callClockFactor,callSyntaxCost] at maxBound ⊢
        simp only [Nat.mul_add]
        nlinarith
      | @loop e body he hb =>
        let bf := callClockFactor ref rows source.clock body
        have child : ∀ entry : CrepSemHOLState width σ, entry.clock < source.clock → entry.code = source.code →
            BodySimulationAt body ctxt live entry (fun n => bf*(n+1)) tableOk := by
          intro entry smaller same
          have sim := ih body entry (Prod.Lex.left _ _ smaller) hb same ctxt live
          apply simAt_mono body ctxt live entry tableOk _ _ ?_ sim
          exact factor_mono ref rows body entry.clock source.clock (Nat.le_of_lt smaller)
        intro sourceFinal result target run nonerror stateRel memRel globalsRel codeRel tableGood localsRel
        obtain ⟨extra,post,bound,ev,hs,hm,hg,hcode,hl⟩ :=
          branchConditionWhile_bounded_clock e he body bf source sourceFinal result target ctxt live tableOk child tableGood
            run nonerror stateRel memRel globalsRel codeRel localsRel
        refine ⟨extra,resultToLoop result,post,ev,hs,hm,hg,hcode,rfl,hl,?_⟩
        apply bound.trans
        apply Nat.mul_le_mul_right
        have eq := scalarExpressionWeight he ctxt ref (ctxt.vmax+1) (ref.vmax+1) live .ln
        change _ = callExpressionCost ref e at eq
        rw [eq]
        have scale : 1 ≤ (callTableCost ref rows+3)^(source.clock+1) := by
          exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.pow_pos (by omega)))
        dsimp [bf,callClockFactor,callSyntaxCost]
        nlinarith
      | call ret name args argsShape =>
        apply call_full_sim args argsShape ret source ctxt ref live name _ tableOk ?_ ?_
        · have pos := cost_pos ref (.call (ret.map (fun ns => (ns,none))) name args)
          have scale : 1 ≤ (callTableCost ref rows+3)^(source.clock+1) := by
            exact Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Nat.pow_pos (by omega)))
          dsimp [callClockFactor]
          nlinarith
        · intro values params body evaluated found smaller
          let entry := decClockCrepSemHOL {source with locals := HolFiniteMapExact.empty.updateList (params.zip values)}
          have entryCode : entry.code = source.code := by rfl
          have bodyShape := table name params body found
          let cc := ctxtFcExact ctxt.target ctxt.funcs params (List.range params.length)
          let ll := listToNumSetHOLExact (List.range params.length)
          have sim := ih body entry (Prod.Lex.left _ _ smaller) bodyShape entryCode cc ll
          apply simAt_mono body cc ll entry tableOk _ _ ?_ sim
          exact factor_call ref rows body (.call (ret.map (fun ns => (ns,none))) name args) params
            (cover name params body found) entry.clock source.clock smaller
  exact key _ p source rfl shape table cover

/-- A completed source run is simulated at the concrete whole-table clock bound. -/
theorem callWholeClock_explicit {width : Nat} [NeZero width] {σ : Type}
    (ref ctxt : CrepToLoopContextExact) (live : NumSet)
    (rows : List (List Nat × CrepProgHOL width)) (tableOk : Spt (List Nat × HolLoopProg width) → Prop)
    (p : CrepProgHOL width) (source sourceFinal : CrepSemHOLState width σ)
    (result : Option (CrepResultHOLExact width)) (target : LoopSemStateFiniteExact width σ)
    (shape : CallScalarProgram p) (table : CallScalarTable source.code)
    (cover : ∀ name params body, source.code.lookup name = some (params,body) → (params,body) ∈ rows)
    (run : evalCrepSemHOLProgExact source p = (result,sourceFinal))
    (nonerror : result ≠ some .error) (nonTimeout : result ≠ some .timeOut)
    (stateRel : crepToLoopStateRelExact source target)
    (memRel : crepToLoopMemRelHOLExact source.memory target.memory source.memaddrs)
    (globalsRel : crepToLoopGlobalsRelHOLExact source.globals target.globals)
    (codeRel : crepToLoopCodeRelExact ctxt source.code target.code)
    (tableGood : tableOk target.code)
    (localsRel : crepToLoopLocalsRelExact ctxt live source.locals target.locals) :
    ∃ post, evaluate (compileHOLExact ctxt live p)
      {target with clock := target.clock + callClockFactor ref rows source.clock p * (CrepSteps.steps p source+1)} =
        (resultToLoop result,post) ∧
      crepToLoopStateRelExact sourceFinal {post with clock := sourceFinal.clock} ∧
      crepToLoopMemRelHOLExact sourceFinal.memory post.memory sourceFinal.memaddrs ∧
      crepToLoopGlobalsRelHOLExact sourceFinal.globals post.globals ∧
      crepToLoopCodeRelExact ctxt sourceFinal.code post.code ∧
      localsResultRel ctxt live result sourceFinal post := by
  have mappedNotTimeout : resultToLoop result ≠ some .timeOut := by
    cases result with
    | none => simp [resultToLoop]
    | some r => cases r <;> simp_all [resultToLoop]
  apply BodySimulationAt.explicit p ctxt live source sourceFinal result target
    (fun n => callClockFactor ref rows source.clock p*(n+1))
    (callClockFactor ref rows source.clock p * (CrepSteps.steps p source+1)) tableOk
    (callWholeClock ref rows tableOk p source shape table cover ctxt live) run nonerror mappedNotTimeout
    stateRel memRel globalsRel codeRel tableGood (by rfl) localsRel

end WholeTableClock

end SteppedFlapjack.CrepToLoopSteps
