import SteppedFlapjack.Concrete.Phase7Compiler
import Flapjack.Pancake.Semantics.PanSem.ClockTimeout
import Flapjack.Pancake.PanLang

/-! Finite source clock monotonicity for observational semantics. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Increasing the source clock after a non-timeout run preserves its result
and all fields other than the remaining clock. -/
theorem source_add_clock {width : Nat} {σ : Type} [NeZero width]
    (p : ProgHOL width) (s t : PanSemStateFiniteExact width σ)
    (q : Option (PanSemResultExact width)) (extra : Nat)
    (run : evaluateHOLFiniteState s p = (q,t)) (notTimeout : q ≠ some .timeOut) :
    evaluateHOLFiniteState {s with clock := s.clock + extra} p = (q,{t with clock := t.clock + extra}) := by
  classical
  let hm : DecidablePred s.memaddrs := fun a => Classical.propDecidable (s.memaddrs a)
  let hs : DecidablePred s.shMemaddrs := fun a => Classical.propDecidable (s.shMemaddrs a)
  let low : FiniteEvalContext width σ := ⟨s,hm,hs⟩
  let high : FiniteEvalContext width σ := ⟨{s with clock := s.clock + extra},hm,hs⟩
  obtain ⟨x,hx⟩ := evalPanSemRecursiveCallFiniteContext_total p low
  obtain ⟨y,hy⟩ := evalPanSemRecursiveCallFiniteContext_total p high
  have heval : evaluateHOLFiniteStateWithDeciders s p (h := hm) (hshared := hs) = (q,t) := by
    rw [← evaluateHOLFiniteState_eq_withDeciders (state := s) (hmem := hm) (hshared := hs) (program := p)]
    exact run
  simp only [evaluateHOLFiniteStateWithDeciders,low,hx] at heval
  have xq : x.1 = q := congrArg Prod.fst heval
  have xt : x.2.state = t := congrArg Prod.snd heval
  have hlow : evalPanSemRecursiveCallContextHOLExact p low.toExact = some (x.1,x.2.toExact) := by
    have h := evalPanSemRecursiveCallFiniteContext_projection p low
    simp only [hx,Option.map_some] at h
    exact h.symm
  have hhigh : evalPanSemRecursiveCallContextHOLExact p high.toExact = some (y.1,y.2.toExact) := by
    have h := evalPanSemRecursiveCallFiniteContext_projection p high
    simp only [hy,Option.map_some] at h
    exact h.symm
  have stateEq : (ctxAddClock low.toExact extra).state = high.toExact.state := rfl
  have hhigh' : evalPanSemRecursiveCallContextHOLExact p (ctxAddClock low.toExact extra) = some (y.1,y.2.toExact) :=
    (eval_context_state p (ctxAddClock low.toExact extra) high.toExact stateEq).trans hhigh
  have mono := (eval_add_clock_mono_aux p low.toExact extra _ _ hlow hhigh').2 (by simpa [xq] using notTimeout)
  have yq : y.1 = q := ((Prod.mk.inj mono).1).trans xq
  have ystate : y.2.state = {t with clock := t.clock + extra} := by
    apply PanSemStateFiniteExact.toExact_injective
    have h := congrArg PanSemExactEvalContext.state (Prod.mk.inj mono).2
    change y.2.state.toExact = stateAddClock x.2.state.toExact extra at h
    rw [xt] at h
    exact h
  rw [evaluateHOLFiniteState_eq_withDeciders (state := {s with clock := s.clock + extra})
    (hmem := hm) (hshared := hs) (program := p)]
  simp only [evaluateHOLFiniteStateWithDeciders, high, hy, yq, ystate]
/-- A successful clocked source entry determines its unclocked observation. -/
theorem source_semantics_of_return {width : Nat} {σ : Type} [NeZero width]
    (s t : PanSemStateFiniteExact width σ) (start : MlS) (clock : Nat) (value : ValueHOL width)
    (run : evaluateHOLFiniteState {s with clock := clock} (.call none start []) = (some (.returned value),t)) :
    semantics s start = .terminate .success t.ffi.ioEvents := by
  classical
  let entry : ProgHOL width := .call none start []
  have compare (k : Nat) :
      let r := evaluateHOLFiniteState {s with clock := k} entry
      r.1 = some .timeOut ∨ (r.1 = some (.returned value) ∧ r.2.ffi.ioEvents = t.ffi.ioEvents) := by
    let out := evaluateHOLFiniteState {s with clock := k} entry
    by_cases smaller : k ≤ clock
    · by_cases timeout : out.1 = some .timeOut
      · exact Or.inl timeout
      · have low : evaluateHOLFiniteState {s with clock := k} entry = (out.1,out.2) := Prod.mk.eta.symm
        have high := source_add_clock entry {s with clock := k} out.2 out.1 (clock-k) low timeout
        have high' : evaluateHOLFiniteState {s with clock := clock} entry =
            (out.1,{out.2 with clock := out.2.clock + (clock-k)}) := by
          simpa only [show k + (clock-k) = clock by omega] using high
        have eq := high'.symm.trans run
        have res : out.1 = some (.returned value) := (Prod.mk.inj eq).1
        have events : out.2.ffi.ioEvents = t.ffi.ioEvents := by
          have st := (Prod.mk.inj eq).2
          simpa only using congrArg (fun state : PanSemStateFiniteExact width σ => state.ffi.ioEvents) st
        exact Or.inr ⟨res,events⟩
    · have high := source_add_clock entry {s with clock := clock} t (some (.returned value)) (k-clock) run (by simp)
      have high' : evaluateHOLFiniteState {s with clock := k} entry =
          (some (.returned value),{t with clock := t.clock + (k-clock)}) := by
        simpa only [show clock + (k-clock) = k by omega] using high
      exact Or.inr ⟨congrArg Prod.fst high',congrArg (fun x => x.2.ffi.ioEvents) high'⟩
  have noFail : ¬ ∃ k, (match (evaluateHOLFiniteState {s with clock := k} entry).1 with
      | some .timeOut => False | some (.finalFfi _) => False | some (.returned _) => False | _ => True) := by
    intro ⟨k,bad⟩
    rcases compare k with timed | ⟨returned,_⟩
    · simp [timed] at bad
    · simp [returned] at bad
  have chosen : holOptionSome (fun res => ∃ k st r outcome,
      evaluateHOLFiniteState {s with clock := k} entry = (r,st) ∧
      (match r with | some (.finalFfi e) => outcome = HolOutcome.ffiOutcome e
                    | some (.returned _) => outcome = HolOutcome.success | _ => False) ∧
      res = HolBehaviour.terminate outcome st.ffi.ioEvents) = some (.terminate .success t.ffi.ioEvents) := by
    apply HolLList.holOptionSome_eq_some
    · exact ⟨clock,t,some (.returned value),.success,run,rfl,rfl⟩
    · intro result h
      obtain ⟨k,st,r,outcome,hr,hout,heq⟩ := h
      rw [heq]
      rcases compare k with timed | ⟨returned,events⟩
      · rw [hr] at timed
        simp at timed
        subst r
        simp at hout
      · rw [hr] at returned events
        simp only at returned events
        subst r
        simp only at hout
        subst outcome
        simpa using congrArg (HolBehaviour.terminate .success) events
  dsimp only [entry] at chosen
  unfold semantics
  change (if (∃ k, (match (evaluateHOLFiniteState {s with clock := k} entry).1 with
      | some .timeOut => False | some (.finalFfi _) => False | some (.returned _) => False | _ => True))
    then HolBehaviour.fail else _) = _
  rw [if_neg noFail]
  change (match holOptionSome (fun res => ∃ k st r outcome,
      evaluateHOLFiniteState {s with clock := k} (.call none start []) = (r,st) ∧
      (match r with | some (.finalFfi e) => outcome = HolOutcome.ffiOutcome e
                    | some (.returned _) => outcome = HolOutcome.success | _ => False) ∧
      res = HolBehaviour.terminate outcome st.ffi.ioEvents) with
    | some res => res | none => _) = _
  rw [chosen]
open Classical in
/-- Successful declaration initialization determines the observational
semantics for an arbitrary source function table. Both initialization checks
are executable on concrete declarations. -/
theorem source_declarations_semantics {width : Nat} {σ : Type} [NeZero width]
    (state declared : PanSemStateFiniteExact width σ)
    (start : MlS) (decls : List (DeclHOL width)) (structs : StructContextExact)
    (names : decsStcnamesHOLExact [] decls = some structs)
    (initialized : evaluateDeclsHOLFinite {state with structs := structs} decls = some declared) :
    semanticsDecls state start decls = semantics declared start := by
  unfold semanticsDecls
  rw [names]
  simp only
  rw [initialized]

open Classical in
/-- Initializing a function-only declaration table installs its functions in
source order. The only check is the compiler's concrete shape check. -/
theorem source_function_declarations_init {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (functions : List (FunDeclHOL width))
    (wellFormed : functions.all (fun f =>
      f.params.all (fun p => isWfShapeExactHOL state.structs p.2) &&
        isWfShapeExactHOL state.structs f.returnShape) = true) :
    evaluateDeclsHOLFinite state (functions.map DeclHOL.function) =
      some {state with code := functions.foldl (fun code f =>
        code.update (f.name,(f.params,f.body,f.returnShape))) state.code} := by
  induction functions generalizing state with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.all_cons,Bool.and_eq_true] at wellFormed
    simp only [List.map_cons,evaluateDeclsHOLFinite,wellFormed.1,List.foldl_cons]
    exact ih _ wellFormed.2

private theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) (v : β) (h : List.lookup k l = some v) : (k,v) ∈ l := by
  induction l with
  | nil => simp at h
  | cons e l ih =>
    obtain ⟨a,b⟩ := e
    by_cases hk : k = a
    · subst hk; simp at h; subst h; simp
    · have he : (k == a) = false := by simp [hk]
      simp only [List.lookup_cons,he] at h
      exact List.mem_cons_of_mem _ (ih h)
private theorem lookup_reverse_nodup {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) (hnd : (l.map Prod.fst).Nodup) :
    List.lookup k l.reverse = List.lookup k l := by
  have hnd' : (l.reverse.map Prod.fst).Nodup := by
    rw [List.map_reverse, List.Nodup, List.pairwise_reverse]
    exact hnd.imp (fun h => Ne.symm h)
  cases h : List.lookup k l with
  | none =>
    cases h' : List.lookup k l.reverse with
    | none => rfl
    | some v =>
      have hm := lookup_mem _ _ _ h'
      have eq := Flapjack.list_lookup_of_mem_of_nodup hnd (List.mem_reverse.mp hm)
      rw [h] at eq; cases eq
  | some v =>
    exact Flapjack.list_lookup_of_mem_of_nodup hnd' (List.mem_reverse.mpr (lookup_mem _ _ _ h))
theorem updateList_reverse_nodup {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (hnd : (l.map Prod.fst).Nodup) :
    (HolFiniteMapExact.empty.updateList l) = (HolFiniteMapExact.empty.updateList l.reverse) := by
  apply HolFiniteMapExact.ext
  funext k
  simp only [HolFiniteMapExact.lookup_updateList]
  change FUPDATE_LIST FEMPTY l k = FUPDATE_LIST FEMPTY l.reverse k
  have h₁ := FLOOKUP_FUPDATE_LIST_reverse_eq_lookup l.reverse k
  have h₂ := FLOOKUP_FUPDATE_LIST_reverse_eq_lookup l k
  simp only [List.reverse_reverse,FLOOKUP] at h₁ h₂
  rw [h₁,h₂,lookup_reverse_nodup l k hnd]

theorem function_fold_code {width : Nat} [NeZero width] (functions : List (FunDeclHOL width))
    (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) :
    functions.foldl (fun code f => code.update (f.name,(f.params,f.body,f.returnShape))) code =
      code.updateList (functionsHOL (functions.map DeclHOL.function)) := by
  induction functions generalizing code with
  | nil =>
    apply HolFiniteMapExact.ext
    funext key
    rfl
  | cons f fs ih =>
    simp only [List.foldl_cons,List.map_cons,functionsHOL,ih]
    apply HolFiniteMapExact.ext
    funext key
    simp only [HolFiniteMapExact.lookup_updateList,FUPDATE_LIST_cons]
    rfl

open Classical in
/-- Function-only declarations have the semantics of their initialized code
table, with the shape check calculated directly from the declarations. -/
theorem source_function_declarations_semantics {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (start : MlS) (functions : List (FunDeclHOL width))
    (wellFormed : functions.all (fun f =>
      f.params.all (fun p => isWfShapeExactHOL ([] : StructContextExact) p.2) &&
        isWfShapeExactHOL ([] : StructContextExact) f.returnShape) = true) :
    semanticsDecls state start (functions.map DeclHOL.function) =
      semantics {state with structs := [], code :=
        state.code.updateList (functionsHOL (functions.map DeclHOL.function))} start := by
  have names : decsStcnamesHOLExact [] (functions.map DeclHOL.function) = some [] := by
    clear wellFormed
    induction functions with
    | nil => rfl
    | cons f fs ih => simpa [decsStcnamesHOLExact] using ih
  have init := source_function_declarations_init {state with structs := []} functions wellFormed
  simpa only [function_fold_code] using source_declarations_semantics state _ start _ [] names init

open Classical in
/-- With distinct function names, the initialized source code is exactly the
reversed association-list table used by the call-aware frontend. -/
theorem source_function_declarations_compiler_code {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) (functions : List (FunDeclHOL width))
    (emptyCode : state.code = HolFiniteMapExact.empty)
    (wellFormed : functions.all (fun f =>
      f.params.all (fun p => isWfShapeExactHOL state.structs p.2) &&
        isWfShapeExactHOL state.structs f.returnShape) = true)
    (unique : ((functionsHOL (functions.map DeclHOL.function)).map Prod.fst).Nodup) :
    evaluateDeclsHOLFinite state (functions.map DeclHOL.function) = some
      {state with code := (HolFiniteMapExact.empty.updateList
        (functionsHOL (functions.map DeclHOL.function)).reverse)} := by
  have init := source_function_declarations_init state functions wellFormed
  rw [function_fold_code,emptyCode,updateList_reverse_nodup _ unique] at init
  exact init

end SteppedFlapjack.Concrete
