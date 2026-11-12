import SteppedFlapjack.Concrete.FrontendShape
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString SteppedFlapjack.PanToCrepSteps

/-- Local variables agree in both directions, including absent bindings. -/
def ScalarLocalsRel {σ : Type} (scope : List VarName) (ctxt : PanToCrepContextExact 64)
    (source : PanSemStateFiniteExact 64 σ) (target : CrepSemHOLState 64 σ) : Prop :=
  ∀ name ∈ scope, ∃ reg, ctxt.vars.lookup (ofString name) = some (.one,[reg]) ∧
    source.locals.lookup (ofString name) = Option.map ValueHOL.val (target.locals.lookup reg)

/-- A supported scalar compiles to one expression whose result agrees even when evaluation fails. -/
theorem scalar_compile_eval_all {σ : Type} {scope : List VarName} {expression : Exp (RiscV.Word 64)}
    (scalar : Scalar scope expression) (ctxt : PanToCrepContextExact 64)
    (source : PanSemStateFiniteExact 64 σ) (target : CrepSemHOLState 64 σ)
    (locals : ScalarLocalsRel scope ctxt source target)
    (stateRel : panToCrepStateRelFiniteExact source target) :
    ∃ compiled, compileExpExactHOLW ctxt (expToHOL expression) = ([compiled],.one) ∧
      @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL expression) =
        Option.map ValueHOL.val (evalCrepSemHOLExp target compiled) := by
  induction scalar with
  | const value => exact ⟨.const value,by simp [expToHOL,compileExpExactHOLW],by simp [expToHOL,evalHOLExact,evalCrepSemHOLExp]⟩
  | «local» name member =>
    obtain ⟨reg,found,values⟩ := locals name member
    refine ⟨.var reg,by simp [expToHOL,compileExpExactHOLW,found],?_⟩
    simpa [expToHOL,evalHOLExact,evalCrepSemHOLExp,lookupKvarHOLExact] using values
  | load address ih =>
    obtain ⟨compiled, comp, eval⟩ := ih
    refine ⟨.load compiled, by simp [expToHOL,shapeToHOL,compileExpExactHOLW,comp,sizeOfShapeHOL,loadShapeBytesHOLW], ?_⟩
    simp only [expToHOL,shapeToHOL,evalHOLExact,isWfShapeExactHOL,if_true,evalCrepSemHOLExp]
    rw [eval]
    cases result : evalCrepSemHOLExp target compiled with
    | none => simp
    | some word =>
      cases word with
      | word word =>
        simp only [Option.map_some,memLoadHOLExact,stateRel.1]
        rw [show source.memaddrs word = target.memaddrs word from congrFun stateRel.2.1 word]
        by_cases h : target.memaddrs word <;> simp [h]
  | op operator a b iha ihb =>
    obtain ⟨ca,compa,vala⟩ := iha
    obtain ⟨cb,compb,valb⟩ := ihb
    refine ⟨.op operator [ca,cb],by simp [expToHOL,compileExpExactHOLW,compileExpExactHOLWList,compa,compb,cexpHeads],?_⟩
    simp only [expToHOL,List.map_cons,List.map_nil,evalHOLExact,evalListHOLExact,evalCrepSemHOLExp]
    rw [vala,valb]
    cases ha : evalCrepSemHOLExp target ca <;> cases hb : evalCrepSemHOLExp target cb <;>
      simp [ha,hb,valueIsWord,valueWord,Function.comp_def]
  | cmp operator a b iha ihb =>
    obtain ⟨ca,compa,vala⟩ := iha
    obtain ⟨cb,compb,valb⟩ := ihb
    refine ⟨.cmp operator ca cb,by simp [expToHOL,compileExpExactHOLW,compa,compb],?_⟩
    simp only [expToHOL,evalHOLExact,evalCrepSemHOLExp]
    rw [vala,valb]
    cases ha : evalCrepSemHOLExp target ca <;> cases hb : evalCrepSemHOLExp target cb <;>
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpResultHOL]
  | shift operator a b iha ihb =>
    obtain ⟨ca,compa,vala⟩ := iha
    obtain ⟨cb,compb,valb⟩ := ihb
    refine ⟨.shift operator ca cb,by simp [expToHOL,compileExpExactHOLW,compa,compb],?_⟩
    simp only [expToHOL,evalHOLExact,evalCrepSemHOLExp]
    rw [vala,valb]
    cases ha : evalCrepSemHOLExp target ca <;> cases hb : evalCrepSemHOLExp target cb <;>
      simp [Function.comp_def]
/-- A failed supported source expression compiles to a failed Crep expression. -/
theorem scalar_compile_error {σ : Type} {scope : List VarName} {expression : Exp (RiscV.Word 64)}
    (scalar : Scalar scope expression) (ctxt : PanToCrepContextExact 64)
    (source : PanSemStateFiniteExact 64 σ) (target : CrepSemHOLState 64 σ)
    (locals : ScalarLocalsRel scope ctxt source target)
    (stateRel : panToCrepStateRelFiniteExact source target)
    (failed : @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a))
      (expToHOL expression) = none) :
    ∃ compiled, compileExpExactHOLW ctxt (expToHOL expression) = ([compiled],.one) ∧
      evalCrepSemHOLExp target compiled = none := by
  obtain ⟨compiled,compiledEq,evalEq⟩ := scalar_compile_eval_all scalar ctxt source target locals stateRel
  rw [failed] at evalEq
  refine ⟨compiled,compiledEq,?_⟩
  cases h : evalCrepSemHOLExp target compiled with
  | none => rfl
  | some value => simp [h] at evalEq
/-- The empty source scope satisfies the local relation for any states. -/
theorem ScalarLocalsRel.empty {σ : Type} (ctxt : PanToCrepContextExact 64)
    (source : PanSemStateFiniteExact 64 σ) (target : CrepSemHOLState 64 σ) : ScalarLocalsRel [] ctxt source target := by
  intro name member
  simp at member

/-- A scalar declaration extends the compiler register bound. -/
theorem scalarDeclContext_max {ctxt : PanToCrepContextExact 64} (name : MlString)
    (maxBound : ctxtMaxFiniteExact ctxt.vmax ctxt.vars) :
    ctxtMaxFiniteExact (scalarDeclContext ctxt name).vmax (scalarDeclContext ctxt name).vars := by
  refine ⟨Nat.zero_le _,?_⟩
  intro key shape slots found slot member
  simp only [scalarDeclContext,HolFiniteMapExact.lookup_update,FUPDATE] at found ⊢
  split at found
  · simp only [Option.some.injEq,Prod.mk.injEq] at found
    obtain ⟨_,rfl⟩ := found
    simp only [List.mem_singleton] at member
    omega
  · have oldBound := maxBound.2 key shape slots found slot member
    omega
/-- A scalar declaration preserves disjoint compiler register assignments. -/
theorem scalarDeclContext_disjoint {ctxt : PanToCrepContextExact 64} (name : MlString)
    (maxBound : ctxtMaxFiniteExact ctxt.vmax ctxt.vars) (disjoint : noOverlapFiniteExact ctxt.vars) :
    noOverlapFiniteExact (scalarDeclContext ctxt name).vars := by
  constructor
  · intro key shape slots found
    by_cases same : name = key
    · simp [scalarDeclContext,HolFiniteMapExact.lookup_update,FUPDATE,same] at found
      obtain ⟨_,rfl⟩ := found
      simp
    · have old : ctxt.vars.lookup key = some (shape,slots) := by
        simpa [scalarDeclContext,HolFiniteMapExact.lookup_update,FUPDATE,same] using found
      exact disjoint.1 key shape slots old
  · intro key key' shape shape' slots slots' found found' overlap
    by_cases same : name = key
    · by_cases same' : name = key'
      · exact same.symm.trans same'
      · simp [scalarDeclContext,HolFiniteMapExact.lookup_update,FUPDATE,same] at found
        obtain ⟨_,rfl⟩ := found
        have old' : ctxt.vars.lookup key' = some (shape',slots') := by
          simpa [scalarDeclContext,HolFiniteMapExact.lookup_update,FUPDATE,same'] using found'
        obtain ⟨slot,inNew,inOld⟩ := overlap
        have slotEq : slot = ctxt.vmax+1 := by simpa using inNew
        have oldBound := maxBound.2 key' shape' slots' old' slot inOld
        omega
    · by_cases same' : name = key'
      · simp [scalarDeclContext,HolFiniteMapExact.lookup_update,FUPDATE,same'] at found'
        obtain ⟨_,rfl⟩ := found'
        have old : ctxt.vars.lookup key = some (shape,slots) := by
          simpa [scalarDeclContext,HolFiniteMapExact.lookup_update,FUPDATE,same] using found
        obtain ⟨slot,inOld,inNew⟩ := overlap
        have slotEq : slot = ctxt.vmax+1 := by simpa using inNew
        have oldBound := maxBound.2 key shape slots old slot inOld
        omega
      · have old : ctxt.vars.lookup key = some (shape,slots) := by
          simpa [scalarDeclContext,HolFiniteMapExact.lookup_update,FUPDATE,same] using found
        have old' : ctxt.vars.lookup key' = some (shape',slots') := by
          simpa [scalarDeclContext,HolFiniteMapExact.lookup_update,FUPDATE,same'] using found'
        exact disjoint.2 key key' shape shape' slots slots' old old' overlap

/-- Declaration extends the local relation using a fresh target slot. -/
theorem ScalarLocalsRel.declare {σ : Type} {scope : List VarName} {ctxt : PanToCrepContextExact 64}
    {source : PanSemStateFiniteExact 64 σ} {target : CrepSemHOLState 64 σ}
    (relation : ScalarLocalsRel scope ctxt source target) (maxBound : ctxtMaxFiniteExact ctxt.vmax ctxt.vars)
    (name : VarName) (word : BitVec 64) :
    ScalarLocalsRel (name :: scope) (scalarDeclContext ctxt (ofString name))
      (setVarHOLFinite (ofString name) (.val (.word word)) source)
      {target with locals := target.locals.update (ctxt.vmax+1,.word word)} := by
  intro item member
  simp only [List.mem_cons] at member
  by_cases same : ofString item = ofString name
  · refine ⟨ctxt.vmax+1,?_,?_⟩
    · simpa [same] using scalarDeclContext_local ctxt (ofString name)
    · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,same]
  · rcases member with eq | member
    · subst item; exact False.elim (same rfl)
    · obtain ⟨reg,found,values⟩ := relation item member
      have regBound : reg ≤ ctxt.vmax := maxBound.2 _ _ _ found reg (by simp)
      have fresh : reg ≠ ctxt.vmax+1 := by omega
      have reverse : ofString name ≠ ofString item := Ne.symm same
      have freshReverse : ctxt.vmax+1 ≠ reg := Ne.symm fresh
      refine ⟨reg,?_,?_⟩
      · simpa [scalarDeclContext,HolFiniteMapExact.lookup_update,FUPDATE,reverse] using found
      · simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,reverse,freshReverse] using values
/-- Assignment preserves the local relation when compiler slots do not overlap. -/
theorem ScalarLocalsRel.assign {σ : Type} {scope : List VarName} {ctxt : PanToCrepContextExact 64}
    {source : PanSemStateFiniteExact 64 σ} {target : CrepSemHOLState 64 σ}
    (relation : ScalarLocalsRel scope ctxt source target) (disjoint : noOverlapFiniteExact ctxt.vars)
    (name : VarName) (member : name ∈ scope) (word : BitVec 64) :
    ∃ reg, ctxt.vars.lookup (ofString name) = some (.one,[reg]) ∧
      ScalarLocalsRel scope ctxt (setVarHOLFinite (ofString name) (.val (.word word)) source)
        {target with locals := target.locals.update (reg,.word word)} := by
  obtain ⟨assigned,assignedFound,_⟩ := relation name member
  refine ⟨assigned,assignedFound,?_⟩
  intro item itemMember
  by_cases same : ofString item = ofString name
  · refine ⟨assigned,?_,?_⟩
    · simpa [same] using assignedFound
    · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,same]
  · obtain ⟨reg,found,values⟩ := relation item itemMember
    have distinct : reg ≠ assigned := by
      intro eq
      subst reg
      have equal := disjoint.2 _ _ _ _ _ _ found assignedFound ⟨assigned,by simp,by simp⟩
      exact same equal
    have reverse : ofString name ≠ ofString item := Ne.symm same
    have distinctReverse : assigned ≠ reg := Ne.symm distinct
    refine ⟨reg,found,?_⟩
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,reverse,distinctReverse] using values

/-- Every source name in the current lexical scope holds a word. -/
def ScalarScopePresent {σ : Type} (scope : List VarName) (source : PanSemStateFiniteExact 64 σ) : Prop :=
  ∀ name ∈ scope, ∃ word, source.locals.lookup (ofString name) = some (.val (.word word))

/-- The empty lexical scope is present in every source state. -/
theorem ScalarScopePresent.empty {σ : Type} (source : PanSemStateFiniteExact 64 σ) : ScalarScopePresent [] source := by
  intro name member
  simp at member

/-- A word update preserves the current scope and makes its name present. -/
theorem ScalarScopePresent.setVar {σ : Type} {scope : List VarName} {source : PanSemStateFiniteExact 64 σ}
    (present : ScalarScopePresent scope source) (name : VarName) (word : BitVec 64) :
    ScalarScopePresent (name :: scope) (setVarHOLFinite (ofString name) (.val (.word word)) source) := by
  intro item member
  simp only [List.mem_cons] at member
  by_cases same : ofString name = ofString item
  · refine ⟨word,?_⟩
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,same]
  · rcases member with eq | member
    · subst item
      exact False.elim (same rfl)
    · obtain ⟨old,found⟩ := present item member
      refine ⟨old,?_⟩
      simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,same] using found

/-- Restoring a declaration's saved local preserves the outer scope. -/
theorem ScalarScopePresent.restore {σ : Type} {scope : List VarName}
    (source final : PanSemStateFiniteExact 64 σ) (name : VarName)
    (original : ScalarScopePresent scope source) (inner : ScalarScopePresent (name :: scope) final) :
    ScalarScopePresent scope {final with locals := HolFiniteMapExact.resVarEq final.locals (ofString name,source.locals.lookup (ofString name))} := by
  intro item member
  by_cases same : ofString item = ofString name
  · obtain ⟨word,found⟩ := original item member
    have saved : source.locals.lookup (ofString name) = some (.val (.word word)) := by simpa [same] using found
    refine ⟨word,?_⟩
    simp [same,saved,HolFiniteMapExact.lookup_resVarEq_some,FUPDATE_HOL]
  · obtain ⟨word,found⟩ := inner item (by simp [member])
    refine ⟨word,?_⟩
    cases saved : source.locals.lookup (ofString name) with
    | none =>
      simpa [saved,HolFiniteMapExact.lookup_resVarEq_none,FDOMSUB_HOL,same] using found
    | some value =>
      simpa [saved,HolFiniteMapExact.lookup_resVarEq_some,HolFiniteMapExact.lookup_updateEq,FUPDATE_HOL,same] using found

/-- For present scalar locals, the established compiler relation supplies two-way local agreement. -/
theorem ScalarLocalsRel.of_existing {σ : Type} {scope : List VarName} {ctxt : PanToCrepContextExact 64}
    {source : PanSemStateFiniteExact 64 σ} {target : CrepSemHOLState 64 σ}
    (registered : ScopeRelation scope ctxt) (present : ScalarScopePresent scope source)
    (related : panToCrepLocalsRelFiniteExact ctxt source.locals target.locals) :
    ScalarLocalsRel scope ctxt source target := by
  intro name member
  obtain ⟨reg,found⟩ := registered name member
  obtain ⟨word,sourceFound⟩ := present name member
  obtain ⟨slots,values,slotFound,targetFound,flat,_⟩ := related.2.2 (ofString name) (.val (.word word)) sourceFound
  have eqSlots : slots = [reg] := by
    simp only [shapeOfHOLExact] at slotFound
    rw [found] at slotFound
    exact (Prod.mk.inj (Option.some.inj slotFound)).2.symm
  subst slots
  have valuesEq : values = [.word word] := by simpa [flattenHOL] using flat.symm
  subst values
  have targetValue : target.locals.lookup reg = some (.word word) := by
    cases h : target.locals.lookup reg with
    | none => simp [h,flattenHOL] at targetFound
    | some value =>
      simp [h,flattenHOL] at targetFound
      exact congrArg some targetFound
  refine ⟨reg,found,?_⟩
  simp [sourceFound,targetValue]

example {σ : Type} (ctxt : PanToCrepContextExact 64) (_source : PanSemStateFiniteExact 64 σ)
    (target : CrepSemHOLState 64 σ) :
    ∃ compiled, compileExpExactHOLW ctxt (expToHOL (.shift .lsl (.const 1) (.const 64) : Exp (RiscV.Word 64))) =
      ([compiled],.one) ∧ evalCrepSemHOLExp target compiled = none := by
  refine ⟨.shift .lsl (.const 1) (.const 64), ?_, ?_⟩
  · simp [expToHOL,compileExpExactHOLW]
  · simp [evalCrepSemHOLExp,wordShiftHOL]
/-- A successful scalar expression in a present scope has a word result. -/
theorem scalar_hol_word {σ : Type} {scope : List VarName} {expression : Exp (RiscV.Word 64)}
    (scalar : Scalar scope expression) (source : PanSemStateFiniteExact 64 σ)
    (present : ScalarScopePresent scope source) (value : ValueHOL 64)
    (evaluated : @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a))
      (expToHOL expression) = some value) : ∃ word, value = .val (.word word) := by
  induction scalar generalizing value with
  | const n => simp [expToHOL,evalHOLExact] at evaluated; subst value; exact ⟨n,rfl⟩
  | «local» name member =>
    obtain ⟨word,found⟩ := present name member
    simp [expToHOL,evalHOLExact,found] at evaluated
    subst value
    exact ⟨word,rfl⟩
  | load address ih =>
    simp only [expToHOL,shapeToHOL,evalHOLExact,isWfShapeExactHOL,if_true] at evaluated
    split at evaluated <;> simp_all [memLoadHOLExact]
    all_goals rcases evaluated with ⟨_, rfl⟩
    all_goals cases source.memory _ with | word w => exact ⟨w,rfl⟩
  | op operator a b iha ihb =>
    simp only [expToHOL,List.map_cons,List.map_nil,evalHOLExact] at evaluated
    split at evaluated <;> simp_all
    aesop
  | cmp operator a b iha ihb =>
    simp only [expToHOL,evalHOLExact] at evaluated
    split at evaluated <;> simp_all
    aesop
  | shift operator a b iha ihb =>
    simp only [expToHOL,evalHOLExact] at evaluated
    split at evaluated <;> simp_all
    aesop
end SteppedFlapjack.Concrete
