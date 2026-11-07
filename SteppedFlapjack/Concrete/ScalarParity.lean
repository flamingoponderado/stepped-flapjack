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
    (locals : ScalarLocalsRel scope ctxt source target) :
    ∃ compiled, compileExpExactHOLW ctxt (expToHOL expression) = ([compiled],.one) ∧
      @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a)) (expToHOL expression) =
        Option.map ValueHOL.val (evalCrepSemHOLExp target compiled) := by
  induction scalar with
  | const value => exact ⟨.const value,by simp [expToHOL,compileExpExactHOLW],by simp [expToHOL,evalHOLExact,evalCrepSemHOLExp]⟩
  | «local» name member =>
    obtain ⟨reg,found,values⟩ := locals name member
    refine ⟨.var reg,by simp [expToHOL,compileExpExactHOLW,found],?_⟩
    simpa [expToHOL,evalHOLExact,evalCrepSemHOLExp,lookupKvarHOLExact] using values
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
    (failed : @evalHOLExact 64 σ _ source.toExact (fun a => Classical.propDecidable (source.memaddrs a))
      (expToHOL expression) = none) :
    ∃ compiled, compileExpExactHOLW ctxt (expToHOL expression) = ([compiled],.one) ∧
      evalCrepSemHOLExp target compiled = none := by
  obtain ⟨compiled,compiledEq,evalEq⟩ := scalar_compile_eval_all scalar ctxt source target locals
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

example {σ : Type} (ctxt : PanToCrepContextExact 64) (source : PanSemStateFiniteExact 64 σ)
    (target : CrepSemHOLState 64 σ) :
    ∃ compiled, compileExpExactHOLW ctxt (expToHOL (.shift .lsl (.const 1) (.const 64) : Exp (RiscV.Word 64))) =
      ([compiled],.one) ∧ evalCrepSemHOLExp target compiled = none := by
  apply scalar_compile_error (scope := []) (.shift .lsl (.const _) (.const _)) ctxt source target
  · intro name member
    simp at member
  · simp [expToHOL,evalHOLExact,wordShiftHOL]
end SteppedFlapjack.Concrete
