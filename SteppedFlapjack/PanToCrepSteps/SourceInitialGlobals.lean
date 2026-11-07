import SteppedFlapjack.PanToCrepSteps.ConcreteDeclInitial

/-! Source-first construction of a no-global lowered call entry. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The empty globals context used when the global pass allocates no globals. -/
def emptyGlobalsContext {width : Nat} [NeZero width] : PanGlobalsContextExact width :=
  { globals := HolFiniteMapExact.empty, globalsSize := 0, maxGlobalsSize := 0 }

/-- Form the state immediately before the lowered call from the original
callee state, installing the compiled code and the call's extra clock tick. -/
def noGlobalsLoweredPreCall {width : Nat} {σ : Type} [NeZero width]
    (source : PanSemStateFiniteExact width σ)
    (code : HolFiniteMapExact MlString (List (MlString × ShapeHOL) × ProgHOL width × ShapeHOL)) :
    PanSemStateFiniteExact width σ :=
  { source with code := code, clock := source.clock + 1 }

/-- A source state with no globals and an empty local environment gives a
related lowered call entry, provided the compiled code table has the actual
globals-pass translation of each source function. The only memory-layout
premises are the alignment and top-address exclusion required by the pass. -/
theorem noGlobals_source_callEntry_rel {σ : Type}
    (source : PanSemStateFiniteExact 64 σ)
    (code : HolFiniteMapExact MlString (List (MlString × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (locals : source.locals = HolFiniteMapExact.empty)
    (globals : source.globals = HolFiniteMapExact.empty)
    (structs : source.structs = [])
    (topOutside : ¬ source.memaddrs source.topAddr)
    (aligned : panGlobalsByteAlignedHOL source.topAddr)
    (codeCompiled : ∀ function parameters program returnShape,
      source.code.lookup function = some (parameters,program,returnShape) →
      code.lookup function = some (parameters,compileProgExactHOL emptyGlobalsContext program,returnShape)) :
    panGlobalsStateRelHOLExact true emptyGlobalsContext source
      (callEntryStateHOLFinite (noGlobalsLoweredPreCall source code) HolFiniteMapExact.empty) := by
  simp [panGlobalsStateRelHOLExact,callEntryStateHOLFinite,noGlobalsLoweredPreCall,
    emptyGlobalsContext,locals,globals,structs,disjointGlobalsHOLExact,
    HolFiniteMapExact.lookup_empty,topOutside,aligned]
  exact ⟨codeCompiled,Or.inr rfl⟩


/-- For the concrete no-global program, the lowered table is the table
actually produced by global compilation, not an independently chosen code
relation. The original state is supplied first. -/
theorem concreteDecl_source_callEntry_rel {σ : Type}
    (start : MlString) (name : VarName) (returned : BitVec 64)
    (source : PanSemStateFiniteExact 64 σ)
    (locals : source.locals = HolFiniteMapExact.empty)
    (globals : source.globals = HolFiniteMapExact.empty)
    (structs : source.structs = [])
    (topOutside : ¬ source.memaddrs source.topAddr)
    (aligned : panGlobalsByteAlignedHOL source.topAddr)
    (sourceCode : source.code = HolFiniteMapExact.empty.update
      (newMainNameHOL (concreteDeclProgram start name returned),([],concreteDeclBody name returned,.one))) :
    panGlobalsStateRelHOLExact true (concreteDeclGlobalContext start name returned) source
      (callEntryStateHOLFinite
        (noGlobalsLoweredPreCall source (HolFiniteMapExact.empty.updateList
          (functionsHOL (compileTopExactHOL (concreteDeclProgram start name returned) start)).reverse))
        HolFiniteMapExact.empty) := by
  rw [concreteDeclGlobalContext_empty]
  change panGlobalsStateRelHOLExact true emptyGlobalsContext source _
  apply noGlobals_source_callEntry_rel source _ locals globals structs topOutside aligned
  intro function parameters program returnShape found
  rw [sourceCode] at found
  simp only [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.lookup_empty] at found
  split at found
  · rename_i eq
    simp only [Option.some.injEq,Prod.mk.injEq] at found
    rcases found with ⟨rfl,rfl,rfl⟩
    have same : newMainNameHOL (concreteDeclProgram start name returned) = function := by simpa using eq
    subst function
    have lookup := concreteDecl_lowered_lookup start name returned
      (noGlobalsLoweredPreCall source (HolFiniteMapExact.empty.updateList
        (functionsHOL (compileTopExactHOL (concreteDeclProgram start name returned) start)).reverse)) rfl
    simpa only [noGlobalsLoweredPreCall, ← concreteDeclGlobalContext_empty start name returned,
      (concreteDeclBody_globals_fixed start start _ name returned).2] using lookup
  · simp at found


/-- The source-first concrete pre-call state also executes the empty global
initializer and has the tick needed by the generated call. -/
theorem concreteDecl_source_initialization {σ : Type}
    (start : MlString) (name : VarName) (returned : BitVec 64)
    (source : PanSemStateFiniteExact 64 σ)
    (locals : source.locals = HolFiniteMapExact.empty)
    (globals : source.globals = HolFiniteMapExact.empty)
    (structs : source.structs = [])
    (topOutside : ¬ source.memaddrs source.topAddr)
    (aligned : panGlobalsByteAlignedHOL source.topAddr)
    (sourceCode : source.code = HolFiniteMapExact.empty.update
      (newMainNameHOL (concreteDeclProgram start name returned),([],concreteDeclBody name returned,.one))) :
    let preCall := noGlobalsLoweredPreCall source (HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL (concreteDeclProgram start name returned) start)).reverse)
    preCall.evaluateHOLFiniteState (nestedSeqHOL []) = (none,preCall) ∧
    preCall.clock ≠ 0 ∧
    panGlobalsStateRelHOLExact true (concreteDeclGlobalContext start name returned) source
      (callEntryStateHOLFinite preCall HolFiniteMapExact.empty) := by
  refine ⟨evaluateHOLFiniteState_skip _,?_,?_⟩
  · simp [noGlobalsLoweredPreCall]
  · exact concreteDecl_source_callEntry_rel start name returned source locals globals structs topOutside aligned sourceCode


/-- The source-first construction agrees with the earlier concrete fixture's
original-state representation, so its machine bound can be reused. -/
theorem concreteDecl_source_recovered {σ : Type}
    (start : MlString) (name : VarName) (returned : BitVec 64)
    (source : PanSemStateFiniteExact 64 σ)
    (locals : source.locals = HolFiniteMapExact.empty)
    (globals : source.globals = HolFiniteMapExact.empty)
    (sourceCode : source.code = HolFiniteMapExact.empty.update
      (newMainNameHOL (concreteDeclProgram start name returned),([],concreteDeclBody name returned,.one))) :
    source = concreteDeclOriginalState start name returned
      (callEntryStateHOLFinite
        (noGlobalsLoweredPreCall source (HolFiniteMapExact.empty.updateList
          (functionsHOL (compileTopExactHOL (concreteDeclProgram start name returned) start)).reverse))
        HolFiniteMapExact.empty) := by
  cases source
  simp_all [concreteDeclOriginalState,callEntryStateHOLFinite,noGlobalsLoweredPreCall]

end SteppedFlapjack.PanToCrepSteps
