import SteppedFlapjack.PanToCrepSteps.ConcreteDeclProgram

/-! Concrete global-entry source state and relation. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact

/-- With no globals, the actual initial global context has zero size. -/
theorem concreteDeclGlobalContext_empty (start : MlString) (name : VarName) (returned : BitVec 64) :
    concreteDeclGlobalContext start name returned =
      { globals := HolFiniteMapExact.empty, globalsSize := 0, maxGlobalsSize := 0 } := by
  simp [concreteDeclGlobalContext,concreteDeclProgram,resortDeclsHOL,isNameHOL,isExnDeclHOL,
    isDeclHOL,isFunctionHOL,List.filter,fpermDecsHOL,decShapesHOL]

/-- A concrete original source state can be recovered from the lowered entry
by changing only its code and clearing its global map. -/
def concreteDeclOriginalState {σ : Type} (start : MlString) (name : VarName) (returned : BitVec 64)
    (lowered : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ :=
  { lowered with globals := HolFiniteMapExact.empty, code := HolFiniteMapExact.empty.update (newMainNameHOL (concreteDeclProgram start name returned),([],concreteDeclBody name returned,.one)) }

/-- For a suitable lowered code lookup and ordinary memory-layout facts, the
constructed original state satisfies the full globals-pass state relation. -/
theorem concreteDecl_original_globalRel {σ : Type} (start : MlString) (name : VarName) (returned : BitVec 64)
    (lowered : PanSemStateFiniteExact 64 σ)
    (structs : lowered.structs = []) (topOutside : ¬ lowered.memaddrs lowered.topAddr)
    (aligned : panGlobalsByteAlignedHOL lowered.topAddr)
    (lookup : lowered.code.lookup (newMainNameHOL (concreteDeclProgram start name returned)) =
      some ([],concreteDeclBody name returned,.one)) :
    panGlobalsStateRelHOLExact true (concreteDeclGlobalContext start name returned)
      (concreteDeclOriginalState start name returned lowered) lowered := by
  rw [concreteDeclGlobalContext_empty]
  simp [panGlobalsStateRelHOLExact,concreteDeclOriginalState,structs,disjointGlobalsHOLExact,
    HolFiniteMapExact.lookup_empty,topOutside,aligned]
  refine ⟨?_,Or.inr rfl⟩
  intro function parameters program returnShape found
  simp only [FUPDATE,HolFiniteMapExact.lookup_empty] at found
  split at found
  · rename_i eq
    simp only [Option.some.injEq,Prod.mk.injEq] at found
    rcases found with ⟨rfl,rfl,rfl⟩
    have same : newMainNameHOL (concreteDeclProgram start name returned) = function := by simpa using eq
    subst function
    simpa only [(concreteDeclBody_globals_fixed start start _ name returned).2] using lookup
  · simp at found

/-- The actual generated Pancake code table contains the renamed concrete
callee with its unchanged body. -/
theorem concreteDecl_lowered_lookup {σ : Type} (start : MlString) (name : VarName) (returned : BitVec 64)
    (pan : PanSemStateFiniteExact 64 σ)
    (codeEq : pan.code = HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL (concreteDeclProgram start name returned) start)).reverse) :
    pan.code.lookup (newMainNameHOL (concreteDeclProgram start name returned)) =
      some ([],concreteDeclBody name returned,.one) := by
  have fresh : newMainNameHOL (concreteDeclProgram start name returned) ≠ start := by
    intro same
    have notMem := PanGlobalsDeclListExact.freshNameMlS_correct (ofString "main")
      ((functionsHOL (concreteDeclProgram start name returned)).map Prod.fst)
    apply notMem
    simpa [newMainNameHOL,concreteDeclProgram,functionsHOL] using same
  rw [codeEq,concreteDecl_compileTop]
  simp [functionsHOL,HolFiniteMapExact.lookup_updateList,FUPDATE_LIST,FUPDATE,Ne.symm fresh]

end SteppedFlapjack.PanToCrepSteps
