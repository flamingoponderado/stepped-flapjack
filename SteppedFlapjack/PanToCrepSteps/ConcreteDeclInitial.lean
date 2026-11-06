import SteppedFlapjack.PanToCrepSteps.ConcreteDeclProgram

/-! Concrete global-entry source state and relation. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open SteppedFlapjack.CrepToLoopSteps

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

/-- Empty source locals and an empty Pancake compiler variable map satisfy the
Pancake-to-Crep local relation for any target locals. -/
theorem empty_panCrep_locals {width : Nat} [NeZero width]
    (ctxt : PanToCrepContextExact width) (target : HolFiniteMapExact Nat (HolWordLab width))
    (vars : ctxt.vars = HolFiniteMapExact.empty) :
    panToCrepLocalsRelFiniteExact ctxt HolFiniteMapExact.empty target := by
  simp [panToCrepLocalsRelFiniteExact,noOverlapFiniteExact,ctxtMaxFiniteExact,vars,
    HolFiniteMapExact.lookup_empty]

/-- The empty source-local map and empty variable context satisfy the
Crep-to-Loop relation at an empty live set, independent of Loop locals. -/
theorem empty_crepLoop_locals {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (target : Spt (WordLocW width))
    (vars : ctxt.vars = HolFiniteMapExact.empty) :
    crepToLoopLocalsRelExact ctxt .ln (HolFiniteMapExact.empty : HolFiniteMapExact Nat (HolWordLab width)) target := by
  simp [crepToLoopLocalsRelExact,crepToLoopDistinctVarsExact,crepToLoopCtxtMaxExact,vars,
    HolFiniteMapExact.lookup_empty,sptMem,sptDomain]

/-- Empty exception-shape and compiler-code maps are related. -/
theorem empty_panCrep_exceptions {width : Nat} [NeZero width] :
    panToCrepExcpRelFiniteExact (HolFiniteMapExact.empty : HolFiniteMapExact MlS (BitVec width))
      HolFiniteMapExact.empty := by
  simp [panToCrepExcpRelFiniteExact,HolFiniteMapExact.lookup_empty]

/-- Construct the Crep entry state from the Pancake data and the actual
compiled function list. No local or Crep global bindings are present. -/
def concreteDeclCrepState {σ : Type} (pan : PanSemStateFiniteExact 64 σ)
    (programs : List (MlString × List Nat × CrepProgHOL 64)) : CrepSemHOLState 64 σ where
  locals := HolFiniteMapExact.empty
  globals := HolFiniteMapExact.empty
  code := alistToFmapCodeExact programs
  memory := pan.memory
  memaddrs := pan.memaddrs
  shMemaddrs := pan.shMemaddrs
  clock := pan.clock
  be := pan.be
  ffi := pan.ffi
  baseAddr := pan.baseAddr
  topAddr := pan.topAddr

/-- The constructed Crep state satisfies the Pancake-to-Crep data relation
when the source has no structures or Pancake globals. -/
theorem concreteDecl_panCrep_stateRel {σ : Type} (pan : PanSemStateFiniteExact 64 σ)
    (programs : List (MlString × List Nat × CrepProgHOL 64))
    (structs : pan.structs = []) (globals : pan.globals = HolFiniteMapExact.empty) :
    panToCrepStateRelFiniteExact pan (concreteDeclCrepState pan programs) := by
  simp [panToCrepStateRelFiniteExact,concreteDeclCrepState,structs,globals,HolFiniteMapExact.empty]

open Classical in
/-- Construct the Loop entry by translating the Crep memory and using the
actual compiled Loop code table. -/
noncomputable def concreteDeclLoopState {σ : Type} (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (source : CrepSemHOLState 64 σ) (programs : List (MlString × List Nat × CrepProgHOL 64)) :
    LoopSemStateFiniteExact 64 σ where
  locals := .ln
  globals := HolFiniteMapExact.empty
  memory := fun address => wlabWlocExact (source.memory address)
  mdomain := fun address => decide (source.memaddrs address)
  shMdomain := fun address => decide (source.shMemaddrs address)
  clock := source.clock
  code := sptFromAList (compileProgHOLExact arch programs)
  be := source.be
  ffi := source.ffi
  baseAddr := source.baseAddr
  topAddr := source.topAddr

/-- The constructed Loop entry satisfies the Crep-to-Loop state, memory,
and global relations when the Crep global map is empty. -/
theorem concreteDecl_crepLoop_relations {σ : Type} (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (source : CrepSemHOLState 64 σ) (programs : List (MlString × List Nat × CrepProgHOL 64))
    (globals : source.globals = HolFiniteMapExact.empty) :
    crepToLoopStateRelExact source (concreteDeclLoopState arch source programs) ∧
    crepToLoopMemRelHOLExact source.memory (concreteDeclLoopState arch source programs).memory source.memaddrs ∧
    crepToLoopGlobalsRelHOLExact source.globals (concreteDeclLoopState arch source programs).globals := by
  classical
  simp [crepToLoopStateRelExact,crepToLoopMemRelHOLExact,crepToLoopGlobalsRelHOLExact,
    concreteDeclLoopState,globals,HolFiniteMapExact.lookup_empty]

/-- The constructed original source code has only the renamed main key. -/
theorem concreteDeclOriginalState_code_support {σ : Type} (start : MlString) (name : VarName)
    (returned : BitVec 64) (lowered : PanSemStateFiniteExact 64 σ) :
    ∀ key, (concreteDeclOriginalState start name returned lowered).code.lookup key ≠ none →
      key ∈ [newMainNameHOL (concreteDeclProgram start name returned)] := by
  intro key found
  simp [concreteDeclOriginalState,HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.lookup_empty] at found ⊢
  exact found.symm

/-- Equip a Word-state template with the concrete Loop entry data, heap
metadata, and actual compiled Word code. -/
noncomputable def concreteDeclWordState {C σ : Type} (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (source : CrepSemHOLState 64 σ) (programs : List (MlString × List Nat × CrepProgHOL 64))
    (template : WordSemStateFiniteExact 64 C σ) (heapLength : BitVec 64) : WordSemStateFiniteExact 64 C σ :=
  { template with
    memory := (concreteDeclLoopState arch source programs).memory
    mdomain := (concreteDeclLoopState arch source programs).mdomain
    shMdomain := (concreteDeclLoopState arch source programs).shMdomain
    clock := source.clock
    be := source.be
    ffi := source.ffi
    store := (template.store.updateEq (.currHeap,.word source.baseAddr)).updateEq (.heapLength,.word heapLength)
    code := sptFromAList (loopToWordCompileHOL (compileProgHOLExact arch programs)) }

/-- When the heap endpoints agree, the constructed Word state satisfies the
Loop-to-Word data relation and has the actual compiled code table. -/
theorem concreteDecl_word_data {C σ : Type} (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (source : CrepSemHOLState 64 σ) (programs : List (MlString × List Nat × CrepProgHOL 64))
    (template : WordSemStateFiniteExact 64 C σ) (heapLength : BitVec 64)
    (heap : source.topAddr = source.baseAddr + 2 * heapLength) :
    LoopWordDataRel (concreteDeclLoopState arch source programs)
      (concreteDeclWordState arch source programs template heapLength) ∧
    (concreteDeclWordState arch source programs template heapLength).code =
      sptFromAList (loopToWordCompileHOL (compileProgHOLExact arch programs)) := by
  refine ⟨⟨heapLength,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩,rfl⟩
  all_goals simp [concreteDeclWordState,concreteDeclLoopState,HolFiniteMapExact.lookup_updateEq,
    FUPDATE_HOL,loopToWordGlobalsRelHOLExact,HolFiniteMapExact.lookup_empty,heap]

end SteppedFlapjack.PanToCrepSteps
