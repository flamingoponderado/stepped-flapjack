import SteppedFlapjack.PanToCrepSteps.GlobalEntry
import Flapjack.Pancake.Proofs.PanGlobals.FpermCode
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


private theorem functionOnly_resort {width : Nat} [NeZero width] (fs : List (FunDeclHOL width)) :
    resortDeclsHOL (fs.map DeclHOL.function) = fs.map DeclHOL.function := by
  simp [resortDeclsHOL,List.filter_map,Function.comp_def,isNameHOL,isExnDeclHOL,isDeclHOL,isFunctionHOL]
private theorem functionOnly_perm {width : Nat} [NeZero width] (fs : List (FunDeclHOL width)) (a b : MlS) :
    ∀ d ∈ fpermDecsHOL a b (fs.map DeclHOL.function), isFunctionHOL d = true := by
  induction fs with
  | nil => simp [fpermDecsHOL]
  | cons f fs ih =>
    simp only [List.map_cons,fpermDecsHOL,List.mem_cons]
    intro d h
    rcases h with rfl | h
    · rfl
    · exact ih d h
private theorem functionOnly_shapes {width : Nat} [NeZero width] (fs : List (FunDeclHOL width)) (a b : MlS) :
    decShapesHOL (fpermDecsHOL a b (fs.map DeclHOL.function)) = [] := by
  induction fs with
  | nil => simp [fpermDecsHOL,decShapesHOL]
  | cons f fs ih => simp [fpermDecsHOL,decShapesHOL,ih]
private theorem functions_map_compile {width : Nat} [NeZero width] (ctx : PanGlobalsContextExact width) (ds : List (DeclHOL width)) :
    functionsHOL (ds.map (fun d => match d with
      | .function f => .function {f with body := compileProgExactHOL ctx f.body}
      | _ => .name (ofString "") [])) =
      (functionsHOL ds).map (fun e => (e.1,e.2.1,compileProgExactHOL ctx e.2.2.1,e.2.2.2)) := by
  induction ds with
  | nil => rfl
  | cons d ds ih => cases d <;> simp [functionsHOL,ih]
/-- Function-only declarations generate no global initialization or exceptions. -/
theorem functionOnly_compileDecs {width : Nat} [NeZero width]
    (fs : List (FunDeclHOL width)) (a b : MlS) :
    let renamed := fpermDecsHOL a b (resortDeclsHOL (fs.map DeclHOL.function))
    let initial : PanGlobalsContextExact width :=
      { globals := HolFiniteMapExact.empty, globalsSize := 0,
        maxGlobalsSize := cakeBytesInWord width * BitVec.ofNat width ((decShapesHOL renamed).map sizeOfShapeHOL).sum }
    compileDecsExactHOL initial renamed = ([],
      (fpermDecsHOL a b (fs.map DeclHOL.function)).map (fun d => match d with
        | .function f => .function {f with body := compileProgExactHOL emptyGlobalsContext f.body}
        | _ => .name (ofString "") []),[],emptyGlobalsContext) := by
  let renamed := fpermDecsHOL a b (fs.map DeclHOL.function)
  rcases h : compileDecsExactHOL emptyGlobalsContext renamed with ⟨initializers,funs,exns,ctx⟩
  obtain ⟨rfl,rfl,rfl,rfl⟩ := PanGlobalsCompileDecsStructural.compile_decs_functions_thmHOL _ _ _ _ _ _
    ⟨h,functionOnly_perm fs a b⟩
  simp only [functionOnly_resort,functionOnly_shapes,List.map_nil,List.sum_nil]
  change compileDecsExactHOL emptyGlobalsContext renamed = _
  rw [h]
  congr 2

/-- A function-only source produces an empty initializer and the translated function table. -/
theorem functionOnly_compileTop_functions {width : Nat} [NeZero width]
    (fs : List (FunDeclHOL width)) (start : MlS) (body : ProgHOL width) (shape : ShapeHOL)
    (found : (functionsHOL (fs.map DeclHOL.function)).lookup start = some ([],body,shape)) :
    functionsHOL (compileTopExactHOL (fs.map DeclHOL.function) start) =
      (start,[],.seq .skip (.call none (newMainNameHOL (fs.map DeclHOL.function)) []),shape) ::
        (functionsHOL (fpermDecsHOL start (newMainNameHOL (fs.map DeclHOL.function)) (fs.map DeclHOL.function))).map
          (fun e => (e.1,e.2.1,compileProgExactHOL emptyGlobalsContext e.2.2.1,e.2.2.2)) := by
  obtain ⟨initializers,funs,exns,ctx,compiled,top⟩ :=
    compileTop_entry_wrapper (fs.map DeclHOL.function) start [] body shape found
  have known := functionOnly_compileDecs fs start (newMainNameHOL (fs.map DeclHOL.function))
  dsimp only at known
  rw [compiled] at known
  simp only [Prod.mk.injEq] at known
  obtain ⟨rfl,rfl,rfl,rfl⟩ := known
  rw [top]
  simp only [List.nil_append,functionsHOL,nestedSeqHOL,List.map_nil]
  congr 1
  exact functions_map_compile emptyGlobalsContext _


private theorem updateList_eq_updateListEq {α β : Type} [DecidableEq α]
    (m : HolFiniteMapExact α β) (entries : List (α × β)) : m.updateList entries = m.updateListEq entries := by
  apply HolFiniteMapExact.ext
  funext k
  simp only [HolFiniteMapExact.lookup_updateList,HolFiniteMapExact.lookup_updateListEq]
  rw [FUPDATE_LIST_HOL_eq_FUPDATE_LIST]

/-- Function renaming commutes with initialization of a declaration code table. -/
theorem functionOnly_renamedTable {width : Nat} [NeZero width]
    (declarations : List (DeclHOL width)) (a b : MlS) :
    fpermCodeHOL a b (HolFiniteMapExact.empty.updateList (functionsHOL declarations).reverse) =
      HolFiniteMapExact.empty.updateList (functionsHOL (fpermDecsHOL a b declarations)).reverse := by
  rw [updateList_eq_updateListEq,fpermCodeHOL_updateListEq,fpermCodeHOL_empty]
  rw [← updateList_eq_updateListEq,functionsFpermDecsHOL,List.map_reverse]

private theorem lookup_mapBodies {width : Nat} [NeZero width]
    (ctx : PanGlobalsContextExact width)
    (entries : List (MlS × List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)) (name : MlS) :
    (entries.map (fun e => (e.1,e.2.1,compileProgExactHOL ctx e.2.2.1,e.2.2.2))).lookup name =
      (entries.lookup name).map (fun e => (e.1,compileProgExactHOL ctx e.2.1,e.2.2)) := by
  induction entries with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨key,params,body,shape⟩ := e
    by_cases h : name = key
    · subst key; simp [List.lookup]
    · have heq : (name == key) = false := by simp [h]
      simp [List.lookup,heq,ih]

private theorem lookup_none_not_mem {α β : Type} [BEq α] [LawfulBEq α]
    (entries : List (α × β)) (key : α) (absent : key ∉ entries.map Prod.fst) : entries.lookup key = none := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨name,value⟩ := entry
    simp only [List.map_cons,List.mem_cons,not_or] at absent
    have neq : (key == name) = false := by simp [absent.1]
    simp only [List.lookup_cons,neq]
    exact ih absent.2

/-- Every renamed source function resolves to its actual global-lowered body. -/
theorem functionOnly_compiled_code_lookup {width : Nat} [NeZero width]
    (fs : List (FunDeclHOL width)) (start : MlS) (body : ProgHOL width) (shape : ShapeHOL)
    (found : (functionsHOL (fs.map DeclHOL.function)).lookup start = some ([],body,shape))
    (name : MlS) (parameters : List (MlS × ShapeHOL)) (program : ProgHOL width) (returnShape : ShapeHOL)
    (sourceFound : (fpermCodeHOL start (newMainNameHOL (fs.map DeclHOL.function))
      (HolFiniteMapExact.empty.updateList (functionsHOL (fs.map DeclHOL.function)).reverse)).lookup name =
        some (parameters,program,returnShape)) :
    (HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL (fs.map DeclHOL.function) start)).reverse).lookup name =
        some (parameters,compileProgExactHOL emptyGlobalsContext program,returnShape) := by
  let declarations := fs.map DeclHOL.function
  let fresh := newMainNameHOL declarations
  have freshNone : (HolFiniteMapExact.empty.updateList (functionsHOL declarations).reverse).lookup fresh = none := by
    change FLOOKUP (FUPDATE_LIST FEMPTY (functionsHOL declarations).reverse) fresh = none
    rw [FLOOKUP_FUPDATE_LIST_reverse_eq_lookup]
    exact lookup_none_not_mem _ _ (PanGlobalsDeclListExact.new_main_name_correctHOL declarations)
  have startNone : (fpermCodeHOL start fresh
      (HolFiniteMapExact.empty.updateList (functionsHOL declarations).reverse)).lookup start = none := by
    rw [flookupFpermCodeHOL']
    simpa [fpermName,freshNone]
  have nameNe : name ≠ start := by
    intro eq
    subst name
    rw [startNone] at sourceFound
    cases sourceFound
  rw [functionOnly_renamedTable] at sourceFound
  have sourceLookup : (functionsHOL (fpermDecsHOL start fresh declarations)).lookup name =
      some (parameters,program,returnShape) := by
    change FLOOKUP (FUPDATE_LIST FEMPTY (functionsHOL (fpermDecsHOL start fresh declarations)).reverse) name = _ at sourceFound
    rwa [FLOOKUP_FUPDATE_LIST_reverse_eq_lookup] at sourceFound
  change FLOOKUP (FUPDATE_LIST FEMPTY (functionsHOL (compileTopExactHOL declarations start)).reverse) name = _
  rw [FLOOKUP_FUPDATE_LIST_reverse_eq_lookup,
    functionOnly_compileTop_functions fs start body shape found]
  have nebeq : (name == start) = false := by simp [nameNe]
  simp only [List.lookup_cons,nebeq]
  rw [lookup_mapBodies,sourceLookup]
  rfl

/-- Function-only initialized programs establish the actual global-entry relation. -/
theorem functionOnly_source_initialization {σ : Type}
    (fs : List (FunDeclHOL 64)) (start : MlS) (body : ProgHOL 64) (shape : ShapeHOL)
    (found : (functionsHOL (fs.map DeclHOL.function)).lookup start = some ([],body,shape))
    (source : PanSemStateFiniteExact 64 σ)
    (locals : source.locals = HolFiniteMapExact.empty) (globals : source.globals = HolFiniteMapExact.empty)
    (structs : source.structs = []) (topOutside : ¬ source.memaddrs source.topAddr)
    (aligned : panGlobalsByteAlignedHOL source.topAddr)
    (sourceCode : source.code = fpermCodeHOL start (newMainNameHOL (fs.map DeclHOL.function))
      (HolFiniteMapExact.empty.updateList (functionsHOL (fs.map DeclHOL.function)).reverse)) :
    let pre := noGlobalsLoweredPreCall source (HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL (fs.map DeclHOL.function) start)).reverse)
    pre.evaluateHOLFiniteState (nestedSeqHOL []) = (none,pre) ∧ pre.clock ≠ 0 ∧
      panGlobalsStateRelHOLExact true emptyGlobalsContext source (callEntryStateHOLFinite pre HolFiniteMapExact.empty) := by
  refine ⟨evaluateHOLFiniteState_skip _,by simp [noGlobalsLoweredPreCall],?_⟩
  apply noGlobals_source_callEntry_rel source _ locals globals structs topOutside aligned
  intro name params program returnShape h
  rw [sourceCode] at h
  exact functionOnly_compiled_code_lookup fs start body shape found name params program returnShape h


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
