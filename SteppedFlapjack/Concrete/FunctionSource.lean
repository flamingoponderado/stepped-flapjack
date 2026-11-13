import SteppedFlapjack.Concrete.SourceState
import SteppedFlapjack.Concrete.CountedSource
import SteppedFlapjack.Concrete.Phase7SourceClock
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open SteppedFlapjack.PanToCrepSteps
open Flapjack.Pancake.PanStructs.CompileShapeExact Flapjack.Compiler.Encoders.RiscV.Target

/-- Byte-representable function names have the same executable and HOL lookup. -/
theorem function_table_lookup (fs : List (FunDeclOf 64))
    (ranged : ∀ f ∈ fs, NameRanged f.name) (name : String) (hn : NameRanged name) :
    Option.map panLangEntryToHOL (panSemCodeLookup (functionEntries (fs.map Decl.function)) name) =
    (HolFiniteMapExact.empty.updateList (functionsHOL ((fs.map (fun f => funDeclToHOL f)).map DeclHOL.function)).reverse).lookup (ofString name) := by
  change Option.map panLangEntryToHOL (panSemCodeLookup (functionEntries (fs.map Decl.function)) name) =
    FLOOKUP (FUPDATE_LIST FEMPTY (functionsHOL ((fs.map (fun f => funDeclToHOL f)).map DeclHOL.function)).reverse) (ofString name)
  rw [FLOOKUP_FUPDATE_LIST_reverse_eq_lookup]
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    have hf := ranged f (by simp)
    have ht : ∀ f ∈ fs, NameRanged f.name := fun f h => ranged f (by simp [h])
    by_cases eq : f.name = name
    · subst name
      simp [functionEntries, panSemCodeLookup, lookupInfo, functionsHOL, funDeclToHOL, panLangEntryToHOL]
    · have hne : ofString f.name ≠ ofString name := fun h => eq (ofString_injective_of_ranged hf hn h)
      have hb : (ofString name == ofString f.name) = false := by
        cases he : (ofString name == ofString f.name) <;> simp_all [beq_iff_eq]
      simpa [functionEntries, panSemCodeLookup, lookupInfo, functionsHOL, funDeclToHOL, List.lookup,
        eq, hne, Ne.symm hne, hb, List.map_map] using ih ht


/-- Executable initial state for concrete function declarations and bitmap layout. -/
def functionSourceProduction (fs : List (FunDeclOf 64)) (n clock : Nat) :
    PanSemState (RiscV.Word 64) (FfiState Unit) :=
  {sourceProduction with code := functionEntries (fs.map Decl.function), memory := fun a => some (.word (initialWordFor n a)), clock := clock}

/-- Corresponding HOL initial state for the same declarations and layout. -/
def functionSourceExact (fs : List (FunDeclOf 64)) (n clock : Nat) : PanSemStateFiniteExact 64 Unit :=
  {sourceTemplateFor n with code := HolFiniteMapExact.empty.updateList (functionsHOL ((fs.map funDeclToHOL).map DeclHOL.function)).reverse, clock := clock}

/-- The initialized executable and HOL states agree for every ranged function table. -/
theorem functionSource_related (fs : List (FunDeclOf 64)) (n clock : Nat)
    (ranged : ∀ f ∈ fs, NameRanged f.name) :
    PanSemStateRelExec (functionSourceProduction fs n clock) (functionSourceExact fs n clock).toExact := by
  have base := source_related (.skip : ProgHOL 64)
  obtain ⟨_,_,hs,_,_,_,_,_,_,hbe,hffi,hbase,htop⟩ := base
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,rfl,?_,?_,?_,?_⟩
  · simp [functionSourceProduction,functionSourceExact,sourceProduction,sourceTemplateFor,sourceTemplate]
  · simp [functionSourceProduction,functionSourceExact,sourceProduction,sourceTemplateFor,sourceTemplate]
  · simpa [functionSourceProduction,functionSourceExact,executableState,exactState,
      singleEntrySourceProduction,singleEntrySourceTemplate,PanSemStateFiniteExact.toExact,sourceProduction,sourceTemplateFor,sourceTemplate] using hs
  · intro name hname
    exact function_table_lookup fs ranged name hname
  · simp [functionSourceProduction,functionSourceExact,sourceProduction,sourceTemplateFor,sourceTemplate]
  · intro addr member; rfl
  · simp [functionSourceProduction,functionSourceExact,sourceProduction,sourceTemplateFor,sourceTemplate]
  · simp [functionSourceProduction,functionSourceExact,sourceProduction,sourceTemplateFor,sourceTemplate]
  · exact hbe
  · exact hffi
  · exact hbase
  · exact htop


/-- Scalar, call-aware functions with representable names and shapes. -/
def FunctionTableSupported (fs : List (FunDeclOf 64)) : Prop :=
  ∀ f ∈ fs, FunDeclByteRanged f ∧ CallSupportedIn (f.params.map Prod.fst) f.body ∧
    (∀ p ∈ f.params, p.2 = .one) ∧ f.returnShape = .one

theorem functionEntries_map (fs : List (FunDeclOf 64)) :
    functionEntries (fs.map Decl.function) = fs.map (fun f => (f.name,f.params,f.body,f.returnShape)) := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [functionEntries,ih]

theorem table_names (fs : List (FunDeclOf 64)) (h : FunctionTableSupported fs) :
    ∀ f ∈ fs, NameRanged f.name := by
  intro f hf
  exact (h f hf).1.1

theorem table_code_ranged (fs : List (FunDeclOf 64)) (n clock : Nat) (h : FunctionTableSupported fs) :
    ∀ name entry, panSemCodeLookup (functionSourceProduction fs n clock).code name = some entry →
      PanLangEntryByteRanged entry := by
  have ranged : ∀ d ∈ fs.map Decl.function, DeclByteRanged d := by
    intro d hd
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hd
    exact (h f hf).1
  simpa [functionSourceProduction,PanSemCodeRanged] using
    (panSemCodeRanged_of_functionEntries sourceProduction (fs.map Decl.function) ranged)

theorem table_counted_shapes (fs : List (FunDeclOf 64)) (n clock : Nat) (h : FunctionTableSupported fs) :
    ∀ name params body, (name,params,body) ∈ countedFunctionsOfCode (functionSourceProduction fs n clock).code →
      ∃ scope, CallSupportedIn scope body := by
  intro name params body hm
  simp only [functionSourceProduction,countedFunctionsOfCode,functionEntries_map,List.map_map,List.mem_map] at hm
  obtain ⟨f,hf,heq⟩ := hm
  cases heq
  exact ⟨f.params.map Prod.fst,(h f hf).2.1⟩


theorem functionEntriesHOL_map (fs : List (FunDeclOf 64)) :
    functionsHOL ((fs.map funDeclToHOL).map DeclHOL.function) =
      fs.map (fun f => (ofString f.name, f.params.map paramToHOL, progToHOL f.body, shapeToHOL f.returnShape)) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    simpa [functionsHOL,funDeclToHOL,List.map_map] using
      congrArg (List.cons (ofString f.name, f.params.map paramToHOL, progToHOL f.body, shapeToHOL f.returnShape)) ih

theorem original_entry_shapes (fs : List (FunDeclOf 64)) (h : FunctionTableSupported fs) :
    ∀ entry ∈ functionsHOL ((fs.map funDeclToHOL).map DeclHOL.function),
      ∃ scope, ∃ program : Prog (RiscV.Word 64),
        entry.2.2.1 = progToHOL program ∧ CallSupportedIn scope program ∧ ProgByteRanged program := by
  rw [functionEntriesHOL_map]
  intro entry he
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
  exact ⟨f.params.map Prod.fst,f.body,rfl,(h f hf).2.1,(h f hf).1.2.2.1⟩

/-- Scalar parameters keep their names and scalar shapes in HOL. -/
theorem scalarParams_toHOL (params : List (VarName × Shape))
    (scalar : ∀ p ∈ params, p.2 = .one) :
    params.map paramToHOL = (params.map Prod.fst).map (fun n => (ofString n,ShapeHOL.one)) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro p hp
  have hp' := scalar p hp
  simp [paramToHOL,hp',shapeToHOL]

/-- Simplification preserves scalar, call-aware function table shapes. -/
theorem simplified_entry_shapes (sourceFs : List (FunDeclOf 64)) (supported : FunctionTableSupported sourceFs) :
    ∀ entry ∈ functionsHOL (((sourceFs.map funDeclToHOL).map (fun f => {f with body := panSimpCompileHOL f.body})).map DeclHOL.function),
      ∃ names, ∃ body : Prog (RiscV.Word 64),
        entry.2.1 = names.map (fun n => (ofString n,ShapeHOL.one)) ∧
        entry.2.2.1 = progToHOL body ∧ CallSupportedIn names body ∧ ProgByteRanged body := by
  have eq : functionsHOL (((sourceFs.map funDeclToHOL).map (fun f => {f with body := panSimpCompileHOL f.body})).map DeclHOL.function) =
      sourceFs.map (fun f => (ofString f.name, f.params.map paramToHOL, panSimpCompileHOL (progToHOL f.body), shapeToHOL f.returnShape)) := by
    clear supported
    induction sourceFs with
    | nil => rfl
    | cons f fs ih =>
      simpa [functionsHOL,funDeclToHOL,List.map_map] using congrArg
        (List.cons (ofString f.name, f.params.map paramToHOL, panSimpCompileHOL (progToHOL f.body), shapeToHOL f.returnShape)) ih
  rw [eq]
  intro entry he
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
  obtain ⟨ranged,shape,params,ret⟩ := supported f hf
  have paramEq := scalarParams_toHOL f.params params
  refine ⟨f.params.map Prod.fst,panSimpProg f.body,paramEq,?_,callSupported_panSimp shape,callSupported_panSimp_ranged shape ranged.2.2.1⟩
  exact callSupported_panSimp_hol shape

/-- Original supported functions have the scalar frontend table shape. -/
theorem original_function_shapes (fs : List (FunDeclOf 64)) (supported : FunctionTableSupported fs) :
    ∀ entry ∈ functionsHOL ((fs.map funDeclToHOL).map DeclHOL.function),
      ∃ names, ∃ body : Prog (RiscV.Word 64),
        entry.2.1 = names.map (fun n => (ofString n,ShapeHOL.one)) ∧
        entry.2.2.1 = progToHOL body ∧ CallSupportedIn names body ∧ ProgByteRanged body := by
  rw [functionEntriesHOL_map]
  intro entry he
  obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
  obtain ⟨ranged,shape,params,_⟩ := supported f hf
  have paramEq := scalarParams_toHOL f.params params
  exact ⟨f.params.map Prod.fst,f.body,paramEq,rfl,shape,ranged.2.2.1⟩

/-- Scalar function shapes are well formed in the empty struct context. -/
theorem table_wellFormed (fs : List (FunDeclOf 64)) (supported : FunctionTableSupported fs) :
    (fs.map funDeclToHOL).all (fun f => f.params.all (fun p => isWfShapeExactHOL ([] : StructContextExact) p.2) &&
      isWfShapeExactHOL ([] : StructContextExact) f.returnShape) = true := by
  simp only [List.all_eq_true, List.mem_map]
  intro f hf
  obtain ⟨g,hg,rfl⟩ := hf
  obtain ⟨_,_,params,ret⟩ := supported g hg
  simp only [funDeclToHOL]
  simp only [List.all_eq_true, List.mem_map, Bool.and_eq_true]
  constructor
  · intro p hp
    obtain ⟨p,hp,rfl⟩ := hp
    simp [paramToHOL,params p hp,shapeToHOL]
  · simp [ret,shapeToHOL]

/-- Struct lowering fixes supported call-aware function tables. -/
private theorem scalar_list_fixed {scope : List VarName} (args : List (Exp (RiscV.Word 64)))
    (scalar : ∀ e ∈ args, Scalar scope e) (ctxt : ContextExact) :
    compileExpsExact ctxt (args.map expToHOL) = args.map expToHOL := by
  induction args with
  | nil => simp [compileExpsExact]
  | cons e es ih =>
    simp [compileExpsExact, scalar_structs_fixed (scalar e (by simp)) ctxt,
      ih (fun e he => scalar e (by simp [he]))]

theorem call_structs_fixed {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope program) (ctxt : ContextExact) :
    compileProgExact ctxt (progToHOL program) = progToHOL program := by
  induction supported generalizing ctxt with
  | base h => exact supported_structs_fixed h ctxt
  | tail name args scalar => simp [progToHOL,compileProgExact,scalar_list_fixed args scalar ctxt]
  | call dest name args scalar cont ih => simp [progToHOL,shapeToHOL,compileProgExact,compileShapeExact,scalar_list_fixed args scalar ctxt,ih]
  | decl name scalar body ih => simp [progToHOL,shapeToHOL,compileProgExact,compileShapeExact,scalar_structs_fixed scalar ctxt,ih]
  | seq a b iha ihb => simp [progToHOL,compileProgExact,iha,ihb]
  | ite scalar a b iha ihb => simp [progToHOL,compileProgExact,scalar_structs_fixed scalar ctxt,iha,ihb]
  | «while» scalar body ih => simp [progToHOL,compileProgExact,scalar_structs_fixed scalar ctxt,ih]

theorem call_structs_declarations (fs : List (FunDeclOf 64)) (supported : FunctionTableSupported fs)
    (ctxt : ContextExact) :
    let simplified := (fs.map funDeclToHOL).map (fun f => {f with body := panSimpCompileHOL f.body})
    compileDeclsExact ctxt (simplified.map DeclHOL.function) = (simplified.map DeclHOL.function,ctxt) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    have h := supported f (by simp)
    have hs : FunctionTableSupported fs := fun g hg => supported g (by simp [hg])
    obtain ⟨_,shape,params,ret⟩ := h
    have pEq : (f.params.map paramToHOL).map (fun p => (p.1,compileShapeExact ctxt.structs p.2)) =
        f.params.map paramToHOL := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro p hp
      simp [paramToHOL,params p hp,shapeToHOL,compileShapeExact]
    have body := call_structs_fixed (callSupported_panSimp shape) {ctxt with locals := f.params.map paramToHOL}
    rw [← callSupported_panSimp_hol shape] at body
    simp only [List.map_cons,compileDeclsExact, ih hs, funDeclToHOL]
    simp [pEq,ret,shapeToHOL,compileShapeExact,body]

theorem call_structs_top (fs : List (FunDeclOf 64)) (supported : FunctionTableSupported fs) :
    let simplified := (fs.map funDeclToHOL).map (fun f => {f with body := panSimpCompileHOL f.body})
    compileTopExact (simplified.map DeclHOL.function) = simplified.map DeclHOL.function := by
  let simplified := (fs.map funDeclToHOL).map (fun f => {f with body := panSimpCompileHOL f.body})
  let ctxt : ContextExact := {structs := [], locals := [], globals := []}
  have names : getNamesExact ctxt (simplified.map DeclHOL.function) = ctxt := by
    clear supported
    induction simplified with
    | nil => rfl
    | cons f fs ih => simpa [getNamesExact] using ih
  change (compileDeclsExact (getNamesExact ctxt (simplified.map DeclHOL.function)) (simplified.map DeclHOL.function)).1 = _
  rw [names,call_structs_declarations fs supported ctxt]

theorem call_panToWord (fs : List (FunDeclOf 64)) (supported : FunctionTableSupported fs) :
    panToWordCompileProgHOL riscvConfig.isa ((fs.map funDeclToHOL).map DeclHOL.function) =
      loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa
        (compileProgDeclsHOLW (compileTopExactHOL ((((fs.map funDeclToHOL).map
          (fun f => {f with body := panSimpCompileHOL f.body})).map DeclHOL.function)) (ofString "main")))) := by
  unfold panToWordCompileProgHOL
  rw [simpFunctions]
  dsimp only
  rw [call_structs_top fs supported]

/-- Supported function declarations satisfy the source compiler good-code check. -/
theorem table_good (fs : List (FunDeclOf 64)) (supported : FunctionTableSupported fs) :
    pancakeGoodCodeHOL ((fs.map funDeclToHOL).map DeclHOL.function) = true := by
  simp only [pancakeGoodCodeHOL,List.all_eq_true,List.mem_map]
  intro d hd
  obtain ⟨f,hf,rfl⟩ := hd
  obtain ⟨f,hf,rfl⟩ := hf
  simpa [goodPanopsHOL,funDeclToHOL] using call_good (supported f hf).2.1

end SteppedFlapjack.Concrete
