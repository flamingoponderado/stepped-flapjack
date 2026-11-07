import SteppedFlapjack.PanToCrepSteps.SourceInitialGlobals
import SteppedFlapjack.PanToCrepSteps.GlobalPanCodeRel

/-! Actual globals-pass code for one zero-argument function. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact

/-- A zero-argument program with no globals or exceptions. -/
def singleEntryProgram (start : MlString) (body : ProgHOL 64) : List (DeclHOL 64) :=
  [.function ⟨start,false,false,[],body,.one⟩]

/-- The actual simplifier removes the initial skip from a scalar countdown
entry before the globals pass. -/
theorem singleEntry_declared_panSimp (start name : MlString) (initial returned : BitVec 64)
    (condition assignment : ExpHOL 64) :
    panSimpDeclsHOL (singleEntryProgram start (.dec name .one (.const initial) (.seq .skip
      (.seq (.while condition (.assign .local name assignment)) (.return (.const returned)))))) =
    singleEntryProgram start (.dec name .one (.const initial)
      (.seq (.while condition (.assign .local name assignment)) (.return (.const returned)))) := by
  simp [singleEntryProgram,panSimpDeclsHOL,panSimpCompileHOL,seqAssocHOL,smartSeqHOL,retToTailHOL,seqCallRetHOL]

/-- The full compiler's structure pass leaves the simplified scalar
countdown unchanged. -/
theorem singleEntry_countdown_structs (start name : MlString) (initial returned : BitVec 64) :
    let body : ProgHOL 64 := .dec name .one (.const initial)
      (.seq (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
        (.return (.const returned)))
    Pancake.PanStructs.CompileShapeExact.compileTopExact (singleEntryProgram start body) =
      singleEntryProgram start body := by
  simp [singleEntryProgram,Pancake.PanStructs.CompileShapeExact.compileTopExact,
    Pancake.PanStructs.CompileShapeExact.getNamesExact,Pancake.PanStructs.CompileShapeExact.compileDeclsExact,
    Pancake.PanStructs.CompileShapeExact.compileProgExact,Pancake.PanStructs.CompileShapeExact.compileExpExact,
    Pancake.PanStructs.CompileShapeExact.compileExpsExact,Pancake.PanStructs.CompileShapeExact.compileShapeExact]

/-- The actual Pancake-to-Word compiler first removes the leading skip, then
compiles the resulting scalar countdown through the globals and backend passes. -/
theorem singleEntry_countdown_panToWord (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (name : MlString) (initial returned : BitVec 64) :
    let start := ofString "main"
    let body : ProgHOL 64 := .dec name .one (.const initial)
      (.seq (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
        (.return (.const returned)))
    panToWordCompileProgHOL arch (singleEntryProgram start (.dec name .one (.const initial) (.seq .skip
      (.seq (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
        (.return (.const returned)))))) =
      loopToWordCompileHOL (compileProgHOLExact arch
        (compileProgDeclsHOLW (compileTopExactHOL (singleEntryProgram start body) start))) := by
  simp only [panToWordCompileProgHOL,singleEntry_declared_panSimp,singleEntry_countdown_structs]

/-- The actual global compiler creates the wrapper and a renamed, lowered
callee; no property of the body is assumed. -/
theorem singleEntry_compileTop (start : MlString) (body : ProgHOL 64) :
    let declarations := singleEntryProgram start body
    let renamed := newMainNameHOL declarations
    compileTopExactHOL declarations start =
      [.function ⟨start,false,false,[],.seq .skip (.call none renamed []),.one⟩,
       .function ⟨renamed,false,false,[],
         compileProgExactHOL emptyGlobalsContext (fpermHOL start renamed body),.one⟩] := by
  simp [compileTopExactHOL,compileTopFunctionLookup_eq_lookup,singleEntryProgram,functionsHOL,
    resortDeclsHOL,isNameHOL,isExnDeclHOL,isDeclHOL,isFunctionHOL,List.filter,
    fpermDecsHOL,fpermName,compileDecsExactHOL,decShapesHOL,emptyGlobalsContext]

/-- A local-assignment loop has no function calls to rename, independently
of its condition and assignment expressions. -/
theorem declaredAssignLoop_fperm (start renamed name : MlString) (initial returned : BitVec 64)
    (condition assignment : ExpHOL 64) :
    fpermHOL start renamed (.dec name .one (.const initial) (.seq .skip
      (.seq (.while condition (.assign .local name assignment)) (.return (.const returned))))) =
      .dec name .one (.const initial) (.seq .skip
        (.seq (.while condition (.assign .local name assignment)) (.return (.const returned)))) := by
  simp [fpermHOL]


/-- Every function in the singleton original code table has the expected
compiled lookup in the actual generated table. The original table contains
the renamed body, as required at the generated call entry. -/
theorem singleEntry_compiled_code_lookup {σ : Type}
    (start : MlString) (body : ProgHOL 64) (source : PanSemStateFiniteExact 64 σ)
    (sourceCode : source.code = HolFiniteMapExact.empty.update
      (newMainNameHOL (singleEntryProgram start body),
        ([],fpermHOL start (newMainNameHOL (singleEntryProgram start body)) body,.one))) :
    ∀ function parameters program returnShape,
      source.code.lookup function = some (parameters,program,returnShape) →
      (HolFiniteMapExact.empty.updateList
        (functionsHOL (compileTopExactHOL (singleEntryProgram start body) start)).reverse).lookup function =
          some (parameters,compileProgExactHOL emptyGlobalsContext program,returnShape) := by
  intro function parameters program returnShape found
  rw [sourceCode] at found
  simp only [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.lookup_empty] at found
  split at found
  · rename_i eq
    simp only [Option.some.injEq,Prod.mk.injEq] at found
    rcases found with ⟨rfl,rfl,rfl⟩
    have same : newMainNameHOL (singleEntryProgram start body) = function := by simpa using eq
    subst function
    have fresh : newMainNameHOL (singleEntryProgram start body) ≠ start := by
      intro same
      have notMem := PanGlobalsDeclListExact.freshNameMlS_correct (ofString "main")
        ((functionsHOL (singleEntryProgram start body)).map Prod.fst)
      apply notMem
      simpa [newMainNameHOL,singleEntryProgram,functionsHOL] using same
    rw [singleEntry_compileTop]
    simp [functionsHOL,HolFiniteMapExact.lookup_updateList,FUPDATE_LIST,FUPDATE,Ne.symm fresh]
  · simp at found


/-- Global lowering of a single function has no initialization or global
context, with the callee body compiled in the empty context. -/
theorem singleEntry_globalLowered (start : MlString) (body : ProgHOL 64) :
    let declarations := singleEntryProgram start body
    let renamed := newMainNameHOL declarations
    globalLoweredDecs declarations start =
      ([],[.function ⟨renamed,false,false,[],
        compileProgExactHOL emptyGlobalsContext (fpermHOL start renamed body),.one⟩],[],emptyGlobalsContext) := by
  simp [globalLoweredDecs,singleEntryProgram,resortDeclsHOL,isNameHOL,isExnDeclHOL,
    isDeclHOL,isFunctionHOL,List.filter,fpermDecsHOL,fpermName,compileDecsExactHOL,
    decShapesHOL,emptyGlobalsContext]

/-- The actual code table meets the source-first machine theorem's globals
lookup premise for every declared assignment loop of the supported shape. -/
theorem singleEntry_declared_code_lookup {σ : Type}
    (start name : MlString) (initial returned : BitVec 64)
    (condition assignment : ExpHOL 64) (source : PanSemStateFiniteExact 64 σ)
    (sourceCode : source.code = HolFiniteMapExact.empty.update
      (newMainNameHOL (singleEntryProgram start (.dec name .one (.const initial) (.seq .skip
        (.seq (.while condition (.assign .local name assignment)) (.return (.const returned)))))),
      ([],.dec name .one (.const initial) (.seq .skip
        (.seq (.while condition (.assign .local name assignment)) (.return (.const returned)))),.one))) :
    ∀ function parameters program returnShape,
      source.code.lookup function = some (parameters,program,returnShape) →
      (HolFiniteMapExact.empty.updateList
        (functionsHOL (compileTopExactHOL (singleEntryProgram start (.dec name .one (.const initial) (.seq .skip
          (.seq (.while condition (.assign .local name assignment)) (.return (.const returned)))))) start)).reverse).lookup function =
          some (parameters,compileProgExactHOL emptyGlobalsContext program,returnShape) := by
  apply singleEntry_compiled_code_lookup
  simpa only [declaredAssignLoop_fperm] using sourceCode


/-- The actual singleton compiled program contributes no exception IDs to
the frontend compiler context. -/
theorem singleEntry_compiled_eids_empty (start : MlString) (body : ProgHOL 64) :
    getEidsFromDeclsHOL (compileTopExactHOL (singleEntryProgram start body) start) =
      HolFiniteMapExact.empty := by
  apply HolFiniteMapExact.ext_lookup
  intro key
  rw [singleEntry_compileTop]
  simp [getEidsFromDeclsHOL,getEidsEntriesHOL,exceptionsHOL,HolFiniteMapExact.lookup_empty,
    Flapjack.alistToFmap,FEMPTY]


/-- Fresh renaming makes the actual compiled Crep function names distinct. -/
theorem singleEntry_compiled_names_unique (start : MlString) (body : ProgHOL 64) :
    ((compileProgDeclsHOLW (compileTopExactHOL (singleEntryProgram start body) start)).map Prod.fst).Nodup := by
  apply panToCrepFirstCompileProgAllDistinctExact
  have fresh : newMainNameHOL (singleEntryProgram start body) ≠ start := by
    intro equal
    have notMem := PanGlobalsDeclListExact.freshNameMlS_correct (ofString "main")
      ((functionsHOL (singleEntryProgram start body)).map Prod.fst)
    apply notMem
    simpa [newMainNameHOL,singleEntryProgram,functionsHOL] using equal
  rw [singleEntry_compileTop]
  simp [functionsHOL,Ne.symm fresh]

/-- Both generated functions are explicitly marked non-inline. -/
theorem singleEntry_inline_selection_empty (start : MlString) (body : ProgHOL 64) :
    (functionsHOL ((compileTopExactHOL (singleEntryProgram start body) start).filter inlinableHOL)).map Prod.fst = [] := by
  rw [singleEntry_compileTop]
  simp [List.filter,inlinableHOL,functionsHOL]


/-- Supported scalar expressions contain no global variables. -/
theorem scalarExpression_localised {width : Nat} [NeZero width]
    {ctxt : PanToCrepContextExact width} {e : ExpHOL width}
    (shape : ScalarExpression ctxt e) : localisedExpHOL e = true := by
  induction shape <;> simp_all [localisedExpHOL,everyExpHOL,everyExpListHOL]


/-- The actual generated functions are localized whenever the loop's two
expressions have the supported scalar shape. -/
theorem singleEntry_declared_localised (start name : MlString) (initial returned : BitVec 64)
    (condition assignment : ExpHOL 64) (ctxt : PanToCrepContextExact 64)
    (conditionShape : ScalarExpression ctxt condition) (assignmentShape : ScalarExpression ctxt assignment) :
    ∀ entry ∈ functionsHOL (compileTopExactHOL
      (singleEntryProgram start (.dec name .one (.const initial) (.seq .skip
        (.seq (.while condition (.assign .local name assignment)) (.return (.const returned)))))) start),
      localisedProgHOL entry.2.2.1 = true := by
  have hc := scalarExpression_localised (globalCompile_scalar_shape emptyGlobalsContext conditionShape)
  have ha := scalarExpression_localised (globalCompile_scalar_shape emptyGlobalsContext assignmentShape)
  rw [singleEntry_compileTop]
  simp [functionsHOL,declaredAssignLoop_fperm,compileProgExactHOL,compileExpExactHOL,localisedProgHOL,
    localisedExpHOL,everyExpHOL,everyExpListHOL] at hc ha ⊢
  exact ⟨hc,ha⟩

/-- Function renaming preserves an unprefixed declaration-wrapped assignment loop. -/
theorem declaredWhileAssignLoop_fperm (start renamed name : MlString) (initial returned : BitVec 64)
    (condition assignment : ExpHOL 64) :
    fpermHOL start renamed (.dec name .one (.const initial)
      (.seq (.while condition (.assign .local name assignment)) (.return (.const returned)))) =
      .dec name .one (.const initial)
        (.seq (.while condition (.assign .local name assignment)) (.return (.const returned))) := by
  simp [fpermHOL]

/-- The unprefixed singleton's actual generated functions are localized. -/
theorem singleEntry_declaredWhile_localised (start name : MlString) (initial returned : BitVec 64)
    (condition assignment : ExpHOL 64) (ctxt : PanToCrepContextExact 64)
    (conditionShape : ScalarExpression ctxt condition) (assignmentShape : ScalarExpression ctxt assignment) :
    ∀ entry ∈ functionsHOL (compileTopExactHOL
      (singleEntryProgram start (.dec name .one (.const initial)
        (.seq (.while condition (.assign .local name assignment)) (.return (.const returned))))) start),
      localisedProgHOL entry.2.2.1 = true := by
  have hc := scalarExpression_localised (globalCompile_scalar_shape emptyGlobalsContext conditionShape)
  have ha := scalarExpression_localised (globalCompile_scalar_shape emptyGlobalsContext assignmentShape)
  rw [singleEntry_compileTop]
  simp [functionsHOL,declaredWhileAssignLoop_fperm,compileProgExactHOL,compileExpExactHOL,localisedProgHOL,
    localisedExpHOL,everyExpHOL,everyExpListHOL] at hc ha ⊢
  exact ⟨hc,ha⟩

/-- Struct lowering preserves every supported scalar expression. -/
theorem scalarExpression_structs_fixed {width : Nat} [NeZero width]
    {ctxt : PanToCrepContextExact width} {e : ExpHOL width} (shape : ScalarExpression ctxt e)
    (structCtxt : Pancake.PanStructs.CompileShapeExact.ContextExact) :
    Pancake.PanStructs.CompileShapeExact.compileExpExact structCtxt e = e := by
  induction shape with
  | const v => simp [Pancake.PanStructs.CompileShapeExact.compileExpExact]
  | «local» name n found => simp [Pancake.PanStructs.CompileShapeExact.compileExpExact]
  | baseAddr => simp [Pancake.PanStructs.CompileShapeExact.compileExpExact]
  | topAddr => simp [Pancake.PanStructs.CompileShapeExact.compileExpExact]
  | bytesInWord => simp [Pancake.PanStructs.CompileShapeExact.compileExpExact]
  | shift op ha hb iha ihb => simp [Pancake.PanStructs.CompileShapeExact.compileExpExact,iha,ihb]
  | op operator ha hb iha ihb =>
    simp [Pancake.PanStructs.CompileShapeExact.compileExpExact,
      Pancake.PanStructs.CompileShapeExact.compileExpsExact,iha,ihb]

/-- Both pre-global passes preserve a supported scalar assignment loop, apart
from removing its leading skip. -/
theorem singleEntry_declaredWhile_panToWord (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (name : MlString) (initial returned : BitVec 64) (condition assignment : ExpHOL 64)
    (ctxt : PanToCrepContextExact 64) (conditionShape : ScalarExpression ctxt condition)
    (assignmentShape : ScalarExpression ctxt assignment) :
    let start := ofString "main"
    let body : ProgHOL 64 := .dec name .one (.const initial)
      (.seq (.while condition (.assign .local name assignment)) (.return (.const returned)))
    panToWordCompileProgHOL arch (singleEntryProgram start (.dec name .one (.const initial) (.seq .skip
      (.seq (.while condition (.assign .local name assignment)) (.return (.const returned)))))) =
      loopToWordCompileHOL (compileProgHOLExact arch
        (compileProgDeclsHOLW (compileTopExactHOL (singleEntryProgram start body) start))) := by
  simp only [panToWordCompileProgHOL,singleEntry_declared_panSimp]
  have fixed : Pancake.PanStructs.CompileShapeExact.compileTopExact
      (singleEntryProgram (ofString "main") (.dec name .one (.const initial)
        (.seq (.while condition (.assign .local name assignment)) (.return (.const returned))))) =
      singleEntryProgram (ofString "main") (.dec name .one (.const initial)
        (.seq (.while condition (.assign .local name assignment)) (.return (.const returned)))) := by
    simp [singleEntryProgram,Pancake.PanStructs.CompileShapeExact.compileTopExact,
      Pancake.PanStructs.CompileShapeExact.getNamesExact,Pancake.PanStructs.CompileShapeExact.compileDeclsExact,
      Pancake.PanStructs.CompileShapeExact.compileProgExact,Pancake.PanStructs.CompileShapeExact.compileShapeExact,
      Pancake.PanStructs.CompileShapeExact.compileExpExact,scalarExpression_structs_fixed conditionShape,scalarExpression_structs_fixed assignmentShape]
  rw [fixed]

end SteppedFlapjack.PanToCrepSteps
