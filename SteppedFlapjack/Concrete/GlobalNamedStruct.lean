import SteppedFlapjack.Concrete.GlobalStructSourceSemantics
import Flapjack.Pancake.Proofs.PanStructs.CompileTopSemanticsDeclsExact
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.Pancake.PanStructs.CompileShapeExact

def namedGlobalStructWitness : Prog (RiscV.Word 64) :=
  .seq (.assign .global "pair" (.nStruct "Pair" [("first",.const 7),("second",.const 8)]))
    (.return (.nField "second" (.var .global "pair")))

def namedGlobalStructBody : ProgHOL 64 := progToHOL namedGlobalStructWitness

def namedGlobalStructProgram : List (DeclHOL 64) :=
  [.name (ofString "Pair") [(ofString "first",.one),(ofString "second",.one)],
   .decl (.named (ofString "Pair")) (ofString "pair")
     (.nstruct (ofString "Pair") [(ofString "first",.const 0),(ofString "second",.const 0)]),
   .function ⟨ofString "main",false,false,[],namedGlobalStructBody,.one⟩]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem namedGlobalStruct_compile : compileTopExact namedGlobalStructProgram = globalStructProgram := by
  have namesNe : ofString "second" ≠ ofString "first" := by decide
  simp [namedGlobalStructProgram,namedGlobalStructBody,namedGlobalStructWitness,globalStructProgram,globalStructDecl,globalStructWitness,
    compileTopExact,getNamesExact,compileDeclsExact,compileProgExact,compileExpExact,compileFieldsExact,
    compileShapeExact,oldExpShapeExact,progToHOL,expToHOL,Flapjack.afindi,List.dropWhile,List.findSome?,namesNe,Ne.symm namesNe]
  split <;> simp_all
  rename_i fields h
  obtain ⟨_,rfl⟩ := h
  obtain ⟨_,hf⟩ := ‹_ ∧ _›
  rw [← hf]
  simp [compileShapesExact,compileShapeExact]

theorem namedGlobalStruct_ranged : ProgByteRanged namedGlobalStructWitness := by
  simp [namedGlobalStructWitness,ProgByteRanged,ExpByteRanged,NameRanged,ListFieldByteRanged]

def namedGlobalStructInitial : PanSemState (RiscV.Word 64) (FfiState Unit) :=
  {globalStructInitial with structs := [("Pair",⟨[("first",.one),("second",.one)],2,[]⟩)], globals := updatePanValueMap sourceProduction.globals "pair" (.nStruct "Pair" [("first",.word 0),("second",.word 0)])}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem namedGlobalStruct_run :
    evalPanValueFfiProgSteps (riscv64PanValueFfiContext (fun _ => false))
      (fun _ _ => none) (fun _ _ _ _ _ _ _ => none) namedGlobalStructInitial.structs []
      namedGlobalStructInitial.baseAddress namedGlobalStructInitial.topAddress 8 10
      namedGlobalStructInitial.locals namedGlobalStructInitial.globals namedGlobalStructInitial.memory namedGlobalStructInitial.ffi namedGlobalStructWitness
      (memoryAccess := some (panSemBitVec64MemoryAccess namedGlobalStructInitial)) (contracts := none) =
        some (.returned namedGlobalStructInitial.locals
          (updatePanValueMap namedGlobalStructInitial.globals "pair" (.nStruct "Pair" [("first",.word 7),("second",.word 8)]))
          namedGlobalStructInitial.memory namedGlobalStructInitial.ffi [.word 8],8) := by
  with_unfolding_all rfl

def namedStructInfo : StructInfoHOLExact := ⟨[(ofString "first",.one),(ofString "second",.one)],2⟩
def namedStructContext : StructContextExact := [(ofString "Pair",namedStructInfo)]
def namedStructBase : PanSemStateFiniteExact 64 Unit := {globalStructBase with structs := namedStructContext}
def namedStructHOL : PanSemStateFiniteExact 64 Unit :=
  setGlobalHOLFinite (ofString "pair") (.nStruct (ofString "Pair") [(ofString "first",.val (.word 0)),(ofString "second",.val (.word 0))]) namedStructBase

theorem namedGlobalStruct_hol : ∃ final,
    namedStructHOL.evaluateHOLFiniteState namedGlobalStructBody =
      (some (.returned (.val (.word 8))),final) := by
  refine ⟨(setGlobalHOLFinite (ofString "pair") (.nStruct (ofString "Pair") [(ofString "first",.val (.word 7)),(ofString "second",.val (.word 8))]) namedStructHOL).emptyLocalsHOLFinite,?_⟩
  have namesNe : ofString "second" ≠ ofString "first" := by decide
  simp [namedGlobalStructBody,namedGlobalStructWitness,progToHOL,expToHOL,evaluateHOLFiniteState_seq_line780,
    evaluateHOLFiniteState_assign,evaluateHOLFiniteState_return,evalHOLExact,evalListFieldsHOLExact,
    namedStructHOL,namedStructBase,namedStructContext,namedStructInfo,globalStructBase,sourceTemplate,
    setGlobalHOLFinite,setKvarHOLFinite,isValidValueHOLFinite,lookupKvarHOLExact,FUPDATE,
    structContextLookupHOL,lookupFieldHOL,shapeOfHOLExact,shapeEqHOL,
    emptyLocalsHOLFinite,Ne.symm namesNe]

def namedStructDeclared : PanSemStateFiniteExact 64 Unit :=
  {namedStructHOL with code := HolFiniteMapExact.empty.update (ofString "main",([],namedGlobalStructBody,.one))}

local instance : DecidablePred namedStructBase.memaddrs := by
  change DecidablePred globalStructSourceDomain
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem namedGlobalStruct_decls_run :
    evaluateDeclsHOLFinite namedStructBase namedGlobalStructProgram = some namedStructDeclared := by
  with_unfolding_all rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem namedGlobalStruct_names :
    decsStcnamesHOLExact [] namedGlobalStructProgram = some namedStructContext := by
  with_unfolding_all rfl

theorem namedGlobalStruct_declared_run :
    namedStructDeclared.evaluateHOLFiniteState namedGlobalStructBody =
      (some (.returned (.val (.word (8 : BitVec 64)))),
        (setGlobalHOLFinite (ofString "pair") (.nStruct (ofString "Pair") [(ofString "first",.val (.word 7)),(ofString "second",.val (.word 8))]) namedStructDeclared).emptyLocalsHOLFinite) := by
  have namesNe : ofString "second" ≠ ofString "first" := by decide
  simp [namedStructDeclared,namedGlobalStructBody,namedGlobalStructWitness,progToHOL,expToHOL,evaluateHOLFiniteState_seq_line780,
    evaluateHOLFiniteState_assign,evaluateHOLFiniteState_return,evalHOLExact,evalListFieldsHOLExact,
    namedStructHOL,namedStructBase,namedStructContext,namedStructInfo,globalStructBase,sourceTemplate,
    setGlobalHOLFinite,setKvarHOLFinite,isValidValueHOLFinite,lookupKvarHOLExact,FUPDATE,
    structContextLookupHOL,lookupFieldHOL,shapeOfHOLExact,shapeEqHOL,
    emptyLocalsHOLFinite,Ne.symm namesNe]

/-- The named source declaration initializes its global and terminates. -/
theorem namedGlobalStruct_semantics :
    semanticsDecls globalStructBase (ofString "main") namedGlobalStructProgram = .terminate .success sourceFfi.ioEvents := by
  have classicalRun : @evaluateDeclsHOLFinite 64 Unit _ {globalStructBase with structs := namedStructContext}
      (fun address => Classical.propDecidable (globalStructBase.memaddrs address)) namedGlobalStructProgram = some namedStructDeclared := by
    have decEq : (fun address => Classical.propDecidable (globalStructBase.memaddrs address)) =
        (inferInstance : DecidablePred namedStructBase.memaddrs) := by
      funext address
      exact Subsingleton.elim _ _
    rw [decEq]
    exact namedGlobalStruct_decls_run
  have code : namedStructDeclared.code.lookup (ofString "main") = some ([],namedGlobalStructBody,.one) := by
    simp [namedStructDeclared,namedStructHOL,namedStructBase,globalStructBase,sourceTemplate,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  let final := (setGlobalHOLFinite (ofString "pair") (.nStruct (ofString "Pair") [(ofString "first",.val (.word 7)),(ofString "second",.val (.word 8))]) namedStructDeclared).emptyLocalsHOLFinite
  have behavior := declaration_body_semantics globalStructBase namedStructDeclared namedGlobalStructProgram
    (ofString "main") namedGlobalStructBody namedStructContext namedGlobalStruct_names classicalRun (by rfl) code
    namedStructDeclared.clock final 8 (by simpa [final] using namedGlobalStruct_declared_run)
  simpa [final,emptyLocalsHOLFinite,namedStructDeclared,namedStructHOL,namedStructBase,globalStructBase,sourceTemplate,setGlobalHOLFinite] using behavior

/-- Source simplification retains the concrete named-pair declarations. -/
theorem namedGlobalStruct_simp_fixed : panSimpDeclsHOL namedGlobalStructProgram = namedGlobalStructProgram := by
  simp [namedGlobalStructProgram,namedGlobalStructBody,namedGlobalStructWitness,progToHOL,expToHOL,
    panSimpDeclsHOL,panSimpCompileHOL,seqAssocHOL,smartSeqHOL,retToTailHOL,seqCallRetHOL]

/-- Struct compilation preserves the named program's source behavior. -/
theorem namedGlobalStruct_struct_semantics :
    semanticsDecls globalStructBase (ofString "main") namedGlobalStructProgram =
      semanticsDecls globalStructBase (ofString "main") globalStructProgram := by
  have good : semanticsDecls globalStructBase (ofString "main") namedGlobalStructProgram ≠ .fail := by
    rw [namedGlobalStruct_semantics]
    simp
  have h := Flapjack.Pancake.Proofs.PanStructs.CompileTopSemanticsDeclsExact.compileTopSemanticsDeclsExact globalStructBase (ofString "main") namedGlobalStructProgram
    ⟨good,rfl,rfl,rfl⟩
  simpa [namedGlobalStruct_compile,globalStructBase,sourceTemplate,HolFiniteMapExact.map2,HolFiniteMapExact.empty] using h

/-- The actual simplifier-then-struct compiler pipeline produces the pair program. -/
theorem namedGlobalStruct_pipeline :
    compileTopExact (panSimpDeclsHOL namedGlobalStructProgram) = globalStructProgram := by
  rw [namedGlobalStruct_simp_fixed,namedGlobalStruct_compile]
end SteppedFlapjack.Concrete
