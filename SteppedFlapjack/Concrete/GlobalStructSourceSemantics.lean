import SteppedFlapjack.Concrete.GlobalStructCrep
import SteppedFlapjack.Concrete.Phase7SourceBehaviour
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString

def globalStructDeclared : PanSemStateFiniteExact 64 Unit :=
  {globalStructHOL with code := HolFiniteMapExact.empty.update (ofString "main",([],progToHOL globalStructWitness,.one))}

open SteppedFlapjack.PanToCrepSteps

theorem globalStruct_sourceTable : GlobalCallTable globalStructContext globalStructDeclared.code := by
  intro name values body locals shape found
  have raw := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some globalStructDeclared.code.lookup name values body locals shape found
  by_cases eq : name = ofString "main"
  · subst name
    cases values with
    | nil =>
      simp [lookupCodeHOLExact,globalStructDeclared,globalStructHOL,globalStructBase,sourceTemplate,setGlobalHOLFinite,
        HolFiniteMapExact.lookup_update,FUPDATE] at raw
      obtain ⟨rfl,_,_⟩ := raw
      exact ⟨globalStructCrepContext,.base globalStruct_sourceFrontend⟩
    | cons v vs =>
      simp [lookupCodeHOLExact,globalStructDeclared,globalStructHOL,globalStructBase,sourceTemplate,setGlobalHOLFinite,
        HolFiniteMapExact.lookup_update,FUPDATE] at raw
  · simp [lookupCodeHOLExact,globalStructDeclared,globalStructHOL,globalStructBase,sourceTemplate,setGlobalHOLFinite,
      HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.lookup_empty,Ne.symm eq] at raw

/-- The real main call is accepted by the source call fragment. -/
theorem globalStruct_sourceCall : GlobalCallFrontend globalStructContext globalStructCrepContext
    (.call none (ofString "main") []) := by
  exact .tail (by simp)

local instance : DecidablePred globalStructBase.memaddrs := by
  change DecidablePred globalStructSourceDomain
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem globalStruct_decls_run :
    evaluateDeclsHOLFinite globalStructBase globalStructProgram = some globalStructDeclared := by
  with_unfolding_all rfl

/-- Running main after declaration initialization returns the pair's second word. -/
theorem globalStruct_declared_run :
    globalStructDeclared.evaluateHOLFiniteState (progToHOL globalStructWitness) =
      (some (.returned (.val (.word (8 : BitVec 64)))),
        (setGlobalHOLFinite (ofString "pair") (panValueToHOL (.rStruct [.word 7,.word 8])) globalStructDeclared).emptyLocalsHOLFinite) := by
  simp [globalStructDeclared,globalStructWitness,progToHOL,expToHOL,evaluateHOLFiniteState_seq_line780,
      evaluateHOLFiniteState_assign,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,
      globalStructHOL,globalStructBase,sourceTemplate,setGlobalHOLFinite,setKvarHOLFinite,isValidValueHOLFinite,
      lookupKvarHOLExact,FUPDATE,shapeOfHOLExact,shapeEqHOL,shapeEqHOL.shapeEqListHOL,emptyLocalsHOLFinite]

theorem globalStruct_semantics :
    semanticsDecls globalStructBase (ofString "main") globalStructProgram = .terminate .success sourceFfi.ioEvents := by
  have names : decsStcnamesHOLExact [] globalStructProgram = some [] := by
    simp [globalStructProgram,globalStructDecl,decsStcnamesHOLExact]
  have classicalRun : @evaluateDeclsHOLFinite 64 Unit _ {globalStructBase with structs := []}
      (fun address => Classical.propDecidable (globalStructBase.memaddrs address)) globalStructProgram = some globalStructDeclared := by
    have decEq : (fun address => Classical.propDecidable (globalStructBase.memaddrs address)) =
        (inferInstance : DecidablePred globalStructBase.memaddrs) := by
      funext address
      exact Subsingleton.elim _ _
    rw [decEq]
    exact globalStruct_decls_run
  have code : globalStructDeclared.code.lookup (ofString "main") = some ([],progToHOL globalStructWitness,.one) := by
    simp [globalStructDeclared,globalStructHOL,globalStructBase,sourceTemplate,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  let final := (setGlobalHOLFinite (ofString "pair") (panValueToHOL (.rStruct [.word 7,.word 8])) globalStructDeclared).emptyLocalsHOLFinite
  have behavior := declaration_body_semantics globalStructBase globalStructDeclared globalStructProgram
    (ofString "main") (progToHOL globalStructWitness) [] names classicalRun (by rfl) code globalStructDeclared.clock
    final 8 (by simpa [final] using globalStruct_declared_run)
  simpa [final,emptyLocalsHOLFinite,globalStructDeclared,globalStructHOL,globalStructBase,sourceTemplate,setGlobalHOLFinite] using behavior

end SteppedFlapjack.Concrete
