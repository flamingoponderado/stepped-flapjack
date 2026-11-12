import SteppedFlapjack.Concrete.GlobalStructWitness
import SteppedFlapjack.Concrete.Phase7SourceBehaviour
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString

def globalStructDeclared : PanSemStateFiniteExact 64 Unit :=
  {globalStructHOL with code := HolFiniteMapExact.empty.update (ofString "main",([],progToHOL globalStructWitness,.one))}

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
  have code : globalStructDeclared.code.lookup (ofString "main") = some ([],progToHOL globalStructWitness,.one) := by
    simp [globalStructDeclared,globalStructHOL,globalStructBase,sourceTemplate,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have lookup : lookupCodeHOLFinite globalStructDeclared.code.lookup (ofString "main") [] =
      some (progToHOL globalStructWitness,HolFiniteMapExact.empty,.one) := by
    apply SemInitSupport.lookup_init
    exact code
  let final := (setGlobalHOLFinite (ofString "pair") (panValueToHOL (.rStruct [.word 7,.word 8])) globalStructDeclared).emptyLocalsHOLFinite
  have entry : callEntryStateHOLFinite {globalStructDeclared with clock := globalStructDeclared.clock+1} HolFiniteMapExact.empty = globalStructDeclared := by
    simp [callEntryStateHOLFinite,globalStructDeclared,globalStructHOL,globalStructBase,sourceTemplate,setGlobalHOLFinite]
  have callRun : evaluateHOLFiniteState {globalStructDeclared with clock := globalStructDeclared.clock+1} (.call none (ofString "main") []) =
      (some (.returned (.val (.word (8 : BitVec 64)))),emptyLocalsHOLFinite final) := by
    rw [evaluateHOLFiniteState_call]
    simp only [evalListHOLFinite,evalListHOLExact,lookup,show globalStructDeclared.clock+1 ≠ 0 by omega,↓reduceIte,entry,globalStruct_declared_run]
    simp [shapeOfHOLExact,shapeEqHOL,final,emptyLocalsHOLFinite]
  have behavior := source_semantics_of_return globalStructDeclared (emptyLocalsHOLFinite final) (ofString "main") (globalStructDeclared.clock+1) (.val (.word (8 : BitVec 64))) callRun
  have declarations : semanticsDecls globalStructBase (ofString "main") globalStructProgram = semantics globalStructDeclared (ofString "main") := by
    have names : decsStcnamesHOLExact [] globalStructProgram = some [] := by
      simp [globalStructProgram,globalStructDecl,decsStcnamesHOLExact]
    unfold semanticsDecls
    rw [names]
    simp only
    have initialEq : {globalStructBase with structs := []} = globalStructBase := by rfl
    rw [initialEq]
    have classicalRun : @evaluateDeclsHOLFinite 64 Unit _ globalStructBase
        (fun address => Classical.propDecidable (globalStructBase.memaddrs address)) globalStructProgram = some globalStructDeclared := by
      have decEq : (fun address => Classical.propDecidable (globalStructBase.memaddrs address)) =
          (inferInstance : DecidablePred globalStructBase.memaddrs) := by
        funext address
        exact Subsingleton.elim _ _
      rw [decEq]
      exact globalStruct_decls_run
    rw [classicalRun]
  rw [declarations]
  simpa [final,emptyLocalsHOLFinite,globalStructDeclared,globalStructHOL,globalStructBase,sourceTemplate,setGlobalHOLFinite] using behavior
end SteppedFlapjack.Concrete
