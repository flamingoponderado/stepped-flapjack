import SteppedFlapjack.Concrete.SimpSupported
import SteppedFlapjack.Concrete.FrontendState
import Flapjack.Pancake.Proofs.PanSimp.CompileCorrect
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString SteppedFlapjack.PanToCrepSteps

theorem entryName_body_independent (a b : ProgHOL 64) : entryName a = entryName b := by
  simp [entryName,newMainNameHOL,singleEntryProgram,functionsHOL]

def panSimpSourceState {σ : Type} (program : Prog (RiscV.Word 64)) (source : PanSemStateFiniteExact 64 σ) :=
  {source with code := HolFiniteMapExact.empty.update (entryName (progToHOL (panSimpProg program)),([],progToHOL (panSimpProg program),.one))}

theorem supported_panSimp_state_rel {σ : Type} (program : Prog (RiscV.Word 64)) (supported : Supported program)
 (source : PanSemStateFiniteExact 64 σ)
 (sourceCode : source.code = HolFiniteMapExact.empty.update (entryName (progToHOL program),([],progToHOL program,.one))) :
 PanSimp.stateRel source (panSimpSourceState program source) (panSimpSourceState program source).code := by
  have sameName := entryName_body_independent (progToHOL (panSimpProg program)) (progToHOL program)
  have comp := (supported_panSimp program supported).2
  constructor
  · rfl
  · constructor
    · intro f absent
      simp only [sourceCode,HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.lookup_empty] at absent
      simp only [panSimpSourceState,HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.lookup_empty,sameName]
      split <;> simp_all
    · intro f params body shape found
      simp only [sourceCode,HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.lookup_empty] at found
      simp only [panSimpSourceState,HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.lookup_empty,sameName]
      split at found
      · rename_i eq
        simp only [Option.some.injEq,Prod.mk.injEq] at found
        rcases found with ⟨rfl,rfl,rfl⟩
        simp [eq,comp]
      · simp at found

theorem supported_panSimp_run {σ : Type} (program : Prog (RiscV.Word 64)) (supported : Supported program)
 (source sourceFinal : PanSemStateFiniteExact 64 σ) (result : Option (PanSemResultExact 64))
 (sourceCode : source.code = HolFiniteMapExact.empty.update (entryName (progToHOL program),([],progToHOL program,.one)))
 (run : source.evaluateHOLFiniteState (progToHOL program) = (result,sourceFinal)) (nonerror : result ≠ some .error) :
 ∃ final, (panSimpSourceState program source).evaluateHOLFiniteState (progToHOL (panSimpProg program)) = (result,final) ∧
   PanSimp.stateRel sourceFinal final final.code := by
  have relation := supported_panSimp_state_rel program supported source sourceCode
  have result := PanSimp.compileCorrectHOL (progToHOL program) source result sourceFinal (panSimpSourceState program source)
    ⟨run,nonerror,relation⟩
  simpa only [supported_seqAssocHOL program supported] using result

/-- The actual declaration-level simplifier installs exactly the supported
simplified singleton body used by the later compiler passes. -/
theorem supported_panSimp_declarations (program : Prog (RiscV.Word 64)) (supported : Supported program) :
    panSimpDeclsHOL (declarations (progToHOL program)) =
      declarations (progToHOL (panSimpProg program)) := by
  simp [declarations,singleEntryProgram,panSimpDeclsHOL,(supported_panSimp program supported).2]

end SteppedFlapjack.Concrete
