import SteppedFlapjack.Concrete.SimpSupported
import SteppedFlapjack.Concrete.FrontendState
import SteppedFlapjack.Concrete.CodeIndependent
import Flapjack.Pancake.Proofs.PanSimp.CompileCorrect
import Flapjack.Pancake.Proofs.PanSimp.SeqAssocAssembly
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString SteppedFlapjack.PanToCrepSteps

theorem entryName_body_independent (a b : ProgHOL 64) : entryName a = entryName b := by
  simp [entryName,newMainNameHOL,singleEntryProgram,functionsHOL]

def panSimpSourceState {σ : Type} (program : Prog (RiscV.Word 64)) (source : PanSemStateFiniteExact 64 σ) :=
  {source with code := HolFiniteMapExact.empty.update (entryName (progToHOL (panSimpProg program)),([],progToHOL (panSimpProg program),.one))}

theorem supported_panSimp_state_rel {σ : Type} (program : Prog (RiscV.Word 64)) (supported : CallFreeSupported program)
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

/-- On the same source state, simplification preserves every supported run,
including errors, because the pass only reassociates sequences. -/
theorem supported_panSimp_same_state {σ : Type} (program : Prog (RiscV.Word 64)) (supported : CallFreeSupported program)
    (source : PanSemStateFiniteExact 64 σ) :
    source.evaluateHOLFiniteState (progToHOL (panSimpProg program)) = source.evaluateHOLFiniteState (progToHOL program) := by
  rw [← supported_seqAssocHOL program supported,evaluateSeqAssocHOL]
  rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_skip]
/-- Simplification preserves every supported result when its generated code
is installed, including errors, and updates only the final code table. -/
theorem supported_panSimp_run {σ : Type} (program : Prog (RiscV.Word 64)) (supported : CallFreeSupported program)
    (source sourceFinal : PanSemStateFiniteExact 64 σ) (result : Option (PanSemResultExact 64))
    (run : source.evaluateHOLFiniteState (progToHOL program) = (result,sourceFinal)) :
    (panSimpSourceState program source).evaluateHOLFiniteState (progToHOL (panSimpProg program)) =
      (result,{sourceFinal with code := (panSimpSourceState program source).code}) := by
  have shape := (supported_panSimp program supported).1
  have independent := supported_code_irrel shape source (panSimpSourceState program source).code
  have same := supported_panSimp_same_state program supported source
  rw [same,run] at independent
  exact independent

/-- The actual declaration-level simplifier installs exactly the supported
simplified singleton body used by the later compiler passes. -/
theorem supported_panSimp_declarations (program : Prog (RiscV.Word 64)) (supported : CallFreeSupported program) :
    panSimpDeclsHOL (declarations (progToHOL program)) =
      declarations (progToHOL (panSimpProg program)) := by
  simp [declarations,singleEntryProgram,panSimpDeclsHOL,(supported_panSimp program supported).2]

/-- With the entire function table related by pan_simp, every non-error run
of a call-aware body is preserved by the executable simplifier. -/
theorem callSupported_panSimp_run {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope program) {σ : Type}
    (source sourceFinal target : PanSemStateFiniteExact 64 σ) (result : Option (PanSemResultExact 64))
    (run : source.evaluateHOLFiniteState (progToHOL program) = (result,sourceFinal))
    (nonerror : result ≠ some .error) (rel : PanSimp.stateRel source target target.code) :
    ∃ targetFinal, target.evaluateHOLFiniteState (progToHOL (panSimpProg program)) = (result,targetFinal) ∧
      PanSimp.stateRel sourceFinal targetFinal targetFinal.code := by
  obtain ⟨targetFinal,targetRun,finalRel⟩ := PanSimp.compileCorrectHOL (progToHOL program)
    source result sourceFinal target ⟨run,nonerror,rel⟩
  rw [callSupported_seqAssocHOL supported] at targetRun
  exact ⟨targetFinal,targetRun,finalRel⟩

end SteppedFlapjack.Concrete
