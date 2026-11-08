import SteppedFlapjack.CrepSteps.TailEntry
import SteppedFlapjack.Concrete.FrontendState
import SteppedFlapjack.Concrete.SupportedSpan
import SteppedFlapjack.Concrete.CrepCode
import SteppedFlapjack.Pancake.Semantics.PanSem.EvalExecutedCountedBridge

/-! Concrete countdown at the compiler-generated callee entry. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString SteppedFlapjack.PanToCrepSteps

def naturalCalleeContext (n : Nat) : PanToCrepContextExact 64 :=
  let caller := frontendContext (naturalCountdownHOL n)
  ctxtFcExactHOL caller.funcs caller.eids [] [] []

/-- The generated entry for the unprefixed countdown. -/
def naturalCrepEntry (n : Nat) : CrepProgHOL 64 :=
  .seq .skip (.call none (entryName (naturalCountdownHOL n)) [])

theorem naturalCrepEntry_generated (n : Nat) :
    (ofString "main",[],naturalCrepEntry n) ∈ crepPrograms (naturalCountdownHOL n) := by
  simpa [naturalCrepEntry] using generated_entry_member (naturalCountdownHOL n)

theorem countdown_simp_declarations (n : Nat) :
 panSimpDeclsHOL (declarations (countdownHOL n)) = declarations (naturalCountdownHOL n) := by
 simp [declarations,singleEntryProgram,panSimpDeclsHOL,panSimpCompileHOL,seqAssocHOL,smartSeqHOL,
   retToTailHOL,seqCallRetHOL,countdownHOL,naturalCountdownHOL,naturalCountdown,countdownBodyHOL,countdownBody,
   progToHOL,expToHOL,shapeToHOL]

theorem countdown_simp_program (n : Nat) : panSimpProg (countdown n) = naturalCountdown n := by
  simp [panSimpProg,retToTail,seqAssoc,smartSeq,seqCallRet,countdown,naturalCountdown,countdownBody]

theorem countdown_simp_source (n : Nat) :
  panSimpSourceState (countdown n) (exactState (countdownHOL n)) = exactState (naturalCountdownHOL n) := by
  simp [panSimpSourceState,countdown_simp_program,exactState,singleEntrySourceTemplate,
    naturalCountdownHOL]


theorem countdown_panSimp_crep_code (n : Nat) :
    compileProgDeclsHOLW (compileTopExactHOL (panSimpDeclsHOL (declarations (countdownHOL n))) (ofString "main")) =
      crepPrograms (naturalCountdownHOL n) := by
  rw [countdown_simp_declarations]
  rfl

end SteppedFlapjack.Concrete
