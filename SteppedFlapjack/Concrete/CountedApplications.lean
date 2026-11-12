import SteppedFlapjack.Concrete.CountedSpan
import SteppedFlapjack.Concrete.CrepCountdown
import SteppedFlapjack.Concrete.CrepBranch
import SteppedFlapjack.Concrete.BranchingLoop
/-! The general counted span instantiated for the phase-zero witnesses.
The fixture clocks are the explicit source step budgets, so each target bound
is calculated from that budget and the actual generated Crep body. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact SteppedFlapjack.PanToCrepSteps

def clockedFixtureSource (program : Prog (RiscV.Word 64)) (n : Nat) :=
  {(exactState (progToHOL program)) with clock := n}
def clockedFixtureProduction (program : Prog (RiscV.Word 64)) (n : Nat) :=
  {(executableState (progToHOL program)) with clock := n}

/-- The clocked fixture satisfies the source relation and scalar-local
premises uniformly for any supported source body. -/
theorem clockedFixture_premises (program : Prog (RiscV.Word 64)) (n : Nat) :
    PanSemStateRelExec (clockedFixtureProduction program n) (clockedFixtureSource program n).toExact ∧
    PanSemStateRelExecRanged (clockedFixtureProduction program n) ∧
    WordLocals (clockedFixtureProduction program n).locals := by
  constructor
  · obtain ⟨a,b,c,d,e,f,g,h,_,j,k,l,m⟩ := source_related (progToHOL program)
    exact ⟨a,b,c,d,e,f,g,h,rfl,j,k,l,m⟩
  constructor
  · exact PanSemStateRelExecRanged.setClock (source_ranged (progToHOL program)) n
  · intro name value found
    simp [clockedFixtureProduction,executableState,singleEntrySourceProduction,sourceProduction] at found

end SteppedFlapjack.Concrete
