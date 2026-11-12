import SteppedFlapjack.LoopToWordSteps.WholeCallProgram
import SteppedFlapjack.Concrete.NestedCrepLoop
import SteppedFlapjack.WordSimpSteps.LoopSequenceClock
import Flapjack.Pancake.LoopToWord.Proofs.NoInstallCode
/-! Bottom-up execution of the actual optimized Loop witness. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang SteppedFlapjack.PanToCrepSteps
open Flapjack.LoopSemStateFiniteExact Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps SteppedFlapjack.LoopLiveSteps
def nestedPanContext := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL
  (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main")))) 0
  (getEidsFromDeclsHOL (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main")))
def nestedLoopContext := mkCtxtExact riscvConfig.isa (makeVmapExact [])
  (crepToLoopMakeFuncsExactExecutable nestedCallCrepPrograms) 0
def nestedCrepBody : CrepProgHOL 64 := compileProgExactHOLW nestedPanContext (.seq .skip (.call none (ofString "main'") []))
def nestedCrepLimit := 4 * nestedSourceEntryLimit
def nestedLoopBudget := callClockFactor nestedLoopContext
  (nestedCallCrepPrograms.map (fun row => (row.2.1,row.2.2))) 7 nestedCrepBody * (nestedCrepLimit + 1)
def nestedLoopBound := callSyntaxCost nestedLoopContext nestedCrepBody +
  max (callSyntaxCost nestedLoopContext nestedCrepBody) (loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa nestedCallCrepPrograms))+2) * (7+nestedLoopBudget)
def nestedOptimizedLoopBody := optimiseHOL (compileHOLExact nestedLoopContext .ln nestedCrepBody)
def nestedOptimizedLoopBound :=
  loopVisitWeight nestedOptimizedLoopBody +
    max (loopVisitWeight nestedOptimizedLoopBody)
      (loopCodeWeight (sptFromAList (compileProgHOLExact riscvConfig.isa nestedCallCrepPrograms)) + 2) * (2 * nestedLoopBound)

end SteppedFlapjack.Concrete
