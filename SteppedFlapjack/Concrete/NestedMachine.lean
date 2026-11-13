import SteppedFlapjack.Concrete.GeneratedMachine
import SteppedFlapjack.Concrete.NestedCrepLoop
import SteppedFlapjack.LoopToWordSteps.WholeCallProgram
import SteppedFlapjack.WordSimpSteps.LoopSequenceClock
import Flapjack.Pancake.LoopToWord.Proofs.NoInstallCode
import SteppedFlapjack.Concrete.WordSpan
import SteppedFlapjack.Concrete.SourceState
import SteppedFlapjack.Concrete.FixtureWordStarter
import SteppedFlapjack.Concrete.CountdownWordSpan
import SteppedFlapjack.Concrete.FixtureMachineGuards
import SteppedFlapjack.WordToStackSteps.StartRiscV
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordToWord
open Flapjack.WordToStackProofs Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordToStackSteps
open SteppedFlapjack.StackSteps SteppedFlapjack.WordSimpSteps Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.WordDepth.Executable
open Flapjack.Compiler.Backend.BackendProps

/-- Executable Word table and entry frame for the nested-call witness. -/
def nestedRawWords := loopToWordCompileHOL (compileProgHOLExact riscvConfig.isa nestedCallCrepPrograms)
def nestedOptimizedWords := (compileWith Flapjack.RegAlloc.regAllocExecutable phase3WordConfig riscvConfig nestedRawWords).2
def nestedEntry : WordLangProgHOL (BitVec 64) :=
  ((sptLookup 64 (sptFromAList nestedOptimizedWords)).getD (1,.skip)).2
def nestedEntryFrame : Nat :=
  (compileProgNative riscvConfig false nestedEntry 1 (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1

/-- Native Stack code and bitmaps computed from the actual optimized table. -/
def nestedNative := compileNative riscvConfig false nestedOptimizedWords
def nestedCode : List (Nat × HolProg 64) := nestedNative.2.2.2
def nestedBitmaps : List (BitVec 64) := nestedNative.1
/-- Native frame-size table computed from the actual optimized functions. -/
def nestedFrameSizes : Spt Nat :=
  sptMapi (fun _ (argc,body) =>
    (compileProgNative riscvConfig false body argc (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (.nil,0)).2.1)
    (sptFromAList nestedOptimizedWords)

end SteppedFlapjack.Concrete
