import SteppedFlapjack.PanToCrepSteps.AssignLoopEntryDefs
import SteppedFlapjack.PanToCrepSteps.CountedAssignLoopReturn
import SteppedFlapjack.PanToCrepSteps.TailEntryCrepBound
import SteppedFlapjack.PanToCrepSteps.TailEntryRelations
import SteppedFlapjack.CrepToLoopSteps.RiscVInputs
import SteppedFlapjack.LoopToWordSteps.TailRiscVSetup
import SteppedFlapjack.WordToStackSteps.TailEntryFrame
import SteppedFlapjack.PanToCrepSteps.GlobalSourceEntry
import SteppedFlapjack.LoopToWordSteps.TailRiscVClock
import SteppedFlapjack.CrepToLoopSteps.WholeInitialRelations
import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GcFunConstOk
import SteppedFlapjack.LoopToWordSteps.Outcome
import SteppedFlapjack.WordToStackSteps.DirectTailRiscV
import SteppedFlapjack.WordAllocSteps.WholeTailCode
import Flapjack.Pancake.LoopToWord.Proofs.LabPres
import Flapjack.Pancake.CrepToLoop.Proofs.MakeFuncsLemmas
import SteppedFlapjack.PanToCrepSteps.GlobalTailWord
import SteppedFlapjack.PanToCrepSteps.GlobalPanCodeRel

/-! Native initialization for the counted assignment-loop entry. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.LabToTargetSteps

/-- Whole-compiler and native-machine inputs for a zero-argument Loop entry.
The frame, Word state, code relations, and resource outcome are derived. -/
structure AssignLoopCompilerInputs {F : Type}
    (declarations : List (DeclHOL 64)) (start : MlString) (caller : PanToCrepContextExact 64)
    (loopCtxt : CrepToLoopContextExact) (entry : HolLoopProg 64) (limit : Nat)
    (loop : LoopSemStateFiniteExact 64 F) where
  arch : AsmArchitecture
  crepPrograms : List (MlString × List Nat × CrepProgHOL 64)
  programsEq : crepPrograms = compileProgDeclsHOLW (compileTopExactHOL declarations start)
  callerEq : caller = mkCtxtExactHOL (panToCrepMakeVmapHOLExact [])
    (makeFuncsExactHOL (functionsHOL (compileTopExactHOL declarations start))) (sizeOfShapeHOL (.comb [])-1)
    (getEidsFromDeclsHOL (compileTopExactHOL declarations start))
  loopContextEq : loopCtxt = mkCtxtExact arch (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable crepPrograms) 0
  wc : Flapjack.Compiler.Backend.WordToWord.Config
  ac : AsmConfigExact 64
  loopCode : loop.code = sptFromAList (compileProgHOLExact arch crepPrograms)
  stack : StackSemStateFiniteExact 64 LabToTarget.Config F
  coracle : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64))
  codeEq : stack.code = sptFromAList (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
    (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))).2).2.2.2
  bitmapsPrefix : (Flapjack.Compiler.Backend.WordToStack.Native.compileNative ac false
    (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))).2).1.IsPrefix stack.bitmaps
  ok : Flapjack.WordToStackProofs.InitializationStateRel.initStateOk ac (ac.regCount-(5+ac.avoidRegs.length)) stack coracle
  data : LoopWordDataRel loop
    {callEnv [(.loc 1 0 : WordLocW 64)] (some 0)
      (Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit ac (ac.regCount-(5+ac.avoidRegs.length)) stack
        (sptFromAList (compile wc ac (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))).2) coracle)
      with code := sptFromAList (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))}

end SteppedFlapjack.PanToCrepSteps
