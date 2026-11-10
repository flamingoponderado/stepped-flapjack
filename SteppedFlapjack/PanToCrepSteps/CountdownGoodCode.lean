import SteppedFlapjack.PanToCrepSteps.SingleEntryGlobals
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyGoodCodeSource

/-! Source-derived Lab code validity for the actual compiled countdown. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.BackendProof Flapjack.Compiler.Backend.LabToTarget

/-- The original countdown has valid Pancake operations. -/
theorem countdown_pancakeGoodCode (name : MlString) (initial returned : BitVec 64) :
    pancakeGoodCodeHOL (singleEntryProgram (ofString "main")
      (.dec name .one (.const initial) (.seq .skip (.seq
        (.while (.var .local name) (.assign .local name (.op .sub [.var .local name,.const 1])))
        (.return (.const returned)))))) = true := by
  simp [pancakeGoodCodeHOL,singleEntryProgram,goodPanopsHOL,expsOfHOL,everyExpListHOL,everyExpHOL,panopArityTwoHOL]

end SteppedFlapjack.PanToCrepSteps
