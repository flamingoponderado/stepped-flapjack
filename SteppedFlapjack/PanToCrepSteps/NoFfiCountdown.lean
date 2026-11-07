import SteppedFlapjack.PanToCrepSteps.RiscVBackendCountdown
import Flapjack.Compiler.Backend.LabToTarget.ShmemMembership
import Flapjack.Compiler.Backend.RiscVConfig.PancakeConfigOk
import SteppedFlapjack.PanToCrepSteps.FilteredCountdownGuards
import SteppedFlapjack.PanToCrepSteps.RiscVInitializerFacts
import SteppedFlapjack.PanToCrepSteps.SingleEntrySourceEnvironment
import SteppedFlapjack.PanToCrepSteps.CanonicalFfi

/-! Construct the countdown's matching source environments from an arbitrary template. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open Flapjack.LoopSemStateFiniteExact Flapjack.WordSemStateFiniteExact
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabProps Flapjack.Misc
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.LabToTargetSteps

open Flapjack.Compiler.Backend.RiscVConfig

/-- The shared-memory extractor appends one name for each information record,
even before code-validity properties are established. -/
theorem shmemInfo_lengths (code : LabSem.LabProgHOL 64) (pos : Nat)
    (names : List HolFfiName) (info : List ShmemInfoNum) (hlen : names.length = info.length) :
    (getShmemInfo code pos names info).1.length = (getShmemInfo code pos names info).2.length := by
  induction code generalizing pos names info with
  | nil => simpa [getShmemInfo] using hlen
  | cons sec rest ih =>
    rcases sec with ⟨k,lines⟩
    induction lines generalizing pos names info with
    | nil => simpa only [getShmemInfo] using ih pos names info hlen
    | cons line lines ihLines =>
      cases line with
      | label a b n => simpa only [getShmemInfo] using ihLines pos names info hlen
      | labAsm a w bs n => simpa only [getShmemInfo] using ihLines (pos+bs.length) names info hlen
      | asm a bs n =>
        cases a with
        | asmi a => simpa only [getShmemInfo] using ihLines (pos+bs.length) names info hlen
        | cbw a b => simpa only [getShmemInfo] using ihLines (pos+bs.length) names info hlen
        | shareMem m r addr =>
          cases addr with
          | addr base off =>
            rcases hm : getMemopInfo m with ⟨op,nb⟩
            let entry : ShmemInfoNum :=
              { entryPc := pos, nbytes := nb, addrReg := base, addrOff := off.toNat,
                reg := r, exitPc := pos+bs.length }
            simpa only [getShmemInfo,hm,entry] using
              ihLines (pos+bs.length) (names++[.sharedMem op]) (info++[entry]) (by simp [hlen])

end SteppedFlapjack.PanToCrepSteps
