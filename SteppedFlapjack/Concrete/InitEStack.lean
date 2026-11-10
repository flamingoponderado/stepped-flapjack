import SteppedFlapjack.Concrete.InitELab
import SteppedFlapjack.StackRemoveSteps.InitStackNonempty
import SteppedFlapjack.LoopToWordSteps.FullInitNativeValidity
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.StackRemove.Proofs
open Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.LoopToWordSteps

namespace SteppedFlapjack.Concrete

/-- The actual fullMakeInit Stack state for this Lab layout. -/
noncomputable def fixtureStack (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config) :
    StackSemStateFiniteExact 64 LabToTarget.Config Unit :=
  (fullMakeInit countdownRiscVBackend.stackConf countdownRiscVBackend.dataConf (2^61) 24 riscvConfig.addrOffset
    [4] code (fixtureLab code cfg) fixtureSavedRegs 0 (fixtureStackOracle cfg)).1

/-- A native oracle that never installs additional code. -/
def fixtureWordOracle (cfg : LabToTarget.Config) : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64)) :=
  fun _ => ((1,cfg),[])

/-- Stack-only initialization context for the concrete Lab layout. -/
noncomputable def fixtureStackContext (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) : FullInitStackContext (fixtureStack code cfg) where
  stackConf := countdownRiscVBackend.stackConf
  dataConf := countdownRiscVBackend.dataConf
  maxHeap := 2^61
  sp := 24
  offset := riscvConfig.addrOffset
  bitmaps := [4]
  inputCode := code
  lab := fixtureLab code cfg
  saveRegs := fixtureSavedRegs
  dataSp := 0
  coracle := fixtureStackOracle cfg
  initAssumptions := fixtureLab_initAssumptions code cfg good
  stackEq := rfl

/-- The actual initialized Stack state satisfies the native initializer relation. -/
theorem fixtureStack_nativeInitOk (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) :
    Flapjack.WordToStackProofs.InitializationStateRel.initStateOk riscvConfig
      (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (fixtureStack code cfg) (fixtureWordOracle cfg) := by
  apply (fixtureStackContext code cfg good).nativeInitOk riscvConfig (fixtureWordOracle cfg) [] (by decide) rfl
  · intro n
    simp [fixtureWordOracle,fixtureStackContext]
  · funext n
    rfl

theorem fixtureStack_code (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config) :
    (fixtureStack code cfg).code = sptFromAList code := by
  unfold fixtureStack
  rw [fullMakeInit_eq]
  rfl

theorem fixtureStack_bitmaps (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config) :
    (fixtureStack code cfg).bitmaps = [4] := by
  unfold fixtureStack
  rw [fullMakeInit_eq]
  change (InitMake.makeInitAny _ _ _ _ _ _ _ _ _ _).bitmaps = [4]
  rw [InitAny.makeInitAnyBitmaps]
  simp

theorem fixtureStack_nonempty (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config) :
    1 ≤ (fixtureStack code cfg).stack.length := by
  exact SteppedFlapjack.StackRemoveSteps.fullMakeInit_stack_nonempty _ _ _ _ _ _ _ _ _ _ _

end SteppedFlapjack.Concrete
