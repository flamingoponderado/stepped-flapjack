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
  (fullMakeInit countdownRiscVBackend.stackConf countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset
    [4] code (fixtureLab code cfg) fixtureSavedRegs 0 (fixtureStackOracle cfg)).1

/-- Full Stack initialization with the concrete compiler bitmap list. -/
noncomputable def configuredStack (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (bs : List (BitVec 64)) : StackSemStateFiniteExact 64 LabToTarget.Config Unit :=
  (fullMakeInit countdownRiscVBackend.stackConf countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset
    bs code (configuredLab code cfg bs) fixtureSavedRegs 0 (fixtureStackOracle cfg)).1

theorem configuredStack_one (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config) :
    configuredStack code cfg [4] = fixtureStack code cfg := by
  unfold configuredStack fixtureStack
  rw [configuredLab_one]

/-- A native oracle that never installs additional code. -/
def fixtureWordOracle (cfg : LabToTarget.Config) : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64)) :=
  fun _ => ((1,cfg),[])

/-- The no-install Word oracle starts after the actual bitmap list. -/
def configuredWordOracle (cfg : LabToTarget.Config) (bs : List (BitVec 64)) :
    Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64)) :=
  fun _ => ((bs.length,cfg),[])

theorem configuredWordOracle_one (cfg : LabToTarget.Config) :
    configuredWordOracle cfg [4] = fixtureWordOracle cfg := by rfl

/-- Full initialization context for any fitting compiler bitmap list. -/
noncomputable def configuredStackContext (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (bs : List (BitVec 64)) (fits : 0xa0020018 + bs.length*8 ≤ sourceBase)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) : FullInitStackContext (configuredStack code cfg bs) where
  stackConf := countdownRiscVBackend.stackConf
  dataConf := countdownRiscVBackend.dataConf
  maxHeap := 2^53-1
  sp := 24
  offset := riscvConfig.addrOffset
  bitmaps := bs
  inputCode := code
  lab := configuredLab code cfg bs
  saveRegs := fixtureSavedRegs
  dataSp := 0
  coracle := fixtureStackOracle cfg
  initAssumptions := configuredLab_initAssumptions code cfg bs fits good
  stackEq := rfl

/-- The initialized Stack state meets the native Word initializer contract. -/
theorem configuredStack_nativeInitOk (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (tail : List (BitVec 64)) (fits : 0xa0020018 + (4 :: tail).length*8 ≤ sourceBase)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) :
    Flapjack.WordToStackProofs.InitializationStateRel.initStateOk riscvConfig
      (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (configuredStack code cfg (4 :: tail))
      (configuredWordOracle cfg (4 :: tail)) := by
  apply (configuredStackContext code cfg (4 :: tail) fits good).nativeInitOk riscvConfig
    (configuredWordOracle cfg (4 :: tail)) tail (by decide) rfl
  · intro n
    simp [configuredWordOracle,configuredStackContext]
  · funext n
    rfl

/-- Successful initialization installs the exact program code and bitmap list. -/
theorem configuredStack_code_and_bitmaps (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (bs : List (BitVec 64)) (fits : 0xa0020018 + bs.length*8 ≤ sourceBase)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) :
    (configuredStack code cfg bs).code = sptFromAList code ∧ (configuredStack code cfg bs).bitmaps = bs := by
  exact (configuredStackContext code cfg bs fits good).stack_code_and_bitmaps

/-- The bitmap-aware fixture reserves the same concrete stack as init-e. -/
theorem configuredStack_stackLength (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (bs : List (BitVec 64)) (fits : 0xa0020018 + bs.length*8 ≤ sourceBase)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) :
    (configuredStack code cfg bs).stack.length = 2097172 := by
  let ctx := configuredStackContext code cfg bs fits good
  have r2 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 2 = 11 := by with_unfolding_all rfl
  have r3 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 3 = 12 := by with_unfolding_all rfl
  have r4 : StackNames.findNameSpt countdownRiscVBackend.stackConf.regNames 4 = 13 := by with_unfolding_all rfl
  have length := ctx.stack_length_lab
  simp only [FullInitStackContext.labStackLength,ctx,configuredStackContext,r2,r3,r4] at length
  change (configuredStack code cfg bs).stack.length =
    (Flapjack.Compiler.Backend.StackRemove.Proofs.InitLimits.getStackHeapLimit (2^53-1)
      (BitVec.ofNat 64 sourceBase,BitVec.ofNat 64 heapEnd,BitVec.ofNat 64 ramEnd)).1 at length
  rw [fixture_init_limits] at length
  exact length

/-- The actual initialized Stack state satisfies the native initializer relation. -/
theorem fixtureStack_nativeInitOk (code : List (Nat × HolProg 64)) (cfg : LabToTarget.Config)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) :
    Flapjack.WordToStackProofs.InitializationStateRel.initStateOk riscvConfig
      (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) (fixtureStack code cfg) (fixtureWordOracle cfg) := by
  have fits : 0xa0020018 + (4 :: ([] : List (BitVec 64))).length*8 ≤ sourceBase := by decide
  have h := configuredStack_nativeInitOk code cfg [] fits good
  rw [configuredStack_one,configuredWordOracle_one] at h
  exact h

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
