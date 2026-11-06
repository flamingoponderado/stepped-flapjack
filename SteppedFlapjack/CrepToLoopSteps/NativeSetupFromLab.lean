import SteppedFlapjack.CrepToLoopSteps.WholeNativeCodeKeys
import Flapjack.Compiler.Backend.StackToLab.Proofs.MakeInit
import Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

/-! Construct the renamed Stack state used by the native machine setup. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordToWord Flapjack.WordToStackProofs
open Flapjack.StackSemStateOps Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.LabToTargetSteps

/-- The renamed Stack state constructed by the actual Stack-to-Lab initializer
from a Lab state, the lowered code, and its compilation oracle. -/
noncomputable def nativeRenamedFromLab {F : Type} (f : Spt Nat) (jump : Bool)
    (bounds : BitVec 64 × BitVec 64) (gen : Bool) (maxHeap a b : Nat)
    (removeInput : List (Nat × HolProg 64))
    (oracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64))
    (regs : List Nat) (saveRegs : Nat → Bool) (lab : LabSem.State 64 LabToTarget.Config F) :
    StackSemStateFiniteExact 64 LabToTarget.Config F :=
  Flapjack.Compiler.Backend.StackToLab.Proofs.MakeInit.makeInit
    (sptFromAList (compileHOL f (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)))
    (Prod.map id (Prod.map (compileHOL f) id) ∘ oracle) regs saveRegs lab

/-- The canonical renamed state supplies the code, oracle, and disabled
feature fields required by the Stack-to-machine simulation. -/
theorem nativeRenamedFromLab_fields {F : Type} (f : Spt Nat) (jump : Bool)
    (bounds : BitVec 64 × BitVec 64) (gen : Bool) (maxHeap a b : Nat)
    (removeInput : List (Nat × HolProg 64))
    (oracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64))
    (regs : List Nat) (saveRegs : Nat → Bool) (lab : LabSem.State 64 LabToTarget.Config F) :
    let renamed := nativeRenamedFromLab f jump bounds gen maxHeap a b removeInput oracle regs saveRegs lab
    ¬renamed.useAlloc ∧ ¬renamed.useStore ∧ ¬renamed.useStack ∧
    renamed.code = sptFromAList (compileHOL f (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)) ∧
    renamed.compileOracle = Prod.map id (Prod.map (compileHOL f) id) ∘ oracle := by
  simp [nativeRenamedFromLab,Flapjack.Compiler.Backend.StackToLab.Proofs.MakeInit.makeInit]

/-- Construct the native machine setup using the actual Lab-to-Stack initializer. -/
noncomputable def wholeCrep_native_machineSetupFromLab {F : Type}
    (arch : AsmArchitecture) (crepPrograms : List (MlString × List Nat × CrepProgHOL 64))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64)
    (stack : StackSemStateFiniteExact 64 LabToTarget.Config F) (name stackReplay : Nat)
    (inputCode : List (Nat × HolProg 64))
    (inputCodeEq : inputCode = (compileNative ac false (compile wc ac
      (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))).2).2.2.2)
    (stackCode : stack.code = sptFromAList (compileNative ac false (compile wc ac
      (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))).2).2.2.2)
    (anything : WordSemGcFun 64) (cr : CompileFn 64 LabToTarget.Config) (c : DataToWord.Config)
    (jump : Bool) (bounds : BitVec 64 × BitVec 64) (pointer : Nat) (f : Spt Nat)
    (gen : Bool) (maxHeap a b : Nat) (removeInput : List (Nat × HolProg 64))
    (oracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64))
    (regs : List Nat) (saveRegs : Nat → Bool)
    (lab : LabSem.State 64 LabToTarget.Config F) (pc : BitVec 64)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (labCode : LabSem.LabProgHOL 64) (labs : Spt (Spt Nat)) (asm : AsmState 64)
    (machine : RiscV.L3.riscv_state)
    (pre : Pre cr c {stack with code := sptFromAList (StackRawCall.compile inputCode),clock := stackReplay+1} stack.regs)
    (relation : stateRelHOL jump bounds pointer
      (Tgt anything cr c {stack with code := sptFromAList (StackRawCall.compile inputCode),clock := stackReplay+1} 0 stack.regs)
      (makeInit f (sptFromAList (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)) oracle (nativeRenamedFromLab f jump bounds gen maxHeap a b removeInput oracle regs saveRegs lab)))
    (hf : Function.Bijective (findNameSpt f))
    (labRel : Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel.stateRel
      (nativeRenamedFromLab f jump bounds gen maxHeap a b removeInput oracle regs saveRegs lab) lab)
    (hpc : LabSem.locToPc name 0 lab.code = some lab.pc)
    (hmc : mc.target = riscvTarget) (tie : LabToTarget.oracleTie mc machine lab)
    (machineRel : LabToTarget.stateRel (mc,labCode,labs,pc) lab asm machine) :
    NativeTailMachineSetup stack name stackReplay := by
  let renamed := nativeRenamedFromLab f jump bounds gen maxHeap a b removeInput oracle regs saveRegs lab
  obtain ⟨ha,hs,hk,hcode,hor⟩ := nativeRenamedFromLab_fields f jump bounds gen maxHeap a b removeInput oracle regs saveRegs lab
  exact wholeCrep_native_machineSetup arch crepPrograms wc ac stack name stackReplay inputCode inputCodeEq stackCode
    anything cr c jump bounds pointer f gen maxHeap a b removeInput oracle renamed lab pc mc labCode labs asm machine
    pre relation ha hs hk hf hcode hor labRel hpc hmc tie machineRel


/-- The standard full-initialization assumptions prove the canonical renamed
Stack-to-Lab relation for the compiler-generated StackRemove code and oracle.
These assumptions describe the full initialization entry, including its Lab
program counter. -/
theorem fullInit_nativeRenamed_labRel {F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec 64 × BitVec 64) (bitmaps : List (BitVec 64))
    (code : List (Nat × HolProg 64)) (lab : LabSem.State 64 LabToTarget.Config F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (coracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64))
    (hA : Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics.Assumptions
      stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle) :
    Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel.stateRel
      (nativeRenamedFromLab stackConf.regNames stackConf.jump offset (StackToLab.isGenGc dataConf.gcKind)
        maxHeap sp BvlToBvi.initGlobalsLocation
        (Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics.code1 dataConf code)
        (Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics.coracle2 stackConf sp offset coracle)
        ([2,3,4].map (findNameSpt stackConf.regNames)) saveRegs lab) lab := by
  have rel := Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics.stateRel_s3 hA
  simpa [nativeRenamedFromLab,Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics.s3,
    Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics.code2,
    Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics.coracle3] using rel

end SteppedFlapjack.CrepToLoopSteps
