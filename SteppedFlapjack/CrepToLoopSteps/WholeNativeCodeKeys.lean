import SteppedFlapjack.CrepToLoopSteps.NativeTailFrontendSetup
import SteppedFlapjack.WordToStackSteps.NativeCodeKeys

/-! Distinct native Stack names from the actual Crep compiler output. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordToWord
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordToStackSteps
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.StackSemStateOps Flapjack.Compiler.Backend.StackAlloc Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackNames
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.LabToTargetSteps

/-- The whole Crep-to-native compiler produces a Stack code list with unique
keys, including its runtime stubs. -/
theorem wholeCrep_native_code_nodup (arch : AsmArchitecture)
    (crepPrograms : List (MlString × List Nat × CrepProgHOL 64))
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact 64) :
    (((compileNative ac false (compile wc ac
      (loopToWordCompileHOL (compileProgHOLExact arch crepPrograms))).2).2.2.2).map Prod.fst).Nodup := by
  let programs := loopToWordCompileHOL (compileProgHOLExact arch crepPrograms)
  have nodup : (programs.map Prod.fst).Nodup :=
    loopToWordFirstCompileAllDistinct _ (firstCompileProgAllDistinctExact arch _)
  have minimum : ∀ entry ∈ programs, 60 ≤ entry.1 := by
    apply LoopToWord.loop_to_word_compile_lab_min _ _ 60
    exact ⟨rfl,crep_to_loop_compile_prog_lab_min arch _ _ rfl⟩
  have noRaise : raiseStubLocation ∉ programs.map Prod.fst := by
    intro h
    obtain ⟨entry,hentry,hname⟩ := List.mem_map.mp h
    have lower := minimum entry hentry
    rw [hname] at lower
    simp [raiseStubLocation,wordNumStubs,stackNumStubs] at lower
  have noStore : storeConstsStubLocation ∉ programs.map Prod.fst := by
    intro h
    obtain ⟨entry,hentry,hname⟩ := List.mem_map.mp h
    have lower := minimum entry hentry
    rw [hname] at lower
    simp [storeConstsStubLocation,wordNumStubs,stackNumStubs] at lower
  have names : ((compile wc ac programs).2.map Prod.fst) = programs.map Prod.fst := wholeCompile_names wc ac programs
  change (((compileNative ac false (compile wc ac programs).2).2.2.2).map Prod.fst).Nodup
  apply compileNative_code_nodup
  · rw [names]; exact nodup
  · rw [names]; exact noRaise
  · rw [names]; exact noStore


/-- Build the remaining machine setup using the actual compiled Stack list.
The compiled-list equality and `stackCode` determine both code witnesses;
the semantic initialization and Lab/machine relations remain explicit. -/
noncomputable def wholeCrep_native_machineSetup {F : Type}
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
    (renamed : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (lab : LabSem.State 64 LabToTarget.Config F) (pc : BitVec 64)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (labCode : LabSem.LabProgHOL 64) (labs : Spt (Spt Nat)) (asm : AsmState 64)
    (machine : RiscV.L3.riscv_state)
    (pre : Pre cr c {stack with code := sptFromAList (StackRawCall.compile inputCode),clock := stackReplay+1} stack.regs)
    (relation : stateRelHOL jump bounds pointer
      (Tgt anything cr c {stack with code := sptFromAList (StackRawCall.compile inputCode),clock := stackReplay+1} 0 stack.regs)
      (makeInit f (sptFromAList (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)) oracle renamed))
    (ha : ¬renamed.useAlloc) (hs : ¬renamed.useStore) (hk : ¬renamed.useStack)
    (hf : Function.Bijective (findNameSpt f))
    (hcode : renamed.code = sptFromAList (compileHOL f (StackRemove.compileHOL jump bounds gen maxHeap a b removeInput)))
    (hor : renamed.compileOracle = Prod.map id (Prod.map (compileHOL f) id) ∘ oracle)
    (labRel : Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel.stateRel renamed lab)
    (hpc : LabSem.locToPc name 0 lab.code = some lab.pc)
    (hmc : mc.target = riscvTarget) (tie : LabToTarget.oracleTie mc machine lab)
    (machineRel : LabToTarget.stateRel (mc,labCode,labs,pc) lab asm machine) :
    NativeTailMachineSetup stack name stackReplay := by
  have distinct : (inputCode.map Prod.fst).Nodup := by
    rw [inputCodeEq]
    exact wholeCrep_native_code_nodup arch crepPrograms wc ac
  exact ⟨inputCode,anything,cr,c,jump,bounds,pointer,f,gen,maxHeap,a,b,removeInput,oracle,
    renamed,lab,pc,mc,labCode,labs,asm,machine,distinct,(by simpa only [inputCodeEq] using stackCode),pre,relation,ha,hs,hk,hf,
    hcode,hor,labRel,hpc,hmc,tie,machineRel⟩

end SteppedFlapjack.CrepToLoopSteps
