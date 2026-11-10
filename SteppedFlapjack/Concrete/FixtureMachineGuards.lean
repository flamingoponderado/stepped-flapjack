import SteppedFlapjack.Concrete.FixtureStackSafety
import SteppedFlapjack.PanToCrepSteps.CountdownNoShare
import Flapjack.Pancake.Proofs.PanToTarget.ExecutableCompileProgMaxAsmWith

/-! Discharge the machine's compiler guards from verified fixture facts. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Misc
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.LoopToWordSteps

/-- Successful label removal preserves the absence of shared-memory metadata. -/
theorem fixtureCompiled_noSharedMetadata (code : List (Nat × HolProg 64))
    (good : goodCode riscvConfig (.ln : Spt (Spt Nat))
      (LabFilter.filterSkip (fixtureLab code (fixtureCompilerConfig code)).code))
    (noShare : noShareMemInst (LabFilter.filterSkip (fixtureLab code (fixtureCompilerConfig code)).code))
    (success : (fixtureRemoveLabels code).isSome = true) :
    getShmemInfo (fixtureCompiled code).1 0 [] [] = ([],[]) := by
  have removed : removeLabels 5 riscvConfig 0 .ln []
      (LabFilter.filterSkip (fixtureLab code (fixtureCompilerConfig code)).code) =
      some ((fixtureCompiled code).1,(fixtureCompiled code).2) := by
    have h := fixtureRemoveLabels_eq code success
    exact h
  obtain ⟨ends,labels,ids,distinct,disjoint,targets,pre⟩ := good
  have mcok := riscvTarget_mcConfOk countdownMachineConfig rfl rfl rfl rfl rfl
  have correct := removeLabels_correct 5 riscvConfig 0 .ln []
    (LabFilter.filterSkip (fixtureLab code (fixtureCompilerConfig code)).code)
    (fixtureCompiled code).1 (fixtureCompiled code).2
    ⟨removed,mcok.2.2.2.2.2.2.2,ends,labels,ids,distinct,disjoint,targets,pre,by decide,
      by simp [labLookup,sptLookup]⟩
  have similar := correct.2.1
  have noShare' := (codeSimilar_noShareMem _ _ ⟨similar,noShare⟩)
  exact noShareMem_getShmemInfo _ 0 [] [] noShare'

/-- Good compiled code, operation safety, and checked compiler output imply
all original machine initialization guards. -/
theorem fixtureMachine_allGuards (code : List (Nat × HolProg 64))
    (good : goodCode riscvConfig (.ln : Spt (Spt Nat))
      (LabFilter.filterSkip (fixtureLab code (fixtureCompilerConfig code)).code))
    (safe : fixtureStackSafe code = true)
    (facts : (fixtureRemoveLabels code).isSome = true ∧
      (fixtureCodeBytes code).length ≤ 0xecc ∧ (fixtureCodeBytes code).length % 4 = 0) :
    LabMachineInitGuards (fixtureMachineConfig (fixtureCodeStart code)) (fixtureMachineState code)
      (LabFilter.filterSkip (fixtureLab code (fixtureCompilerConfig code)).code)
      (fixtureCompiled code).1 (fixtureCompiled code).2 5 0 0xecc (fixtureMachineAsm code)
      (fixtureLabMemoryFor code) fixtureByteDomain fixtureSharedByteDomain
      (fun n => (((fixtureLab code (fixtureCompilerConfig code)).compileOracle n).1,
        LabFilter.filterSkip ((fixtureLab code (fixtureCompilerConfig code)).compileOracle n).2)) [] [] [] := by
  have safety := fixtureLabSafe code (fixtureCompilerConfig code) safe
  have removed : removeLabels 5 riscvConfig 0 .ln []
      (LabFilter.filterSkip (fixtureLab code (fixtureCompilerConfig code)).code) =
      some ((fixtureCompiled code).1,(fixtureCompiled code).2) := fixtureRemoveLabels_eq code facts.1
  have info := fixtureCompiled_noSharedMetadata code good safety.1 facts.1
  have noInstall : noInstallOrNoShareMem (LabFilter.filterSkip (fixtureLab code (fixtureCompilerConfig code)).code) [] :=
    Or.inl ⟨safety.1,by simp⟩
  have length : (fixtureCompilerConfig code).pos = (progToBytes (fixtureCompiled code).1).length := by
    change (fixtureCodeBytes code).length = _
    rw [fixtureCompiled_bytes]
  exact fixtureMachine_guards code (fixtureCompilerConfig code) (fixtureCompiled code).1 (fixtureCompiled code).2
    good safety.2 removed info noInstall rfl length rfl (by omega) facts.2.2


/-- The concrete buffer dominates every line of a fitting compiled program,
so each Lab step costs at most 948 machine ticks. -/
theorem fixtureLabMachineFactor (code : List (Nat × HolProg 64))
    (fits : (fixtureCodeBytes code).length ≤ 0xecc) :
    SteppedFlapjack.LabToTargetSteps.labTickBound 4 (fixtureCompiled code).1 ⟨0x800f0134,[],0xecc⟩ = 948 := by
  have length : (progToBytes (fixtureCompiled code).1).length ≤ 0xecc := by
    rw [← fixtureCompiled_bytes]
    exact fits
  have lines : SteppedFlapjack.LabToTargetSteps.maxLineBytes (fixtureCompiled code).1 ≤ 0xecc := by
    apply SteppedFlapjack.LabToTargetSteps.maxLineBytes_le
    intro j member
    exact (SteppedFlapjack.LabToTargetSteps.lineBytes_length_le_progToBytes member).trans length
  unfold SteppedFlapjack.LabToTargetSteps.labTickBound SteppedFlapjack.LabToTargetSteps.lineByteBound
  simp only [List.length_nil,Nat.zero_add,Nat.max_eq_right lines]


/-- Transfer a successful concrete Lab run to the loaded machine at 948 times
its explicit Lab clock, preserving its complete FFI state. -/
theorem fixtureLabMachineReturn (code : List (Nat × HolProg 64))
    (good : goodCode riscvConfig (.ln : Spt (Spt Nat))
      (LabFilter.filterSkip (fixtureLab code (fixtureCompilerConfig code)).code))
    (safe : fixtureStackSafe code = true)
    (facts : (fixtureRemoveLabels code).isSome = true ∧
      (fixtureCodeBytes code).length ≤ 0xecc ∧ (fixtureCodeBytes code).length % 4 = 0)
    (clock : Nat) (post : LabSem.State 64 Config Unit)
    (run : LabSem.evaluate {(fixtureTargetLab code (fixtureCompilerConfig code) (fixtureMachineState code))
      with clock := clock} = (.halt .success,post)) :
    ∃ machinePost, evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi
      (948 * clock) (fixtureMachineState code) = (.halt .success,machinePost,post.ffi) := by
  have removed : removeLabels 5 riscvConfig 0 .ln []
      (LabFilter.filterSkip (fixtureLab code (fixtureCompilerConfig code)).code) =
      some ((fixtureCompiled code).1,(fixtureCompiled code).2) := fixtureRemoveLabels_eq code facts.1
  have guards := fixtureMachine_allGuards code good safe facts
  have result := fixtureLabToMachineExplicit code (fixtureCompilerConfig code)
    (fixtureCompiled code).1 (fixtureCompiled code).2 removed guards clock .success post run
  rw [fixtureLabMachineFactor code facts.2.1] at result
  exact result


/-- The exact byte stream loaded into the fixture machine is produced by the
original Lab-to-target compiler. -/
theorem fixtureLabCompiler_output (code : List (Nat × HolProg 64))
    (safe : fixtureStackSafe code = true) (success : (fixtureRemoveLabels code).isSome = true) :
    ∃ final, LabToTarget.compile riscvConfig countdownRiscVBackend.labConf
      (fixtureLab code countdownRiscVBackend.labConf).code = some (fixtureCodeBytes code,final) := by
  have names := (fixtureLabSafe code countdownRiscVBackend.labConf safe).2
  have removed : removeLabels 5 riscvConfig 0 .ln []
      (LabFilter.filterSkip (fixtureLab code countdownRiscVBackend.labConf).code) =
      some ((fixtureCompiled code).1,(fixtureCompiled code).2) := fixtureRemoveLabels_eq code success
  unfold LabToTarget.compile LabToTarget.compileLab
  simp only [show countdownRiscVBackend.labConf.ffiNames = none from rfl,names,
    show countdownRiscVBackend.labConf.initClock = 5 from rfl,
    show countdownRiscVBackend.labConf.pos = 0 from rfl,
    show countdownRiscVBackend.labConf.labels = .ln from rfl,removed,if_true]
  rw [fixtureCompiled_bytes]
  exact ⟨_,rfl⟩


/-- The Pancake compiler emits exactly the code bytes loaded in the machine. -/
theorem fixturePancakeCompiler_output (body : Flapjack.Pancake.PanLang.ProgHOL 64)
    (words : List (Nat × Nat × WordLangProgHOL (BitVec 64))) (code : List (Nat × HolProg 64))
    (compiled : panToWordCompileProgHOL riscvConfig.isa
      (singleEntryProgram (Flapjack.Basis.Pure.MlString.ofString "main") body) = words)
    (codeEq : (WordToStack.Native.compileNative riscvConfig false
      (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig words).2).2.2.2 = code)
    (bitmap : (WordToStack.Native.compileNative riscvConfig false
      (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig words).2).1 = [4])
    (safe : fixtureStackSafe code = true) (success : (fixtureRemoveLabels code).isSome = true) :
    ∃ final, Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast countdownRiscVBackend riscvConfig
      (singleEntryProgram (Flapjack.Basis.Pure.MlString.ofString "main") body) =
        some (fixtureCodeBytes code,[4],final) := by
  obtain ⟨labFinal,labEq⟩ := fixtureLabCompiler_output code safe success
  rw [Flapjack.Pancake.Proofs.PanToTarget.compileProgAsmFast_eq_fst]
  simp only [Flapjack.Pancake.Proofs.PanToTarget.compileProgMaxAsmExecutable,WordToWord.compileExecutable_eq,compiled]
  change ∃ final, Backend.fromStack riscvConfig countdownRiscVBackend .ln
    (WordToStack.Native.compileNative riscvConfig false
      (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig words).2).2.2.2
    (WordToStack.Native.compileNative riscvConfig false
      (WordToWord.compile countdownRiscVBackend.wordToWordConf riscvConfig words).2).1 = _
  rw [codeEq,bitmap]
  change ∃ final, Backend.attachBitmaps .ln countdownRiscVBackend ([4] : List (BitVec 64))
    (LabToTarget.compile riscvConfig countdownRiscVBackend.labConf (fixtureLab code countdownRiscVBackend.labConf).code) = _
  rw [labEq]
  exact ⟨_,rfl⟩

end SteppedFlapjack.Concrete
