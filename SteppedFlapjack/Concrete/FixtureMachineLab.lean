import SteppedFlapjack.PanToCrepSteps.RiscVInitializerFacts
import SteppedFlapjack.Concrete.FixtureMachineState
import SteppedFlapjack.LabToTargetSteps.InitializedRiscV

/-! Connect the init-e-shaped fixture Lab run to its concrete RISC-V machine. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.LoopToWordSteps SteppedFlapjack.LabToTargetSteps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

/-- A successful label-removal result identifies the exact loaded bytes. -/
theorem fixtureCodeBytes_eq (code : List (Nat × HolProg 64)) (code2 : LabProgHOL 64) (labs : Spt (Spt Nat)) (cfg : Config)
    (removed : removeLabels 5 riscvConfig 0 .ln [] (LabFilter.filterSkip (fixtureLab code cfg).code) = some (code2,labs)) :
    fixtureCodeBytes code = progToBytes code2 := by
  simp only [fixtureLab] at removed
  unfold fixtureCodeBytes
  rw [removed]

/-- The actual label-removal result for a fixture's compiled Lab program. -/
noncomputable def fixtureRemoveLabels (code : List (Nat × HolProg 64)) : Option (LabProgHOL 64 × Spt (Spt Nat)) :=
  removeLabels 5 riscvConfig 0 .ln [] (LabFilter.filterSkip (fixtureLab code countdownRiscVBackend.labConf).code)

/-- The selected compiled code and labels; success is proved for each witness. -/
noncomputable def fixtureCompiled (code : List (Nat × HolProg 64)) : LabProgHOL 64 × Spt (Spt Nat) :=
  (fixtureRemoveLabels code).getD ([],.ln)

/-- A successful label-removal result is exactly the selected compiled code. -/
theorem fixtureRemoveLabels_eq (code : List (Nat × HolProg 64))
    (success : (fixtureRemoveLabels code).isSome = true) :
    fixtureRemoveLabels code = some (fixtureCompiled code) := by
  cases h : fixtureRemoveLabels code with
  | none => simp [h] at success
  | some result => simp [fixtureCompiled,h]

/-- The selected code yields exactly the bytes installed in the fixture. -/
theorem fixtureCompiled_bytes (code : List (Nat × HolProg 64)) :
    fixtureCodeBytes code = progToBytes (fixtureCompiled code).1 := by
  change (match fixtureRemoveLabels code with
    | some (code2,_) => progToBytes code2
    | none => []) = progToBytes (fixtureCompiled code).1
  unfold fixtureCompiled
  cases h : fixtureRemoveLabels code with
  | none => simp [progToBytes]
  | some result => cases result; simp

/-- Configure the empty installation oracle using the actual compiler result. -/
noncomputable def fixtureCompilerConfig (code : List (Nat × HolProg 64)) : Config :=
  { countdownRiscVBackend.labConf with
    labels := (fixtureCompiled code).2
    pos := (fixtureCodeBytes code).length
    ffiNames := some [] }

/-- The initialized fixture's explicit Lab run transfers to its concrete
machine at the code-derived clock, with the same outcome and full FFI. -/
theorem fixtureLabToMachineExplicit (code : List (Nat × HolProg 64)) (cfg : Config)
    (code2 : LabProgHOL 64) (labs : Spt (Spt Nat))
    (removed : removeLabels 5 riscvConfig 0 .ln [] (LabFilter.filterSkip (fixtureLab code cfg).code) = some (code2,labs))
    (guards : LabMachineInitGuards (fixtureMachineConfig (fixtureCodeStart code)) (fixtureMachineState code)
      (LabFilter.filterSkip (fixtureLab code cfg).code) code2 labs 5 0 0xecc (fixtureMachineAsm code)
      (fixtureLabMemoryFor code) fixtureByteDomain fixtureSharedByteDomain
      (fun n => (((fixtureLab code cfg).compileOracle n).1,
        LabFilter.filterSkip ((fixtureLab code cfg).compileOracle n).2)) [] [] [])
    (clock : Nat) (outcome : HolOutcome) (post : LabSem.State 64 Config Unit)
    (run : evaluate {(fixtureTargetLab code cfg (fixtureMachineState code)) with clock := clock} = (.halt outcome,post)) :
    ∃ machinePost, evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi
      (labTickBound 4 code2 ⟨0x800f0134,[],0xecc⟩ * clock) (fixtureMachineState code) =
        (.halt outcome,machinePost,post.ffi) := by
  have bytes : fixtureCodeBytes code = progToBytes code2 := by
    apply fixtureCodeBytes_eq code code2 labs cfg
    simpa only [fixtureLab] using removed
  have pos : (fixtureMachineConfig (fixtureCodeStart code)).target.getPc (fixtureMachineState code) +
      BitVec.ofNat 64 (progToBytes code2).length = 0x800f0134 := by
    change fixtureCodeStart code + BitVec.ofNat 64 (progToBytes code2).length = 0x800f0134
    rw [← bytes]
    exact fixtureCodeStart_add_length code
  have alignedD : ∀ a, decide (fixtureLabDomain a) = true → holByteAligned a = true := by
    intro a h
    exact fixtureLabDomain_aligned a (of_decide_eq_true h)
  have alignedS : ∀ a, decide (sharedAddress a) = true → holByteAligned a = true := by
    intro a h
    exact ((sharedAddress_alignment a).1 (of_decide_eq_true h)).1
  have fixtureEq : fixtureTargetLab code cfg (fixtureMachineState code) =
      LabProps.alignSdm (LabProps.alignDm (makeInit
        (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi (fixtureMachineAsm code)
        (fixtureLabMemoryFor code) fixtureByteDomain fixtureSharedByteDomain (fixtureMachineState code)
        (fixtureLab code cfg).code (compile riscvConfig) 0x800f0134 0xecc (fixtureLab code cfg).compileOracle)) := by
    change fixtureTargetLab code cfg (fixtureMachineState code) =
      LabProps.alignSdm (LabProps.alignDm (makeInit
        (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi (fixtureMachineAsm code)
        (fixtureLabMemoryFor code) (byteClosure (fun a => decide (fixtureLabDomain a)))
        (byteClosure (fun a => decide (sharedAddress a))) (fixtureMachineState code)
        (fixtureLab code cfg).code (compile riscvConfig) 0x800f0134 0xecc (fixtureLab code cfg).compileOracle))
    rw [makeInit_byteClosure _ _ _ _ _ _ alignedD alignedS]
    rfl
  have labRun : evaluate {LabProps.alignSdm (LabProps.alignDm (makeInit
        (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi (fixtureMachineAsm code)
        (fixtureLabMemoryFor code) fixtureByteDomain fixtureSharedByteDomain (fixtureMachineState code)
        (fixtureLab code cfg).code (compile riscvConfig)
        ((fixtureMachineConfig (fixtureCodeStart code)).target.getPc (fixtureMachineState code) +
          BitVec.ofNat 64 (progToBytes code2).length) 0xecc (fixtureLab code cfg).compileOracle)) with clock := clock} =
      (.halt outcome,post) := by
    rw [pos,← fixtureEq]
    exact run
  have result := initializedLabToRiscVExplicit (fixtureMachineConfig (fixtureCodeStart code)) (fixtureMachineState code)
    sourceFfi (fixtureLab code cfg).code code2 labs 5 0 0xecc (fixtureMachineAsm code)
    (fixtureLabMemoryFor code) fixtureByteDomain fixtureSharedByteDomain (fixtureLab code cfg).compileOracle
    [] [] [] rfl guards clock clock outcome post labRun (Nat.le_refl clock)
  simpa only [pos] using result



/-- `makeInit` reads only the assembler's integer and floating-point registers. -/
private theorem makeInit_asm_congr {C S Q F : Type} (mc : MachineConfig 64 S Q) (ffi : HolFfiState F) (t t' : Flapjack.AsmState 64)
    (hr : t.regs = t'.regs) (hf : t.fpRegs = t'.fpRegs) (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool) (ms : S)
    (code : LabProgHOL 64) (comp : C → LabProgHOL 64 → Option (List (BitVec 8) × C)) (cbpos : BitVec 64) (cbspace : Nat)
    (co : Nat → C × LabProgHOL 64) :
    makeInit mc ffi t m dm sdm ms code comp cbpos cbspace co = makeInit mc ffi t' m dm sdm ms code comp cbpos cbspace co := by
  simp only [makeInit, hr, hf]

/-- A clock update to the state's own clock is the identity (generic, no unfolding). -/
private theorem withClock_of_eq {C F : Type} (s : LabSem.State 64 C F) (k : Nat) (h : s.clock = k) :
    ({s with clock := k} : LabSem.State 64 C F) = s := by
  subst h; rfl

private theorem makeInit_clock {C S Q F : Type} (mc : MachineConfig 64 S Q) (ffi : HolFfiState F) (t : Flapjack.AsmState 64)
    (m : BitVec 64 → WordLocW 64) (dm sdm : BitVec 64 → Bool) (ms : S) (code : LabProgHOL 64)
    (comp : C → LabProgHOL 64 → Option (List (BitVec 8) × C)) (cbpos : BitVec 64) (cbspace : Nat)
    (co : Nat → C × LabProgHOL 64) : (makeInit mc ffi t m dm sdm ms code comp cbpos cbspace co).clock = 0 := rfl

/-- The constructor's Lab (byte-aligned machine domains, code-derived buffer
position) is the Phase 5 fixture Lab. Cheap: two funext rewrites and the
buffer-position equation; makeInit reads only the assembler registers. -/
private theorem configuredCtorLab_eq (code : List (Nat × HolProg 64)) (cfg : Config) (bs : List (BitVec 64))
    (_bitmapFits : 0xa0020018 + bs.length*8 ≤ 0xa0410000) (code2 : LabProgHOL 64)
    (bytes : fixtureCodeBytes code = progToBytes code2) :
    makeInit (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi (configuredMachineAsm code bs) (configuredLabMemory code bs)
      (fun a => configuredByteDomain bs a && holByteAligned a) (fun a => fixtureSharedByteDomain a && holByteAligned a)
      (configuredMachineState code bs) (configuredLab code cfg bs).code
      (LabToTarget.compile (fixtureMachineConfig (fixtureCodeStart code)).target.config)
      ((fixtureMachineConfig (fixtureCodeStart code)).target.getPc (configuredMachineState code bs) +
        BitVec.ofNat 64 (progToBytes code2).length) 0xecc (configuredLab code cfg bs).compileOracle =
    configuredTargetLab code cfg bs (configuredMachineState code bs) := by
  have pos : (fixtureMachineConfig (fixtureCodeStart code)).target.getPc (configuredMachineState code bs) +
      BitVec.ofNat 64 (progToBytes code2).length = 0x800f0134 := by
    change fixtureCodeStart code + BitVec.ofNat 64 (progToBytes code2).length = 0x800f0134
    rw [← bytes]
    exact fixtureCodeStart_add_length code
  have hD : (fun a => configuredByteDomain bs a && holByteAligned a) = fun a => decide (configuredLabDomain bs a) :=
    byteClosure_aligned _ (fun a h => configuredLabDomain_aligned bs a (of_decide_eq_true h))
  have hS : (fun a => fixtureSharedByteDomain a && holByteAligned a) = fun a => decide (sharedAddress a) :=
    byteClosure_aligned _ (fun a h => ((sharedAddress_alignment a).1 (of_decide_eq_true h)).1)
  have hc : (fixtureMachineConfig (fixtureCodeStart code)).target.config = riscvConfig := rfl
  rw [pos, hD, hS, hc, makeInit_asm_congr _ _ (configuredMachineAsm code bs) fixtureAsm rfl rfl]
  unfold configuredTargetLab
  congr 1

private theorem configuredCtorAssumptions (code : List (Nat × HolProg 64)) (cfg : Config) (bs : List (BitVec 64))
    (bitmapFits : 0xa0020018 + bs.length*8 ≤ 0xa0410000) (code2 : LabProgHOL 64)
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code) (bytes : fixtureCodeBytes code = progToBytes code2) :
    Assumptions countdownRiscVBackend.stackConf countdownRiscVBackend.dataConf (2^53-1) 24
      riscvConfig.addrOffset bs code (makeInit (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi (configuredMachineAsm code bs) (configuredLabMemory code bs)
      (fun a => configuredByteDomain bs a && holByteAligned a) (fun a => fixtureSharedByteDomain a && holByteAligned a)
      (configuredMachineState code bs) (configuredLab code cfg bs).code
      (LabToTarget.compile (fixtureMachineConfig (fixtureCodeStart code)).target.config)
      ((fixtureMachineConfig (fixtureCodeStart code)).target.getPc (configuredMachineState code bs) +
        BitVec.ofNat 64 (progToBytes code2).length) 0xecc (configuredLab code cfg bs).compileOracle) fixtureSavedRegs 0 (fixtureStackOracle cfg) := by
  rw [configuredCtorLab_eq code cfg bs bitmapFits code2 bytes]
  exact configuredTargetLab_assumptions code cfg bs _ (by simp only [sourceBase]; omega) good

private theorem configuredCtorStack_eq (code : List (Nat × HolProg 64)) (cfg : Config) (bs : List (BitVec 64))
    (bitmapFits : 0xa0020018 + bs.length*8 ≤ 0xa0410000) (code2 : LabProgHOL 64)
    (bytes : fixtureCodeBytes code = progToBytes code2) :
    (fullMakeInit countdownRiscVBackend.stackConf countdownRiscVBackend.dataConf (2^53-1) 24
      riscvConfig.addrOffset bs code {(makeInit (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi (configuredMachineAsm code bs) (configuredLabMemory code bs)
      (fun a => configuredByteDomain bs a && holByteAligned a) (fun a => fixtureSharedByteDomain a && holByteAligned a)
      (configuredMachineState code bs) (configuredLab code cfg bs).code
      (LabToTarget.compile (fixtureMachineConfig (fixtureCodeStart code)).target.config)
      ((fixtureMachineConfig (fixtureCodeStart code)).target.getPc (configuredMachineState code bs) +
        BitVec.ofNat 64 (progToBytes code2).length) 0xecc (configuredLab code cfg bs).compileOracle) with clock := 0} fixtureSavedRegs 0 (fixtureStackOracle cfg)).1 =
      configuredStack code cfg bs := by
  rw [withClock_of_eq _ 0 (makeInit_clock _ _ _ _ _ _ _ _ _ _ _ _), configuredCtorLab_eq code cfg bs bitmapFits code2 bytes]
  exact configuredTargetLab_stack code cfg bs _

noncomputable def configuredMachineContext (code : List (Nat × HolProg 64)) (cfg : Config) (bs : List (BitVec 64))
    (bitmapFits : 0xa0020018 + bs.length*8 ≤ 0xa0410000)
    (code2 : LabProgHOL 64) (labs : Spt (Spt Nat))
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code)
    (removed : removeLabels 5 riscvConfig 0 .ln [] (LabFilter.filterSkip (configuredLab code cfg bs).code) = some (code2,labs))
    (guards : LabMachineInitGuards (fixtureMachineConfig (fixtureCodeStart code)) (configuredMachineState code bs)
      (LabFilter.filterSkip (configuredLab code cfg bs).code) code2 labs 5 0 0xecc (configuredMachineAsm code bs)
      (configuredLabMemory code bs) (configuredByteDomain bs) fixtureSharedByteDomain
      (fun n => (((configuredLab code cfg bs).compileOracle n).1,
        LabFilter.filterSkip ((configuredLab code cfg bs).compileOracle n).2)) [] [] []) :
    FullInitMachineContext (configuredStack code cfg bs) :=
  cast (congrArg FullInitMachineContext (configuredCtorStack_eq code cfg bs bitmapFits code2 (fixtureCodeBytes_eq code code2 labs cfg removed)))
    (fullInitMachineContext_of_alignedFilteredLabInit (F := Unit)
      countdownRiscVBackend.stackConf countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset bs code
      fixtureSavedRegs 0 (fixtureStackOracle cfg) (fixtureMachineConfig (fixtureCodeStart code)) (configuredMachineState code bs)
      sourceFfi (configuredLab code cfg bs).code code2 labs
      5 0 0xecc 0 (configuredMachineAsm code bs) (configuredLabMemory code bs) (configuredByteDomain bs) fixtureSharedByteDomain
      (configuredLab code cfg bs).compileOracle [] [] [] rfl guards
      (configuredCtorAssumptions code cfg bs bitmapFits code2 good (fixtureCodeBytes_eq code code2 labs cfg removed)))



noncomputable def fixtureMachineContext (code : List (Nat × HolProg 64)) (cfg : Config)
    (code2 : LabProgHOL 64) (labs : Spt (Spt Nat))
    (good : StackToLab.Proofs.GoodCode.goodCode 24 code)
    (removed : removeLabels 5 riscvConfig 0 .ln [] (LabFilter.filterSkip (fixtureLab code cfg).code) = some (code2,labs))
    (guards : LabMachineInitGuards (fixtureMachineConfig (fixtureCodeStart code)) (fixtureMachineState code)
      (LabFilter.filterSkip (fixtureLab code cfg).code) code2 labs 5 0 0xecc (fixtureMachineAsm code)
      (fixtureLabMemoryFor code) fixtureByteDomain fixtureSharedByteDomain
      (fun n => (((fixtureLab code cfg).compileOracle n).1,
        LabFilter.filterSkip ((fixtureLab code cfg).compileOracle n).2)) [] [] []) :
    FullInitMachineContext (fixtureStack code cfg) := by
  have memEq := congrArg (fun lab => lab.memory) (configuredLab_one code cfg)
  change configuredLabMemory code [4] = fixtureLabMemoryFor code at memEq
  have guards' := guards
  rw [← configuredMachineState_one code, ← configuredMachineAsm_one code,
    ← memEq, ← configuredByteDomain_one] at guards'
  have ctx := configuredMachineContext code cfg [4] (by decide) code2 labs good removed guards'
  rw [configuredStack_one] at ctx
  exact ctx


/-- Derive the complete Lab machine guards from concrete compiler facts and
the already-proved machine initialization. -/
theorem configuredMachine_guards (code : List (Nat × HolProg 64)) (cfg : Config) (bs : List (BitVec 64))
    (bitmapFits : 0xa0020018 + bs.length * 8 ≤ 0xa0410000)
    (code2 : LabProgHOL 64) (labs : Spt (Spt Nat))
    (good : goodCode riscvConfig (.ln : Spt (Spt Nat)) (LabFilter.filterSkip (fixtureLab code cfg).code))
    (names : findFfiNames (LabFilter.filterSkip (fixtureLab code cfg).code) = [])
    (removed : removeLabels 5 riscvConfig 0 .ln [] (LabFilter.filterSkip (fixtureLab code cfg).code) = some (code2,labs))
    (info : getShmemInfo code2 0 [] [] = ([],[]))
    (noInstall : noInstallOrNoShareMem (LabFilter.filterSkip (fixtureLab code cfg).code) [])
    (cfgLabs : cfg.labels = labs) (cfgPos : cfg.pos = (progToBytes code2).length) (cfgFfi : cfg.ffiNames = some [])
    (fits : (fixtureCodeBytes code).length ≤ 61440) (aligned : (fixtureCodeBytes code).length % 4 = 0) :
    LabMachineInitGuards (fixtureMachineConfig (fixtureCodeStart code)) (configuredMachineState code bs)
      (LabFilter.filterSkip (fixtureLab code cfg).code) code2 labs 5 0 0xecc (configuredMachineAsm code bs)
      (configuredLabMemory code bs) (configuredByteDomain bs) fixtureSharedByteDomain
      (fun n => (((fixtureLab code cfg).compileOracle n).1,
        LabFilter.filterSkip ((fixtureLab code cfg).compileOracle n).2)) [] [] [] := by
  have bytes := fixtureCodeBytes_eq code code2 labs cfg removed
  have init := configuredMachine_goodInit code bs bitmapFits fits aligned
  rw [bytes] at init
  have mcok : mcConfOk (fixtureMachineConfig (fixtureCodeStart code)) := by
    apply riscvTarget_mcConfOk _ rfl <;> rfl
  have oracle := emptyLabCompilerOracleOk cfg labs (progToBytes code2).length riscvConfig [] cfgLabs cfgPos cfgFfi
  have oracle' : compilerOracleOk
      (fun n => (((fixtureLab code cfg).compileOracle n).1,
        LabFilter.filterSkip ((fixtureLab code cfg).compileOracle n).2)) labs (progToBytes code2).length
      (fixtureMachineConfig (fixtureCodeStart code)).target.config (fixtureMachineConfig (fixtureCodeStart code)).ffiNames := by
    simpa [fixtureLab,StackToLab.compileNoStubs,StackNames.compileHOL,LabFilter.filterSkip,
      fixtureMachineConfig,countdownMachineConfig,riscvTarget] using oracle
  refine ⟨good,mcok,fun _ => oracle',?_,removed,init,info,?_,?_,?_,?_,?_,noInstall,?_⟩
  · simp [names,fixtureMachineConfig,countdownMachineConfig,Flapjack.Misc.listSubset]
  · rfl
  · rfl
  · apply mmioPcsMinIndex_eq_some
    simp [fixtureMachineConfig,countdownMachineConfig,mmioIndexBoundary]
  · rfl
  · rfl
  · simp [fixtureMachineConfig,countdownMachineConfig]


/-- Derive the complete Lab machine guards from concrete compiler facts and
the already-proved machine initialization. -/
theorem fixtureMachine_guards (code : List (Nat × HolProg 64)) (cfg : Config)
    (code2 : LabProgHOL 64) (labs : Spt (Spt Nat))
    (good : goodCode riscvConfig (.ln : Spt (Spt Nat)) (LabFilter.filterSkip (fixtureLab code cfg).code))
    (names : findFfiNames (LabFilter.filterSkip (fixtureLab code cfg).code) = [])
    (removed : removeLabels 5 riscvConfig 0 .ln [] (LabFilter.filterSkip (fixtureLab code cfg).code) = some (code2,labs))
    (info : getShmemInfo code2 0 [] [] = ([],[]))
    (noInstall : noInstallOrNoShareMem (LabFilter.filterSkip (fixtureLab code cfg).code) [])
    (cfgLabs : cfg.labels = labs) (cfgPos : cfg.pos = (progToBytes code2).length) (cfgFfi : cfg.ffiNames = some [])
    (fits : (fixtureCodeBytes code).length ≤ 61440) (aligned : (fixtureCodeBytes code).length % 4 = 0) :
    LabMachineInitGuards (fixtureMachineConfig (fixtureCodeStart code)) (fixtureMachineState code)
      (LabFilter.filterSkip (fixtureLab code cfg).code) code2 labs 5 0 0xecc (fixtureMachineAsm code)
      (fixtureLabMemoryFor code) fixtureByteDomain fixtureSharedByteDomain
      (fun n => (((fixtureLab code cfg).compileOracle n).1,
        LabFilter.filterSkip ((fixtureLab code cfg).compileOracle n).2)) [] [] [] := by
  have memEq := congrArg (fun lab => lab.memory) (configuredLab_one code cfg)
  change configuredLabMemory code [4] = fixtureLabMemoryFor code at memEq
  have h := configuredMachine_guards code cfg [4] (by decide) code2 labs good names removed info noInstall
    cfgLabs cfgPos cfgFfi fits aligned
  rwa [configuredMachineState_one, configuredMachineAsm_one, memEq, configuredByteDomain_one] at h

end SteppedFlapjack.Concrete
