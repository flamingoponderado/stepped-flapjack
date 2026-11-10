import SteppedFlapjack.Concrete.FixtureMachineState
import SteppedFlapjack.LabToTargetSteps.InitializedRiscV

/-! Connect the init-e-shaped fixture Lab run to its concrete RISC-V machine. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Compiler.Encoders.RiscV.Target
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.LoopToWordSteps SteppedFlapjack.LabToTargetSteps

/-- A successful label-removal result identifies the exact loaded bytes. -/
theorem fixtureCodeBytes_eq (code : List (Nat × HolProg 64)) (code2 : LabProgHOL 64) (labs : Spt (Spt Nat)) (cfg : Config)
    (removed : removeLabels 5 riscvConfig 0 .ln [] (LabFilter.filterSkip (fixtureLab code cfg).code) = some (code2,labs)) :
    fixtureCodeBytes code = progToBytes code2 := by
  simp only [fixtureLab] at removed
  unfold fixtureCodeBytes
  rw [removed]

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



/-- The concrete initialized fixture forms a full Stack-to-machine context. -/
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
  let mc := fixtureMachineConfig (fixtureCodeStart code)
  let machine := fixtureMachineState code
  let asm := fixtureMachineAsm code
  let oracle := (fixtureLab code cfg).compileOracle
  let filteredOracle := fun n => ((oracle n).1, LabFilter.filterSkip (oracle n).2)
  let raw := makeInit mc sourceFfi asm (fixtureLabMemoryFor code) fixtureByteDomain fixtureSharedByteDomain
    machine (fixtureLab code cfg).code (compile riscvConfig) 0x800f0134 0xecc oracle
  let filtered := makeInit mc sourceFfi asm (fixtureLabMemoryFor code) fixtureByteDomain fixtureSharedByteDomain
    machine (LabFilter.filterSkip (fixtureLab code cfg).code) (compileLab riscvConfig) 0x800f0134 0xecc filteredOracle
  have bytes := fixtureCodeBytes_eq code code2 labs cfg removed
  have pos : mc.target.getPc machine + BitVec.ofNat 64 (progToBytes code2).length = 0x800f0134 := by
    change fixtureCodeStart code + BitVec.ofNat 64 (progToBytes code2).length = 0x800f0134
    rw [← bytes]
    exact fixtureCodeStart_add_length code
  have alignedD : ∀ a, decide (fixtureLabDomain a) = true → holByteAligned a = true := by
    intro a h
    exact fixtureLabDomain_aligned a (of_decide_eq_true h)
  have alignedS : ∀ a, decide (sharedAddress a) = true → holByteAligned a = true := by
    intro a h
    exact ((sharedAddress_alignment a).1 (of_decide_eq_true h)).1
  have labEq : fixtureTargetLab code cfg machine = LabProps.alignSdm (LabProps.alignDm raw) := by
    change fixtureTargetLab code cfg machine = LabProps.alignSdm (LabProps.alignDm (makeInit mc sourceFfi asm
      (fixtureLabMemoryFor code) (byteClosure (fun a => decide (fixtureLabDomain a)))
      (byteClosure (fun a => decide (sharedAddress a))) machine (fixtureLab code cfg).code
      (compile riscvConfig) 0x800f0134 0xecc oracle))
    rw [makeInit_byteClosure _ _ _ _ _ _ alignedD alignedS]
    rfl
  have filterRel : LabFilter.Proofs.stateRel filtered raw := by
    exact makeInit_filterRel mc sourceFfi asm (fixtureLabMemoryFor code) fixtureByteDomain fixtureSharedByteDomain
      machine (fixtureLab code cfg).code (compileLab riscvConfig) 0x800f0134 0xecc oracle
  have machineRel := makeInit_stateRel mc machine sourceFfi (LabFilter.filterSkip (fixtureLab code cfg).code)
    code2 labs 5 0 0xecc asm (fixtureLabMemoryFor code) fixtureByteDomain fixtureSharedByteDomain
    filteredOracle [] [] [] guards
  have tie := oracleTie_makeInit mc sourceFfi asm (fixtureLabMemoryFor code) fixtureByteDomain fixtureSharedByteDomain
    machine (LabFilter.filterSkip (fixtureLab code cfg).code) (compileLab riscvConfig)
    0x800f0134 0xecc filteredOracle
  refine {
    stackConf := countdownRiscVBackend.stackConf, dataConf := countdownRiscVBackend.dataConf,
    maxHeap := 2^53-1, sp := 24, offset := riscvConfig.addrOffset, bitmaps := [4], inputCode := code,
    lab := fixtureTargetLab code cfg machine, saveRegs := fixtureSavedRegs, dataSp := 0,
    coracle := fixtureStackOracle cfg,
    initAssumptions := fixtureTargetLab_assumptions code cfg machine good,
    stackEq := (fixtureTargetLab_stack code cfg machine).symm,
    pc := mc.target.getPc machine, mc := mc, labCode := code2, labs := labs, asm := asm, machine := machine,
    hmc := rfl, machineLab := filtered, labRelation := ?_, tie := tie, machineRel := ?_ }
  · exact Or.inr (Or.inr (Or.inr ⟨raw,labEq,filterRel⟩))
  · rw [pos] at machineRel
    change stateRel (mc,code2,labs,mc.target.getPc machine) filtered asm machine at machineRel
    exact machineRel

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
  have bytes := fixtureCodeBytes_eq code code2 labs cfg removed
  have init := fixtureMachine_goodInit code fits aligned
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

end SteppedFlapjack.Concrete
