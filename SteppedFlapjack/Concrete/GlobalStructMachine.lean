import SteppedFlapjack.Concrete.GlobalStructConfiguredWord
import SteppedFlapjack.Concrete.GlobalNamedStruct
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordToWord
open Flapjack.WordToStackProofs Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInit
open SteppedFlapjack SteppedFlapjack.Concrete SteppedFlapjack.PanToCrepSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordToStackSteps
open SteppedFlapjack.StackSteps SteppedFlapjack.WordSimpSteps Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.WordDepth Flapjack.Compiler.Backend.WordDepth.Executable
open Flapjack.Compiler.Backend.BackendProps
namespace SteppedFlapjack.Concrete
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
private theorem sourceGood : pancakeGoodCodeHOL globalStructProgram = true := by
  with_unfolding_all decide
private theorem entryLookup (cfg : LabToTarget.Config) :
    sptLookup 64 (configuredWord globalStructNativeCode globalStructOptimizedWords cfg globalStructNativeBitmaps).code = some (1,globalStructNativeEntry) := by
  change sptLookup 64 (sptFromAList globalStructOptimizedWords) = some (1,globalStructNativeEntry)
  unfold globalStructNativeEntry
  rw [globalStruct_optimizedTable]
  simp [sptLookup_sptFromAList,sptAListLookup]
private theorem configuredMachine (cfg : LabToTarget.Config)
    (filtered : LabSem.State 64 LabToTarget.Config Unit)
    (pc : BitVec 64) (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (labCode : LabSem.LabProgHOL 64) (labs : Spt (Spt Nat)) (asm : AsmState 64) (machine : RiscV.L3.riscv_state)
    (hmc : mc.target = riscvTarget)
    (link : LabToTargetSteps.LabExecutionLink filtered (configuredTargetLab globalStructNativeCode cfg globalStructNativeBitmaps machine))
    (tie : LabToTarget.oracleTie mc machine filtered)
    (rel : LabToTarget.stateRel (mc,labCode,labs,pc) filtered asm machine) :
    let words := globalStructOptimizedWords
    let code := globalStructNativeCode
    let bs := globalStructNativeBitmaps
    let limit := globalStructActualOptimizedLimit
    let allowance := (max 1 (wordCodeWeight (sptFromAList words)) + 1) * (6*limit+1) + 1
    let n := 1 + max 1 (stackCodeWeight (sptFromAList code)) * (6*limit+1 + allowance)
    ∃ finalMachine finalFfi,
      evaluateTargetHOL mc sourceFfi (LabToTargetSteps.labTickBound 4 labCode filtered.codeBuffer *
        StackToLabSteps.stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset
          bs code (fixtureStackOracle cfg) n) machine = (.halt .success,finalMachine,finalFfi) ∧
      finalFfi.ioEvents = sourceFfi.ioEvents := by
  let raw := globalStructActualWordPrograms
  let words := globalStructOptimizedWords
  let code := globalStructNativeCode
  let bs := globalStructNativeBitmaps
  let tail := bs.drop 1
  let entry := globalStructNativeEntry
  let frame := globalStructNativeEntryFrame
  let frames := globalStructNativeFrameSizes
  let limit := globalStructActualOptimizedLimit
  let source := {(configuredWord code words cfg bs) with clock := 6*limit+1}
  let call : WordLangProgHOL (BitVec 64) := .call none (some 64) [0] none
  let wordPost := (WordSemStateFiniteExact.evaluate call source).2
  have run : WordSemStateFiniteExact.evaluate call source = (some (.result (.loc 1 0) [.word 8]),wordPost) := by
    apply Prod.ext
    · exact (globalStruct_configuredWordRun cfg).1
    · rfl
  have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
  have wordsEq : words = (compile phase3WordConfig riscvConfig raw).2 := by
    simp [words,raw,globalStructOptimizedWords,compileWith_eq_compile _ allocator]
  have bsHeader : bs = 4 :: tail := nativeBitmaps_header words
  have fits : 0xa0020018 + bs.length*8 ≤ sourceBase := globalStruct_bitmapFits
  have good : StackToLab.Proofs.GoodCode.goodCode 24 code := globalStruct_nativeGood
  have frameLookup : sptLookup 64 (configuredWord code words cfg bs).stackSize = some frame := globalStruct_frameLookup cfg
  have lookup : sptLookup 64 (configuredWord code words cfg bs).code = some (1,entry) := entryLookup cfg
  have noStubs := compiledWord_noStubs riscvConfig.isa globalStructCallPrograms
  have fields := configuredStack_code_and_bitmaps code cfg bs fits good
  have initOk := configuredStack_nativeInitOk code cfg tail (by simpa [bsHeader] using fits) good
  have related := wholeWordStack_initStateRel phase3WordConfig riscvConfig raw
    (configuredStack code cfg bs) (configuredWordOracle cfg bs) noStubs.1 noStubs.2
    (by rw [fields.1, ← wordsEq]; rfl) (by rw [fields.2, ← wordsEq]; exact List.prefix_refl _) (by simpa [bsHeader] using initOk)
  have clockRelated := stateRel_setClocks riscvConfig (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length))
    0 0 _ _ [] 0 (6*limit+1) related
  have targetSafe := wholeCompile_targetSafety phase3WordConfig riscvConfig raw (loopToWord_programSafety _)
  have safe : safeWordCode source := by
    simpa [source,configuredWord,Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit,safeWordCode,wordsEq] using
      ⟨targetSafe.2.1,targetSafe.1⟩
  have noAlloc : WordProps.noAllocCode source.code := by
    simpa [source,configuredWord,Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit,wordsEq] using targetSafe.2.2
  have args : WordSemStateFiniteExact.getVars [0] source = some [(.loc 1 0)] := by
    simp [source,configuredWord,Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit,WordSemStateFiniteExact.getVars,WordSemStateFiniteExact.getVar,sptLookup]
  have loc : BvlToBvi.initGlobalsLocation = 64 := by decide
  have capacity : optionLe (optionMap₂ max (some (max 1 (1+frame)))
      (optionMap₂ (· + ·) (some 1) (fullCallGraphDepth frames 64 (sptFromAList words))))
      (some (configuredStack code cfg bs).stack.length) := by
    rw [configuredStack_stackLength code cfg bs fits good]
    exact globalStruct_nativeCapacity
  have machineCapacity : let t := callEnv [(.loc 1 0 : WordLocW 64)] (some frame) (decClock source)
      optionLe (optionMap₂ max t.stackMax (optionMap₂ (· + ·) (wordSemStackSize t.stack)
        (fullCallGraphDepth t.stackSize 64 t.code))) (some t.stackLimit) := by
    simpa [source,configuredWord,Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit,
      WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.decClock,wordSemStackSize,wordSemOptionMax,
      wordSemOptionAdd,frames,globalStructNativeFrameSizes,words] using capacity
  have hA := configuredTargetLab_assumptions code cfg bs machine fits good
  obtain ⟨finalMachine,finalFfi,machineRun,events⟩ := wordStart_riscv_explicit riscvConfig
    (riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)) countdownRiscVBackend.stackConf
    countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset bs code (configuredTargetLab code cfg bs machine) filtered
    fixtureSavedRegs 0 (fixtureStackOracle cfg) (by intro i; rfl) hA source wordPost
    (some (.result (.loc 1 0) [.word 8])) .success (by rw [configuredTargetLab_stack]; simpa [source,configuredWord,wordsEq] using clockRelated)
    safe noAlloc (by simpa [call,loc] using run)
    (by simp) (by simp) entry frame (.loc 1 0) (by simpa [source,loc] using lookup)
    (by simpa [source,loc] using frameLookup) args (by simp [source]) machineCapacity (by rfl)
    pc mc labCode labs asm machine hmc link tie rel
  have allowanceEq : callTableBudget (.call none (some 64) [0] none) source =
      (max 1 (wordCodeWeight (sptFromAList words)) + 1) * (6*limit+1) + 1 := by
    simp [callTableBudget,wordControlWeight,source,configuredWord,
      Flapjack.Compiler.Backend.WordToStack.Native.Initialization.makeInit,words]
  simp only [loc] at machineRun
  rw [allowanceEq] at machineRun
  have wordFfi : wordPost.ffi = sourceFfi := (globalStruct_configuredWordRun cfg).2
  refine ⟨finalMachine,finalFfi,?_,(by simpa [wordFfi] using events)⟩
  simpa [configuredTargetLab_shape,configuredLab,fixtureLab,source,words,raw,bs,code,limit] using machineRun
theorem globalStruct_actualMachine :
    let code := globalStructNativeCode
    let bs := globalStructNativeBitmaps
    let words := globalStructOptimizedWords
    let limit := globalStructActualOptimizedLimit
    let allowance := (max 1 (wordCodeWeight (sptFromAList words)) + 1) * (6*limit+1) + 1
    let n := 1 + max 1 (stackCodeWeight (sptFromAList code)) * (6*limit+1 + allowance)
    ∃ finalMachine finalFfi,
      evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi
        (948 * StackToLabSteps.stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset
          bs code (fixtureStackOracle (fixtureCompilerConfig code)) n) (configuredMachineState code bs) =
            (.halt .success,finalMachine,finalFfi) ∧ finalFfi.ioEvents = sourceFfi.ioEvents := by
  let code := globalStructNativeCode
  let bs := globalStructNativeBitmaps
  let cfg := fixtureCompilerConfig code
  have allocator : Flapjack.RegAlloc.regAllocExecutable = Flapjack.RegAlloc.regAlloc := by
    funext a b c d e f g
    exact Flapjack.RegAlloc.regAllocExecutable_eq a b c d e f g
  have labGood : LabToTarget.goodCode riscvConfig (.ln : Spt (Spt Nat))
      (LabFilter.filterSkip (fixtureLab code cfg).code) := by
    have h := source_labGoodCode globalStructProgram globalStructActualWordPrograms globalStruct_rawWords sourceGood globalStruct_sourceUnique
    simpa [fixtureLab,code,cfg,globalStructNativeCode,globalStructOptimizedWords,compileWith_eq_compile _ allocator,phase3WordConfig_eq] using h
  have fits : 0xa0020018 + bs.length*8 ≤ 0xa0410000 := by
    change 0xa0020018 + (compileNative riscvConfig false globalStructOptimizedWords).1.length*8 ≤ 0xa0410000
    rw [globalStruct_nativeBitmap]
    decide
  have facts : (fixtureRemoveLabels code).isSome = true ∧ (fixtureCodeBytes code).length ≤ 0xecc ∧
      (fixtureCodeBytes code).length % 4 = 0 := globalStruct_nativeCompilerFacts
  have removed : LabToTarget.removeLabels 5 riscvConfig 0 .ln []
      (LabFilter.filterSkip (configuredLab code cfg bs).code) =
      some ((fixtureCompiled code).1,(fixtureCompiled code).2) := fixtureRemoveLabels_eq code facts.1
  have guards := configuredMachine_allGuards code bs fits labGood globalStruct_nativeSafe facts
  obtain ⟨filtered,link,tie,rel,buffer⟩ := configuredMachine_relations code cfg bs fits
    (fixtureCompiled code).1 (fixtureCompiled code).2 globalStruct_nativeGood removed guards
  have result := configuredMachine cfg filtered (fixtureCodeStart code) (fixtureMachineConfig (fixtureCodeStart code))
    (fixtureCompiled code).1 (fixtureCompiled code).2 (configuredMachineAsm code bs)
    (configuredMachineState code bs) rfl link tie rel
  simp only [buffer,fixtureLabMachineFactor code facts.2.1] at result
  exact result

/-- The native witness uses the actual Word compilation of the named source. -/
theorem namedGlobalStruct_rawWords :
    panToWordCompileProgHOL riscvConfig.isa namedGlobalStructProgram = globalStructActualWordPrograms := by
  unfold panToWordCompileProgHOL globalStructActualWordPrograms globalStructCallPrograms
  dsimp only
  rw [namedGlobalStruct_pipeline]

/-- The named-struct source and its actual RISC-V compilation terminate with
    the same I/O events at an explicit bound derived from the generated code. -/
theorem namedGlobalStruct_source_machine :
    let code := globalStructNativeCode
    let bs := globalStructNativeBitmaps
    let words := globalStructOptimizedWords
    let limit := globalStructActualOptimizedLimit
    let allowance := (max 1 (wordCodeWeight (sptFromAList words)) + 1) * (6*limit+1) + 1
    let n := 1 + max 1 (stackCodeWeight (sptFromAList code)) * (6*limit+1 + allowance)
    ∃ finalMachine finalFfi,
      evaluateTargetHOL (fixtureMachineConfig (fixtureCodeStart code)) sourceFfi
        (948 * StackToLabSteps.stackLabTickLimit countdownRiscVBackend.dataConf (2^53-1) 24 riscvConfig.addrOffset
          bs code (fixtureStackOracle (fixtureCompilerConfig code)) n) (configuredMachineState code bs) =
            (.halt .success,finalMachine,finalFfi) ∧
      semanticsDecls globalStructBase (ofString "main") namedGlobalStructProgram =
        .terminate .success finalFfi.ioEvents := by
  obtain ⟨machine,ffi,run,events⟩ := globalStruct_actualMachine
  refine ⟨machine,ffi,run,?_⟩
  rw [events]
  exact namedGlobalStruct_semantics

end SteppedFlapjack.Concrete
