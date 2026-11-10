import SteppedFlapjack.Concrete.Phase7Stack
import SteppedFlapjack.Concrete.FixtureStackLab

/-! Affine form of the code-derived machine bound. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.PanToCrepSteps SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps
open SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordToStackSteps SteppedFlapjack.StackToLabSteps SteppedFlapjack.WordSimpSteps
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open SteppedFlapjack.StackAllocSteps SteppedFlapjack.StackRemoveSteps.CompCorrect

/-- Machine ticks calculated from the source budget and generated code. -/
noncomputable def supportedMachineTicks (program : Prog (RiscV.Word 64)) (n : Nat) : Nat :=
  let code := (supportedNative program).2.2.2
  948 * fixtureLabTickLimit code (fixtureCompilerConfig code) (supportedStackBound program n)

/-- Coefficient of the source visit count in the machine bound. -/
noncomputable def supportedMachineFactor (program : Prog (RiscV.Word 64)) : Nat :=
  let body := progToHOL (panSimpProg program)
  let ctxt := witnessLoopContext riscvConfig.isa body
  let callee := supportedCallee body
  let crepWeight := CrepSteps.statementWeight callee
  let loopWeight := loopVisitWeight (optimiseHOL (compileHOLExact (ctxtFcExact ctxt.target ctxt.funcs [] []) .ln callee))
  let loops := twoLoopPrograms riscvConfig.isa (ofString "main") (entryName body) callee
  let words := loopToWordCompileHOL loops
  let k := riscvConfig.regCount-(5+riscvConfig.avoidRegs.length)
  let entryOut := (fullCompileSingleWith Flapjack.RegAlloc.regAllocExecutable riscvConfig.twoRegArith k phase3WordConfig.regAlg riscvConfig
    ((64,1,loopToWordCompFuncHOL 64 [] branchingLoopEntry),entryColour phase3WordConfig words 64)).2.2
  let calleeOut := (fullCompileSingleWith Flapjack.RegAlloc.regAllocExecutable riscvConfig.twoRegArith k phase3WordConfig.regAlg riscvConfig
    ((65,1,loopToWordCompFuncHOL 65 [] (twoCallee riscvConfig.isa (ofString "main") (entryName body) callee)),entryColour phase3WordConfig words 65)).2.2
  let wordFactor := wordControlWeight entryOut * (wordControlWeight calleeOut+1)
  let nativeCode := (supportedNative program).2.2.2
  let nativeEntry := nativeTailEntryCode countdownRiscVBackend.wordToWordConf riscvConfig (supportedWordPrograms program) 64 supportedEntry
  let nativeFactor := callSequenceCost riscvConfig 0
    (sptFromAList (compileNative riscvConfig false (compile countdownRiscVBackend.wordToWordConf riscvConfig (supportedWordPrograms program)).2).2.2.2)
    nativeEntry (nativeTailEntryBitmap countdownRiscVBackend.wordToWordConf riscvConfig (supportedWordPrograms program) 64)
    (k,nativeEntryFrameSize k nativeEntry,nativeEntryFrame k nativeEntry)
  let cfg := fixtureCompilerConfig nativeCode
  let generated := sptFromAList (code1 countdownRiscVBackend.dataConf nativeCode)
  let labFactor := costFromFields riscvConfig.addrOffset 0 (.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64)
    generated [4] (coracle1 (fixtureStackOracle cfg))
  948 * flattenStepFactor * labFactor * uniformFactor (width := 64) countdownRiscVBackend.dataConf * nativeFactor *
    wordFactor * 6 * loopWeight * (crepWeight + 3 * loopWeight * crepWeight)

/-- The remaining part of the bound depends on code and configuration alone. -/
noncomputable def supportedMachineOffset (program : Prog (RiscV.Word 64)) : Nat := supportedMachineTicks program 0

set_option maxHeartbeats 1500000 in
/-- The full composed machine bound is affine in the source visit budget. -/
theorem supportedMachineTicks_affine (program : Prog (RiscV.Word 64)) (n : Nat) :
    supportedMachineTicks program n = supportedMachineFactor program * n + supportedMachineOffset program := by
  simp only [supportedMachineOffset,supportedMachineTicks,fixtureLabTickLimit,supportedStackBound,
    nativeTailEntryBound,supportedWordBound,twoProgramWordBound,supportedLoopVisits,supportedLoopBudget,
    supportedCrepBudget,supportedMachineFactor]
  ring
end SteppedFlapjack.Concrete
