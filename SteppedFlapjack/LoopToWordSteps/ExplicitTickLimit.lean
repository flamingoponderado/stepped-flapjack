import SteppedFlapjack.StackRemoveSteps.ExplicitFields
import SteppedFlapjack.LoopToWordSteps.FullInitNativeSetup
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitAny
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackRemove.Proofs
open SteppedFlapjack.StackRemoveSteps.CompCorrect SteppedFlapjack.StackAllocSteps
open SteppedFlapjack.WordToStackSteps SteppedFlapjack.LabToTargetSteps SteppedFlapjack.StackToLabSteps
open SteppedFlapjack.WordAllocSteps

/-- A tick bound calculated from compiler data and source syntax, without an execution state. -/
noncomputable def explicitTickLimit
    (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec 64 × BitVec 64) (bitmaps : List (BitVec 64))
    (inputCode : List (Nat × HolProg 64))
    (oracle : Nat → LabToTarget.Config × List (Nat × HolProg 64) × List (BitVec 64))
    (labCode : LabSem.LabProgHOL 64) (buffer : WordSemBuffer 64 8)
    (wc : WordToWord.Config) (ac : AsmConfigExact 64)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (p : HolLoopProg 64) (ctxt : Spt Nat) (labels : Nat × Nat) (limit : Nat) : Nat :=
  let k := ac.regCount-(5+ac.avoidRegs.length)
  let compiledCode := sptFromAList (compile wc ac programs).2
  let out := (fullCompileSingle ac.twoRegArith k wc.regAlg ac
    ((firstLoopName,1,(LoopToWord.compHOL ctxt p labels).1),entryColour wc programs firstLoopName)).2.2
  let bitmap := (nativeEntryBitmap ac false k firstLoopName (compile wc ac programs).2 (.list [4],1)).getD (.list [],0)
  let frame := max (maxVarHOL out / 2 + 1-k) (1-k)
  let frameSize := if frame = 0 then 0 else frame+1
  let stackLimit := tailStackReplayLimit ac 1 firstLoopName wc.regAlg k (entryColour wc programs firstLoopName)
    p ctxt labels compiledCode limit
  let cost := uniformFactor (width := 64) dc *
    (3 + callSequenceCost ac stackLimit (sptFromAList inputCode) out bitmap (k,frameSize,frame))
  let code := sptFromAList (code1 dc inputCode)
  let co := coracle1 oracle
  let runCost := max (costFromFields offset cost (.call none (.inl firstLoopName) none) code bitmaps co)
    (costFromFields offset cost (.call none (.inl firstLoopName) none) code [4] co)
  labTickBound 4 labCode buffer * (flattenStepFactor *
    (2 + loopOnlyCost 0 (initCode (StackToLab.isGenGc dc.gcKind) maxHeap sp : HolProg 64) + runCost * cost + 4))

/-- The existing simulation bound is bounded by the explicit compiler calculation. -/
theorem FullInitMachineContext.successTickLimit_le_explicit {F : Type}
    {stack : StackSemStateFiniteExact 64 LabToTarget.Config F} (backend : FullInitMachineContext stack)
    (wc : WordToWord.Config) (ac : AsmConfigExact 64)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (p : HolLoopProg 64) (ctxt : Spt Nat) (labels : Nat × Nat) (limit : Nat) :
    backend.successTickLimit wc ac programs p ctxt labels limit ≤
      explicitTickLimit backend.dataConf backend.maxHeap backend.sp backend.offset backend.bitmaps
        backend.inputCode backend.coracle backend.labCode backend.lab.codeBuffer wc ac programs p ctxt labels limit := by
  have codeEq : stack.code = sptFromAList backend.inputCode := by
    have eq := congrArg (fun s => s.code) backend.stackEq
    simpa only [fullMakeInit_eq,StackAlloc.makeInit] using eq
  simp only [FullInitMachineContext.successTickLimit,explicitTickLimit,codeEq]
  apply Nat.mul_le_mul_left
  apply Nat.mul_le_mul_left
  apply Nat.add_le_add_right
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul_right
  exact makeInitAny_cost_bounded (StackToLab.isGenGc backend.dataConf.gcKind) backend.stackConf.jump
    backend.maxHeap backend.bitmaps backend.dataSp (coracle1 backend.coracle) backend.offset backend.sp
    (sptFromAList (code1 backend.dataConf backend.inputCode))
    (s2 backend.stackConf backend.dataConf backend.maxHeap backend.sp backend.offset backend.inputCode
      backend.lab backend.saveRegs backend.coracle) _ (.call none (.inl firstLoopName) none)
end SteppedFlapjack.LoopToWordSteps

