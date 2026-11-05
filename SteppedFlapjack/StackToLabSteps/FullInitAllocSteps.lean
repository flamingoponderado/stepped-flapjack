import SteppedFlapjack.StackAllocSteps.MakeInitEntrySteps
import SteppedFlapjack.StackToLabSteps.FullInitRemoveLabSteps
namespace SteppedFlapjack.StackToLabSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs Flapjack.Compiler.Backend.StackAlloc
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.Compiler.Backend.StackToLab.Proofs Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open SteppedFlapjack.StackSteps SteppedFlapjack.StackAllocSteps

/-- Allocation's initialized entry simulation, with its premises derived
from the original full compiler initialization bundle. -/
theorem fullInitAllocEntryWithin {width : Nat} [NeZero width] {C F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (lab : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (hwidth : 8 ≤ width)
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code lab saveRegs dataSp coracle) :
    let base := InitMake.makeInitAny (StackToLab.isGenGc dataConf.gcKind) maxHeap bitmaps dataSp
      (coracle1 coracle) stackConf.jump offset sp (sptFromAList (code1 dataConf code))
      (s2 stackConf dataConf maxHeap sp offset code lab saveRegs coracle)
    let input := StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle base
    ∀ (k n : Nat) (res : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F),
      evaluate ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width), {input with clock := k}) = (res, post) →
      res ≠ some .error →
      steps ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width), {input with clock := k}) ≤ n →
      ∃ extra targetPost,
        evaluate ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width), {base with clock := k + extra}) =
          (res, targetPost) ∧ targetPost.ffi = post.ffi ∧
        steps ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width), {base with clock := k + extra}) ≤
          uniformFactor (width := width) dataConf * n := by
  dsimp only
  intro k n res post run nonError hsteps
  let base := InitMake.makeInitAny (StackToLab.isGenGc dataConf.gcKind) maxHeap bitmaps dataSp
    (coracle1 coracle) stackConf.jump offset sp (sptFromAList (code1 dataConf code))
    (s2 stackConf dataConf maxHeap sp offset code lab saveRegs coracle)
  have bundles := And.intro (dischargeThese_s2 hA) (propagateThese_s2 hA)
  obtain ⟨initialized, hopt, _⟩ := InitSemantics.makeInitSemantics stackConf.jump offset
    (StackToLab.isGenGc dataConf.gcKind) maxHeap sp BvlToBvi.initGlobalsLocation
    (coracle1 coracle) (code1 dataConf code) (s2 stackConf dataConf maxHeap sp offset code lab saveRegs coracle)
    bitmaps dataSp bundles
  have hbase : base = initialized := by simp [base, InitMake.makeInitAny, hopt]
  obtain ⟨initPost, hpost, hprop⟩ := InitAny.makeInitOpt_eq_some hopt
  rw [hpost] at hprop
  have hbuf : base.bitmaps.length + base.dataBuffer.buffer.length + base.dataBuffer.spaceLeft < 2 ^ width - 1 := by
    rw [hbase, hpost]
    rcases hprop with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hdb, _, _, _, hbl, _⟩
    simp only [InitReduce.initReduce] at hbl hdb ⊢
    simp only [List.length_nil, Nat.add_zero]
    omega
  have hst : base.stack.length * (width / 8) < 2 ^ width := by
    rw [hbase, hpost]
    rcases hprop with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, hsb, _⟩
    exact hsb
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hgood, hgoodO, -, -, -, -, -, -, -, -⟩ := hA
  have hcode : ∀ key prog, sptAListLookup key (StackRawCall.compile code) = some prog →
      key ≠ gcStubLocation ∧ StackProps.allocArg prog := by
    intro key prog hk
    obtain ⟨⟨n0, p0⟩, hm0, he⟩ := List.mem_map.mp (sptAListLookup_mem hk)
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨hstub, hal⟩ := hgood.2.1 _ hm0
    refine ⟨by simp only [stackNumStubs, gcStubLocation] at hstub ⊢; omega,
      (StackRawCall.callArgComp _ _).2.mpr hal⟩
  have horacle : ∀ i key prog, (key, prog) ∈ (coracle i).2.1 →
      key ≠ gcStubLocation ∧ StackProps.allocArg prog := by
    intro i key prog hp
    obtain ⟨hstub, hal⟩ := (hgoodO i).2.1 _ hp
    exact ⟨by simp only [stackNumStubs, gcStubLocation] at hstub ⊢; omega, hal⟩
  have hu := InitAny.makeInitAnyUseStack (StackToLab.isGenGc dataConf.gcKind) maxHeap bitmaps dataSp
    (coracle1 coracle) stackConf.jump offset sp (sptFromAList (code1 dataConf code))
    (s2 stackConf dataConf maxHeap sp offset code lab saveRegs coracle)
  have hus := InitAny.makeInitAnyUseStore (StackToLab.isGenGc dataConf.gcKind) maxHeap bitmaps dataSp
    (coracle1 coracle) stackConf.jump offset sp (sptFromAList (code1 dataConf code))
    (s2 stackConf dataConf maxHeap sp offset code lab saveRegs coracle)
  have hua := InitAny.makeInitAnyUseAlloc (StackToLab.isGenGc dataConf.gcKind) maxHeap bitmaps dataSp
    (coracle1 coracle) stackConf.jump offset sp (sptFromAList (code1 dataConf code))
    (s2 stackConf dataConf maxHeap sp offset code lab saveRegs coracle)
  have hcd := InitAny.makeInitAnyCode (StackToLab.isGenGc dataConf.gcKind) maxHeap bitmaps dataSp
    (coracle1 coracle) stackConf.jump offset sp (sptFromAList (code1 dataConf code))
    (s2 stackConf dataConf maxHeap sp offset code lab saveRegs coracle)
  have hco := InitAny.makeInitAnyCompileOracle (StackToLab.isGenGc dataConf.gcKind) maxHeap bitmaps dataSp
    (coracle1 coracle) stackConf.jump offset sp (sptFromAList (code1 dataConf code))
    (s2 stackConf dataConf maxHeap sp offset code lab saveRegs coracle)
  exact makeInitEntryWithinSteps (StackRawCall.compile code) coracle base dataConf hwidth
    BvlToBvi.initGlobalsLocation k n res post hcode horacle hu hus (by simpa using hua)
    (by simpa [base, code1] using hcd) (by simpa [base, coracle1] using hco) hbuf hst run nonError hsteps
end SteppedFlapjack.StackToLabSteps
