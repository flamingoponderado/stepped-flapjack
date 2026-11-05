import SteppedFlapjack.StackRemoveSteps.InitEntrySteps
namespace SteppedFlapjack.StackRemoveSteps
open Flapjack Flapjack.StackSemStateOps Flapjack.StackSemEvaluate Flapjack.StackSemControl
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs

/-- The compiler's initialization bundles imply the concrete preconditions of
the stack-removal initializer. -/
theorem initHypOfBundles {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (gen : Bool)
    (maxHeap pointer start : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (code : List (Nat × HolProg width)) (s : StackSemStateFiniteExact width C F)
    (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (hyp : InitMake.dischargeThese jump bounds gen maxHeap pointer start oracle code s ∧
      InitMake.propagateThese s bitmaps dataSpace) :
    InitMake.initPre gen maxHeap bitmaps dataSpace pointer start s ∧
      s.compileOracle = (fun index => let entry := oracle index
        (entry.1, entry.2.1.map (progComp jump bounds pointer), entry.2.2)) ∧
      (∀ (n i : Nat) (p : HolProg width), (i, p) ∈ (oracle n).2.1 →
        StackProps.regBound p pointer ∧ stackNumStubs ≤ i + 1) ∧
      sptLookup stackErrLab s.code = some (haltInst (BitVec.ofNat width 2)) ∧
      codeRelHOL jump bounds pointer (sptFromAList code) s.code := by
  obtain ⟨⟨every, oracleBound, oracleEq, codeEq, k8, entry1, save, noStack, noStore, noAlloc,
    maxOk⟩, good, ptr2, ptr3, ptr4, bp, r2, r3, r4, m0, m1, m2, m3, m4, cbEmpty, le, al2, al4,
    albp, big, heap⟩ := hyp
  refine ⟨⟨?_, ?_, maxOk⟩, oracleEq, oracleBound, ?_,
    InitCodeRelation.impCodeRel jump bounds gen maxHeap pointer start code s.code ⟨every, codeEq⟩⟩
  · rw [codeEq, sptLookup_sptFromAList]
    simp [compileHOL, initStubs, sptAListLookup]
  · have sub : -1 * ptr2 + ptr4 = ptr4 - ptr2 := by
      rw [BitVec.neg_mul]; simp [BitVec.sub_eq_add_neg, BitVec.add_comm]
    rw [sub] at heap
    exact ⟨ptr2, ptr3, ptr4, bp, good, k8, entry1, save, noStack, noStore, noAlloc, r2, r3, r4,
      m0, m1, m2, m3, m4, le, big, al2, al4, albp, cbEmpty, heap⟩
  · rw [codeEq, sptLookup_sptFromAList]
    simp [compileHOL, initStubs, sptAListLookup, stackErrLab]
end SteppedFlapjack.StackRemoveSteps
