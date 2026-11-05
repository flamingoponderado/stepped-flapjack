import SteppedFlapjack.StackRemoveSteps.StoreConstsSteps
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.StoreConsts

/-! Step-bounded constant-store simulation, adapted from the original
stack-removal correctness proof using the proved copy-loop step bound. `B`
bounds the actual source bitmap list for this run. -/

namespace SteppedFlapjack.StackRemoveSteps.CompCorrect
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Encoders.Asm Flapjack.StackSemEvaluate Flapjack.StackSemStateOps
open Flapjack.Compiler.Backend.StackRemove.CompCorrect
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.StoreConsts
open SteppedFlapjack.StackSteps SteppedFlapjack.StackRemoveSteps
set_option maxHeartbeats 2000000
theorem compCorrectStoreConstsWithinSteps {width : Nat} [NeZero width] {C F : Type}
    (temporary bitmap : Nat) (stub : Option Nat)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (B : Nat) (bitmapLength : source.bitmaps.length ≤ B)
    (hypothesis : evaluate (.storeConsts temporary bitmap stub, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      StackProps.regBound (.storeConsts temporary bitmap stub : HolProg width) pointer) :
    ∃ clock postTarget,
      evaluate (comp jump bounds pointer (.storeConsts temporary bitmap stub),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) ∧
      steps (comp jump bounds pointer (.storeConsts temporary bitmap stub),
        {target with clock := clock + target.clock}) ≤ storeConstsSteps width B := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  change 3 < pointer ∧ temporary < pointer ∧ bitmap < pointer at bound
  have notAlloc : source.useAlloc = false := relation.2.2.2.2.2.1
  rw [evaluate_storeConsts] at sourceRun
  rw [if_neg (by simp [relation.2.1])] at sourceRun
  cases stub with
  | some label =>
    simp only [notAlloc, Bool.false_eq_true, not_false_eq_true,
      Option.isSome_some, and_self, if_true] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, and_false, if_false,
      StackSemStoreConstsGuard.checkStoreConstsOpt, not_true_eq_false] at sourceRun
    unfold StackSemStoreConsts.storeConstSem at sourceRun
    split at sourceRun
    next invalid => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
    next distinct =>
      have distinct : [0, 1, 2, 3, temporary, bitmap].Nodup := by simpa only [not_not] using distinct
      split at sourceRun
      next _ _ _ index address offset read1 read2 read3 =>
        cases copySource : StackSemStoreConsts.copyWordsExact index.toNat address offset
            source.bitmaps (fun key => source.mdomain key = true) source.memory with
        | none =>
          simp only [copySource] at sourceRun
          exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        | some output =>
          rcases output with ⟨finalAddress, finalMemory⟩
          simp only [copySource] at sourceRun
          rw [if_neg (by simp [notAlloc])] at sourceRun
          simp only [id_eq] at sourceRun
          have loopDistinct : [1, 2, 3, temporary, bitmap].Nodup :=
            (List.nodup_cons.mp distinct).2
          have bOne : bitmap ≠ 1 := by
            simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
            omega
          have bTwo : bitmap ≠ 2 := by
            simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
            omega
          have bThree : bitmap ≠ 3 := by
            simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
            omega
          have tOne : temporary ≠ 1 := by
            simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
            omega
          have tTwo : temporary ≠ 2 := by
            simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
            omega
          have tb : temporary ≠ bitmap := by
            simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
            omega
          have good : goodDimindex width := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
          obtain ⟨bitmapWord, bitmapLookup, _⟩ := Bitmap.bitmapReads jump bounds pointer source target relation
          obtain ⟨base, baseRead, _reserve, _upper, _pointerRead, heap⟩ :=
            StackPointer.stateRelGetVarK jump bounds pointer source target relation
          have firstRead := StoreHeapReads.memLoadLemma .bitmapBase source target (.word bitmapWord) base
            ⟨by simp [storeList], by simpa only [StackSemRegisterTransfers.storeOfSyntax] using bitmapLookup,
              by simpa only [List.length_append, Nat.add_comm] using heap⟩
          have targetIndex : target.regs.lookup 1 = some (.word index) := by
            change getVar 1 target = _
            rw [← RelationLaws.stateRelGetVar jump bounds pointer 1 source target ⟨relation, by omega⟩]
            exact read1
          have targetAddress : target.regs.lookup 2 = some (.word address) := by
            change getVar 2 target = _
            rw [← RelationLaws.stateRelGetVar jump bounds pointer 2 source target ⟨relation, by omega⟩]
            exact read2
          have targetOffset : target.regs.lookup 3 = some (.word offset) := by
            change getVar 3 target = _
            rw [← RelationLaws.stateRelGetVar jump bounds pointer 3 source target ⟨relation, by omega⟩]
            exact read3
          let bitmapBase := bitmapWord <<< wordShiftAmount width
          let prepared := setVar bitmap (.word ((bitmapWord + index) <<< wordShiftAmount width)) target
          have addressEq : (bitmapWord + index) <<< wordShiftAmount width =
              bitmapBase + bytesInWord width * BitVec.ofNat width index.toNat := by
            simp only [bitmapBase, BitVec.shiftLeft_add_distrib, BitVec.ofNat_toNat, BitVec.setWidth_eq]
            rw [WordAddressArithmetic.lslWordShift index good, BitVec.mul_comm index]
          have preparedReads : getVar 2 prepared = some (.word address) ∧
              getVar 3 prepared = some (.word offset) ∧
              getVar bitmap prepared = some (.word
                (bitmapBase + bytesInWord width * BitVec.ofNat width index.toNat)) := by
            simp [prepared, getVar, setVar, HolFiniteMapExact.lookup_updateEq,
              FUPDATE_HOL, Ne.symm bTwo, Ne.symm bThree, targetAddress, targetOffset, addressEq]
          rw [copyHeapShape] at heap
          have copyHeap : SetSep.star
              (SetSep.star (Misc.wordList bitmapBase (source.bitmaps.map WordLocW.word))
                (copyFrame base bitmapBase source))
              (memoryHOL source.memory (fun key => source.mdomain key = true))
              (SetSep.fun2Set (target.memory, fun key => target.mdomain key = true)) := by
            simpa only [bitmapLookup, Option.map_some, wordLocWToGeneric, theSomeWord, bitmapBase] using heap
          have subset := memoryFun2SetSubset source.memory target.memory
            (fun key => source.mdomain key = true) (fun key => target.mdomain key = true)
            (SetSep.star (Misc.wordList bitmapBase (source.bitmaps.map WordLocW.word))
              (copyFrame base bitmapBase source))
            (by rw [SetSep.starComm]; exact copyHeap)
          obtain ⟨allowance, unchanged, value, nextBitmap, targetMemory, copyRun, finalHeap, copySteps⟩ :=
            SteppedFlapjack.StackRemoveSteps.copyLoopThmWithin temporary bitmap index.toNat 0 address offset finalAddress bitmapBase
              source.bitmaps (fun key => source.mdomain key = true)
              (fun key => target.mdomain key = true) source.memory finalMemory
              (copyFrame base bitmapBase source) prepared
              ⟨copySource, loopDistinct, rfl, good, subset,
                preparedReads.1, preparedReads.2.1, preparedReads.2.2, copyHeap⟩
          let copied : StackSemStateFiniteExact width C F :=
            {prepared with memory := targetMemory, regs := (((if unchanged then prepared.regs else prepared.regs.updateEq (temporary, .word value)).updateEq (2, .word finalAddress)).updateEq (1, .word 1)).updateEq (bitmap, .word nextBitmap)}
          change evaluate (copyLoop temporary bitmap,
            {prepared with clock := prepared.clock + allowance}) = (none, copied) at copyRun
          have memoryRel := stateRelCopiedMemory jump bounds pointer source target base
            finalMemory targetMemory relation baseRead
            (by simpa only [bitmapLookup, Option.map_some, wordLocWToGeneric, theSomeWord, bitmapBase] using finalHeap)
          have prefixRun := prepareBitmap bitmap pointer base bitmapWord index
            {target with clock := allowance + target.clock} baseRead targetIndex bOne firstRead good
          have prefixState : setVar bitmap (.word ((bitmapWord + index) <<< wordShiftAmount width))
              {target with clock := allowance + target.clock} =
              {prepared with clock := prepared.clock + allowance} := by
            simp only [prepared, setVar, Nat.add_comm]
          rw [prefixState] at prefixRun
          have copiedRead : getVar 1 copied = some (.word 1) := by
            simp [copied, getVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, Ne.symm bOne]
          let postTarget := setVar temporary (.word 1) (setVar bitmap (.word 1)
            (setVar 1 (.word 1) (setVar 2 (.word finalAddress) {target with memory := targetMemory})))
          rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
          subst result
          subst postSource
          refine ⟨allowance, postTarget, ?_, ?_, ?_⟩
          · rw [macroAfterPrepare jump bounds pointer temporary bitmap none
              {target with clock := allowance + target.clock}
              {prepared with clock := prepared.clock + allowance} prefixRun]
            change evaluate (.seq (copyLoop temporary bitmap)
              (listSeqHOL [moveInst temporary 1, moveInst bitmap 1]), _) = _
            rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate]
            simp only [copyRun]
            rw [finishMoves temporary bitmap copied tOne copiedRead]
            dsimp only [postTarget, copied, prepared, setVar]
            congr 2
            apply HolFiniteMapExact.ext_lookup
            intro query
            cases unchanged <;>
              by_cases qBitmap : query = bitmap <;>
              by_cases qOne : query = 1 <;>
              by_cases qTwo : query = 2 <;>
              by_cases qTemporary : query = temporary <;>
              simp [qBitmap, qOne, qTwo, qTemporary, tb,
                Ne.symm tOne, Ne.symm tTwo, Ne.symm tb, Ne.symm bOne, Ne.symm bTwo,
                HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
          · exact StateUpdates.stateRelSetVar jump bounds pointer temporary (.word 1) _ _
              ⟨StateUpdates.stateRelSetVar jump bounds pointer bitmap (.word 1) _ _
                ⟨StateUpdates.stateRelSetVar jump bounds pointer 1 (.word 1) _ _
                  ⟨StateUpdates.stateRelSetVar jump bounds pointer 2 (.word finalAddress) _ _
                    ⟨memoryRel, by omega⟩, by omega⟩, bound.2.2⟩, bound.2.1⟩
          · have prefixBound := steps_comp_storeConsts_of_prefix jump bounds pointer temporary bitmap none
              {target with clock := allowance + target.clock}
              {prepared with clock := prepared.clock + allowance} prefixRun
            have copyBound := copySteps.trans (copyLoopSteps_mono width (by omega : source.bitmaps.length - index.toNat ≤ B))
            unfold storeConstsSteps
            omega
      next => exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)

end SteppedFlapjack.StackRemoveSteps.CompCorrect
