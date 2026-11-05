import Flapjack.Compiler.Backend.StackRemove.Proofs.CopyEach
import SteppedFlapjack.StackRemoveSteps.Defs

/-! Fine-grained step bounds for the `copyEach` per-bitmap-word copy loop
(stepped-flapjack#2, phase C3).

The adapted `copyEachThmWithin` carries the same simulation result as
Flapjack's `copyEachThm` plus the fine-grained step bound
`15 * (pattern.toNat + 1) + 3`: each iteration costs fourteen steps (the loop,
the `If`, and the twelve-step body) and the sentinel costs three. The
duplication of the simulation proof is deliberate (see
`CONTINUE-STEP-PRESERVATION.md`); the source definitions stay in Flapjack. -/

namespace SteppedFlapjack.StackRemoveSteps

open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemMeasure
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.StackSemStoreConsts
open Flapjack.Compiler.Backend.StackRemove.CopyEachProof
open Flapjack.StackSemInst Flapjack.StackSemExpressions
open SteppedFlapjack.StackSteps
open Flapjack.StackSemIntegerInstructions

/-- Register reads are unchanged by a clock update. -/
theorem getVar_update_clock {width : Nat} [NeZero width] {C F : Type}
    (v : Nat) (s : StackSemStateFiniteExact width C F) (c : Nat) :
    StackSemStateOps.getVar v ({s with clock := c} : StackSemStateFiniteExact width C F) =
      StackSemStateOps.getVar v s := rfl

set_option maxHeartbeats 1000000 in
/-- Full bitmap-copy simulation with the fine-grained step bound. Retains the
same source copy success, distinct registers, domain equality/inclusion, good
word dimension, register reads and separated list/frame/memory assertion as
`copyEachThm`, and additionally bounds the run by
`15 * (pattern.toNat + 1) + 3` steps. -/
theorem copyEachThmWithin {width : Nat} [NeZero width] {C F : Type}
    (temporary bitmap index finalIndex : Nat)
    (pattern address offset finalAddress base : BitVec width)
    (bitmaps : List (BitVec width))
    (domain targetDomain : BitVec width → Prop) [DecidablePred domain]
    (memory finalMemory : BitVec width → WordLocW width)
    (rest : ((BitVec width × WordLocW width) → Prop) → Prop)
    (target : StackSemStateFiniteExact width C F)
    (hypothesis :
      copyWordsForPattern pattern index address offset bitmaps domain memory =
        some (finalIndex, finalAddress, finalMemory) ∧
      [1, 2, 3, temporary, bitmap].Nodup ∧
      targetDomain = (fun key => target.mdomain key = true) ∧
      goodDimindex width ∧
      StackSemStateOps.getVar 1 target = some (.word pattern) ∧
      (∀ key, domain key → targetDomain key) ∧
      StackSemStateOps.getVar 2 target = some (.word address) ∧
      StackSemStateOps.getVar 3 target = some (.word offset) ∧
      StackSemStateOps.getVar bitmap target =
        some (.word (base + bytesInWord width * BitVec.ofNat width index)) ∧
      SetSep.star
        (SetSep.star (Misc.wordList base (bitmaps.map WordLocW.word)) rest)
        (memoryHOL memory domain) (SetSep.fun2Set (target.memory, targetDomain))) :
    ∃ (allowance : Nat) (_value : BitVec width) (nextMemory : BitVec width → WordLocW width),
      StackSemEvaluate.evaluate
        (copyEach temporary bitmap, {target with clock := target.clock + allowance}) =
        (none, {target with memory := nextMemory, regs := (((if pattern = 1 then target.regs else target.regs.updateEq (temporary, .word _value)).updateEq (2, .word finalAddress)).updateEq (1, .word 1)).updateEq (bitmap, .word (base + bytesInWord width * BitVec.ofNat width finalIndex))}) ∧
      SetSep.star
        (SetSep.star (Misc.wordList base (bitmaps.map WordLocW.word)) rest)
        (memoryHOL finalMemory domain) (SetSep.fun2Set (nextMemory, targetDomain)) ∧
      steps (copyEach temporary bitmap, {target with clock := target.clock + allowance}) ≤
        15 * (pattern.toNat + 1) + 3 := by
  fun_induction copyWordsForPattern pattern index address offset bitmaps domain memory
    generalizing finalIndex finalAddress finalMemory target
  case case1 => cases hypothesis.1
  case case2 index address memory hzero =>
    rcases hypothesis with ⟨success, _distinct, _domain, _good,
      oneRead, _subset, addressRead, _offsetRead, bitmapRead, heap⟩
    cases success
    refine ⟨0, 0, target.memory, ?_, heap, ?_⟩
    · simp only [Nat.add_zero, ite_true]
      rw [sentinelPostState bitmap index base address target oneRead addressRead bitmapRead]
      exact copyEachSentinel temporary bitmap target oneRead
    · have h := steps_copyEach_sentinel temporary bitmap target oneRead
      have hnat : BitVec.toNat (1 : BitVec width) = 1 := by
        have hpos : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
        simp [BitVec.toNat_ofNat, hpos]
      have hstate : ({target with clock := target.clock + 0} : StackSemStateFiniteExact width C F) = target := by
        simp
      rw [hstate]
      simp only [hnat]
      omega
  case case4 => cases hypothesis.1
  case case3 pattern index address memory hzero hone guard value nextMemory ih =>
    rcases hypothesis with ⟨success, distinct, domainEq, good,
      patternRead, subset, addressRead, offsetRead, bitmapRead, heap⟩
    have canonicalHeap := heap
    rw [domainEq] at canonicalHeap
    have canonicalSubset := subset
    rw [domainEq] at canonicalSubset
    let post := copyStepState temporary bitmap index pattern address offset base value target
    have step := copyStepFromHeap temporary bitmap index pattern address offset base
      bitmaps domain memory rest target distinct good patternRead addressRead offsetRead
      bitmapRead guard canonicalSubset canonicalHeap
    obtain ⟨nextPatternRead, nextAddressRead, nextOffsetRead, nextBitmapRead, nextClock⟩ :=
      copyStepReads temporary bitmap index pattern address offset base value target distinct offsetRead
    have memoryEq : nextMemory =
        (fun key => if key = address then
          .word (if pattern.getLsbD 0 then value + offset else value) else memory key) := by
      funext key
      by_cases same : key = address <;>
        by_cases bit : pattern.getLsbD 0 = true <;> simp [nextMemory, same, bit]
    have nextHeap : SetSep.star
        (SetSep.star (Misc.wordList base (bitmaps.map WordLocW.word)) rest)
        (memoryHOL nextMemory domain) (SetSep.fun2Set (post.memory, targetDomain)) := by
      simpa only [memoryEq, post, value, copyStepState, domainEq] using step.2
    obtain ⟨allowance, finalValue, resultMemory, recursiveRun, finalHeap, recursiveSteps⟩ :=
      ih finalIndex finalAddress finalMemory post
        ⟨success, distinct, domainEq, good, nextPatternRead, subset,
          by simpa only [bytesInWord] using nextAddressRead,
          nextOffsetRead, nextBitmapRead, nextHeap⟩
    let boosted : StackSemStateFiniteExact width C F :=
      {target with clock := target.clock + (allowance + 1)}
    have getVarBoosted : StackSemStateOps.getVar 1 boosted = StackSemStateOps.getVar 1 target := rfl
    have patternReadBoosted :
        StackSemStateOps.getVar 1
          ({target with clock := target.clock + (allowance + 1)} : StackSemStateFiniteExact width C F) =
          some (.word pattern) := by
      convert patternRead using 2
    let boostedPost : StackSemStateFiniteExact width C F :=
      {post with clock := target.clock + (allowance + 1)}
    have boostedStep := copyStepFromHeap temporary bitmap index pattern address offset base
      bitmaps domain memory rest boosted distinct good patternReadBoosted addressRead offsetRead
      bitmapRead guard canonicalSubset canonicalHeap
    have boostedRun : StackSemEvaluate.evaluate
        (Compiler.Backend.StackLang.listSeqHOL [loadInst temporary bitmap,
          Compiler.Backend.StackLang.addBytesInWordInst bitmap,
          .ite .test 1 (.imm 1) .skip (Compiler.Backend.StackLang.addInst temporary 3),
          rightShiftInst 1 1, storeInst temporary 2,
          Compiler.Backend.StackLang.addBytesInWordInst 2], boosted) = (none, boostedPost) := by
      simpa only [boosted, boostedPost, post, copyStepState, value] using boostedStep.1
    have reentry := copyEachReenter temporary bitmap pattern boosted boostedPost
      patternReadBoosted hone (by dsimp [boosted]; omega) rfl boostedRun
    have reentryState : StackSemStateOps.decClock boostedPost =
        {post with clock := post.clock + allowance} := by
      simp [StackSemStateOps.decClock, boostedPost, post, copyStepState]
    refine ⟨allowance + 1,
      (if pattern >>> (1 : Nat) = 1 then
        (if pattern.getLsbD 0 then value + offset else value) else finalValue),
      resultMemory, ?_, finalHeap, ?_⟩
    · change StackSemEvaluate.evaluate (copyEach temporary bitmap, boosted) = _
      rw [reentry, reentryState, recursiveRun]
      simp only [hone, if_false, post, copyStepState]
      congr 2
      apply HolFiniteMapExact.ext_lookup
      intro query
      simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
      have tOne : temporary ≠ 1 := by omega
      have tTwo : temporary ≠ 2 := by omega
      have tb : temporary ≠ bitmap := by omega
      by_cases nextSentinel : pattern >>> (1 : Nat) = BitVec.ofNat width 1 <;>
        by_cases qBitmap : query = bitmap <;>
        by_cases qOne : query = 1 <;>
        by_cases qTwo : query = 2 <;>
        by_cases qTemporary : query = temporary <;>
        simp [nextSentinel, qBitmap, qOne, qTwo, qTemporary, tOne, tTwo, tb,
          HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
    · change pattern ≠ BitVec.ofNat width 1 at hone
      have hcond : (pattern == (1 : BitVec width)) = false := by simp [hone]
      have evalIte : StackSemEvaluate.evaluate
          ((.ite .notEqual 1 (.imm 1)
            (Compiler.Backend.StackLang.listSeqHOL [loadInst temporary bitmap,
              Compiler.Backend.StackLang.addBytesInWordInst bitmap,
              .ite .test 1 (.imm 1) .skip (Compiler.Backend.StackLang.addInst temporary 3),
              rightShiftInst 1 1, storeInst temporary 2,
              Compiler.Backend.StackLang.addBytesInWordInst 2]) (.break 0) : HolProg width),
            boosted) = (none, boostedPost) := by
        rw [StackSemEvaluate.evaluate_ite, getVarBoosted]
        simp only [StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, patternRead,
          wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL]
        simp only [hcond, Bool.not_false]
        rw [boostedRun]
      have hdef : (copyEach temporary bitmap : HolProg width)
          = (.loop (.ite .notEqual 1 (.imm 1)
              (Compiler.Backend.StackLang.listSeqHOL [loadInst temporary bitmap,
                Compiler.Backend.StackLang.addBytesInWordInst bitmap,
                .ite .test 1 (.imm 1) .skip (Compiler.Backend.StackLang.addInst temporary 3),
                rightShiftInst 1 1, storeInst temporary 2,
                Compiler.Backend.StackLang.addBytesInWordInst 2])
              (.break 0) : HolProg width)) := rfl
      have hsteps : steps (copyEach temporary bitmap, boosted) =
          1 + (1 + steps (Compiler.Backend.StackLang.listSeqHOL [loadInst temporary bitmap,
            Compiler.Backend.StackLang.addBytesInWordInst bitmap,
            .ite .test 1 (.imm 1) .skip (Compiler.Backend.StackLang.addInst temporary 3),
            rightShiftInst 1 1, storeInst temporary 2,
            Compiler.Backend.StackLang.addBytesInWordInst 2], boosted)) +
          steps (copyEach temporary bitmap, StackSemStateOps.decClock boostedPost) := by
        rw [hdef, steps_loop, steps_ite, getVarBoosted]
        simp only [StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, patternRead,
          wordSemWordCmp, Compiler.Encoders.Asm.wordCmpHOL]
        simp only [hcond, Bool.not_false]
        rw [evalIte]
        simp only [StackSemControl.fixClock]
        have clockEq : boostedPost.clock = boosted.clock := rfl
        simp only [clockEq, Nat.min_self, StackSemControl.contLoop, true_and]
        rw [if_pos (by dsimp [boosted]; omega : boosted.clock ≠ 0)]
      have hinner := steps_innerBody_le temporary bitmap boosted
      have hpat : 2 ≤ pattern.toNat := by
        have h0 : pattern.toNat ≠ 0 := by
          intro hz
          apply hzero
          apply BitVec.eq_of_toNat_eq
          simpa using hz
        have h1 : pattern.toNat ≠ 1 := by
          intro h1'
          apply hone
          apply BitVec.eq_of_toNat_eq
          rw [h1']
          have hpos : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
          simp [BitVec.toNat_ofNat, hpos]
        omega
      have hshift : (pattern >>> (1 : Nat)).toNat = pattern.toNat / 2 :=
        BitVec.toNat_ushiftRight pattern 1
      have hdiv : pattern.toNat / 2 ≤ pattern.toNat - 1 :=
        Nat.le_pred_of_lt (Nat.div_lt_self (by omega) (by decide))
      rw [hsteps, reentryState]
      omega
