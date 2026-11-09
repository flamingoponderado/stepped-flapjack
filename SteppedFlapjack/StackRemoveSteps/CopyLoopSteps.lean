import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Flapjack.Compiler.Backend.StackRemove.Proofs.CopyLoop
import Flapjack.Compiler.Backend.StackProps.EvaluateAddClock
import SteppedFlapjack.StackRemoveSteps.CopyEachSteps
import SteppedFlapjack.StackRemoveSteps.Defs

/-! Fine-grained step bounds for the `copyLoop` bitmap-copy loop
(stepped-flapjack#2, phase C3).

`copyLoop` is a two-instruction prefix, an outer `while` over the bitmap words
that runs one `copyEach` per negative word, and a final `copyEach`. The bound
`copyLoopSteps width (bitmaps.length - index)` charges five nodes for the
prefix, six nodes plus one `copyEach` bound per outer iteration, and the exit
check plus the trailing `copyEach` in the constant. -/

namespace SteppedFlapjack.StackRemoveSteps

open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemMeasure
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Encoders.Asm
open Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.StackSemStoreConsts
open Flapjack.Compiler.Backend.StackRemove.CopyEachProof
open Flapjack.Compiler.Backend.StackRemove.CopyLoopProof
open Flapjack.StackSemInst Flapjack.StackSemExpressions
open SteppedFlapjack.StackSteps
open Flapjack.StackSemIntegerInstructions

variable {width : Nat} [NeZero width] {C F : Type}

/-- The two-instruction bitmap prefix takes at most three nodes. -/
theorem steps_prefix_le (bitmap : Nat) (s : StackSemStateFiniteExact width C F) :
    steps ((.seq (loadInst 1 bitmap) (addBytesInWordInst bitmap) : HolProg width), s) ≤ 3 := by
  have h1 : steps (loadInst 1 bitmap, s) ≤ 1 := by
    simp only [loadInst]
    exact le_of_eq (steps_inst _ s)
  have h2 : ∀ s' : StackSemStateFiniteExact width C F,
      steps (addBytesInWordInst bitmap, s') ≤ 1 := by
    intro s'
    simp only [addBytesInWordInst]
    exact le_of_eq (steps_inst _ s')
  rw [steps_seq]
  split
  · rename_i s1 _
    have := h2 s1
    omega
  · omega

/-- A successful prefix run splits into its two instruction runs. -/
theorem steps_prefix_runs (bitmap : Nat) (s loaded : StackSemStateFiniteExact width C F)
    (h : evaluate (listSeqHOL [loadInst 1 bitmap, addBytesInWordInst bitmap], s) = (none, loaded)) :
    ∃ s1, evaluate (loadInst 1 bitmap, s) = (none, s1) ∧
      evaluate (addBytesInWordInst bitmap, s1) = (none, loaded) := by
  have hseq : evaluate ((.seq (loadInst 1 bitmap) (addBytesInWordInst bitmap) : HolProg width), s) =
      (none, loaded) := h
  rcases ha : evaluate (loadInst 1 bitmap, s) with ⟨ra, sa⟩
  rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, ha] at hseq
  cases ra with
  | none => exact ⟨sa, rfl, by simpa using hseq⟩
  | some r => simp at hseq

/-- A successful `seq` run splits into its two component runs. -/
theorem evaluate_seq_none (a b : HolProg width) (s out : StackSemStateFiniteExact width C F)
    (h : evaluate ((.seq a b : HolProg width), s) = (none, out)) :
    ∃ s1, evaluate (a, s) = (none, s1) ∧ evaluate (b, s1) = (none, out) := by
  rcases ha : evaluate (a, s) with ⟨ra, sa⟩
  rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, ha] at h
  cases ra with
  | none => exact ⟨sa, rfl, by simpa using h⟩
  | some r => simp at h

/-- The full `copyLoop` node count, split at the outer loop's exit state. -/
theorem steps_copyLoop_le (temporary bitmap : Nat)
    (s s1 loaded final : StackSemStateFiniteExact width C F)
    (p1Run : evaluate (loadInst 1 bitmap, s) = (none, s1))
    (p2Run : evaluate (addBytesInWordInst bitmap, s1) = (none, loaded))
    (loopRun : evaluate (whileProg .less 1 (.imm 0)
      (listSeqHOL [copyEach temporary bitmap, loadInst 1 bitmap, addBytesInWordInst bitmap]),
      loaded) = (none, final)) :
    steps (copyLoop temporary bitmap, s) =
      5 + steps (whileProg .less 1 (.imm 0)
        (listSeqHOL [copyEach temporary bitmap, loadInst 1 bitmap, addBytesInWordInst bitmap]),
        loaded) + steps (copyEach temporary bitmap, final) := by
  have hcopy : (copyLoop temporary bitmap : HolProg width) =
      .seq (loadInst 1 bitmap) (.seq (addBytesInWordInst bitmap)
        (.seq (whileProg .less 1 (.imm 0)
          (listSeqHOL [copyEach temporary bitmap, loadInst 1 bitmap, addBytesInWordInst bitmap]))
          (copyEach temporary bitmap))) := rfl
  rw [hcopy]
  rw [steps_seq_run _ _ s s1 p1Run]
  rw [steps_seq_run _ _ s1 loaded p2Run]
  rw [steps_seq_run _ _ loaded final loopRun]
  have h1 : steps (loadInst 1 bitmap, s) = 1 := by
    simp only [loadInst, steps_inst]
  have h2 : steps (addBytesInWordInst bitmap, s1) = 1 := by
    simp only [addBytesInWordInst, steps_inst]
  omega

/-- One continuing outer iteration: six nodes plus the `copyEach` body. -/
theorem steps_while_step (temporary bitmap : Nat) (pattern : BitVec width)
    (loaded next : StackSemStateFiniteExact width C F)
    (read : StackSemStateOps.getVar 1 loaded = some (.word pattern))
    (sign : pattern.msb = true)
    (bodyRun : evaluate (listSeqHOL [copyEach temporary bitmap, loadInst 1 bitmap,
      addBytesInWordInst bitmap], loaded) = (none, next))
    (clock : next.clock ≠ 0) :
    steps (whileProg .less 1 (.imm 0)
      (listSeqHOL [copyEach temporary bitmap, loadInst 1 bitmap, addBytesInWordInst bitmap]),
      loaded) ≤
      6 + steps (copyEach temporary bitmap, loaded) +
        steps (whileProg .less 1 (.imm 0)
          (listSeqHOL [copyEach temporary bitmap, loadInst 1 bitmap, addBytesInWordInst bitmap]),
          StackSemStateOps.decClock next) := by
  have comparison : wordCmpHOL .less pattern (0 : BitVec width) = pattern.msb :=
    signedLessZero pattern
  have hdef : (whileProg .less 1 (.imm 0)
      (listSeqHOL [copyEach temporary bitmap, loadInst 1 bitmap, addBytesInWordInst bitmap]) :
      HolProg width) =
      .loop (.ite .less 1 (.imm 0)
        (listSeqHOL [copyEach temporary bitmap, loadInst 1 bitmap, addBytesInWordInst bitmap])
        (.break 0)) := rfl
  have iteRun : evaluate ((.ite .less 1 (.imm 0)
      (listSeqHOL [copyEach temporary bitmap, loadInst 1 bitmap, addBytesInWordInst bitmap])
      (.break 0) : HolProg width), loaded) = (none, next) := by
    rw [evaluate_ite]
    simp only [StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, read, wordSemWordCmp]
    rw [comparison, sign]
    exact bodyRun
  rw [hdef]
  rw [steps_loop_run _ _ next none iteRun (by simp [StackSemControl.contLoop]) clock]
  have hite : steps ((.ite .less 1 (.imm 0)
      (listSeqHOL [copyEach temporary bitmap, loadInst 1 bitmap, addBytesInWordInst bitmap])
      (.break 0) : HolProg width), loaded) =
      1 + steps (listSeqHOL [copyEach temporary bitmap, loadInst 1 bitmap,
        addBytesInWordInst bitmap], loaded) :=
    steps_ite_true .less 1 (.imm 0) _ _ loaded (.word pattern)
      (.word (BitVec.ofNat width 0)) read
      (by simp [StackSemStateOps.getVarImm, HolRegImm.toWordRegImm])
      (by
        simp only [wordSemWordCmp]
        show some (wordCmpHOL .less pattern (0 : BitVec width)) = some true
        rw [comparison, sign])
  rw [hite]
  have hbody : steps (listSeqHOL [copyEach temporary bitmap, loadInst 1 bitmap,
      addBytesInWordInst bitmap], loaded) ≤ 1 + steps (copyEach temporary bitmap, loaded) + 3 := by
    simp only [listSeqHOL]
    rw [steps_seq]
    split
    · rename_i s' _
      have := steps_prefix_le bitmap s'
      omega
    · omega
  omega

/-- The outer loop's exit check takes three nodes and changes nothing. -/
theorem steps_while_exit (temporary bitmap : Nat) (pattern : BitVec width)
    (loaded : StackSemStateFiniteExact width C F)
    (read : StackSemStateOps.getVar 1 loaded = some (.word pattern))
    (sign : pattern.msb = false) :
    steps (whileProg .less 1 (.imm 0)
      (listSeqHOL [copyEach temporary bitmap, loadInst 1 bitmap, addBytesInWordInst bitmap]),
      loaded) ≤ 3 := by
  have comparison : wordCmpHOL .less pattern (0 : BitVec width) = pattern.msb :=
    signedLessZero pattern
  have hdef : (whileProg .less 1 (.imm 0)
      (listSeqHOL [copyEach temporary bitmap, loadInst 1 bitmap, addBytesInWordInst bitmap]) :
      HolProg width) =
      .loop (.ite .less 1 (.imm 0)
        (listSeqHOL [copyEach temporary bitmap, loadInst 1 bitmap, addBytesInWordInst bitmap])
        (.break 0)) := rfl
  have iteRun : evaluate ((.ite .less 1 (.imm 0)
      (listSeqHOL [copyEach temporary bitmap, loadInst 1 bitmap, addBytesInWordInst bitmap])
      (.break 0) : HolProg width), loaded) = (some (.break 0), loaded) := by
    rw [evaluate_ite]
    simp only [StackSemStateOps.getVarImm, HolRegImm.toWordRegImm, read, wordSemWordCmp]
    rw [comparison, sign]
    rw [evaluate_break]
  rw [hdef]
  rw [steps_loop_exit _ _ loaded (some (.break 0)) iteRun
    (by simp [StackSemControl.contLoop])]
  have hite : steps ((.ite .less 1 (.imm 0)
      (listSeqHOL [copyEach temporary bitmap, loadInst 1 bitmap, addBytesInWordInst bitmap])
      (.break 0) : HolProg width), loaded) =
      1 + steps ((.break 0 : HolProg width), loaded) :=
    steps_ite_false .less 1 (.imm 0) _ _ loaded (.word pattern)
      (.word (BitVec.ofNat width 0)) read
      (by simp [StackSemStateOps.getVarImm, HolRegImm.toWordRegImm])
      (by
        simp only [wordSemWordCmp]
        show some (wordCmpHOL .less pattern (0 : BitVec width)) = some false
        rw [comparison, sign])
  rw [hite]
  have hbreak : steps ((.break 0 : HolProg width), loaded) = 1 := steps_break 0 loaded
  rw [hbreak]

/-! ### Arithmetic of the bound -/

theorem copyLoopSteps_mono (width : Nat) {B1 B2 : Nat} (h : B1 ≤ B2) :
    copyLoopSteps width B1 ≤ copyLoopSteps width B2 := by
  have h1 : 15 * B1 * 2 ^ width ≤ 15 * B2 * 2 ^ width :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 15 h)
  have h2 : 9 * B1 ≤ 9 * B2 := Nat.mul_le_mul_left 9 h
  unfold copyLoopSteps
  omega

theorem copyLoopSteps_succ (width B : Nat) :
    copyLoopSteps width B + (15 * 2 ^ width + 9) = copyLoopSteps width (B + 1) := by
  unfold copyLoopSteps
  ring

theorem copyLoopSteps_pos (width B : Nat) : 15 * 2 ^ width + 11 ≤ copyLoopSteps width B := by
  unfold copyLoopSteps
  have : 0 ≤ B * (15 * 2 ^ width + 9) := Nat.zero_le _
  nlinarith [Nat.zero_le (B * (15 * 2 ^ width + 9))]

/-! ### The `copyLoop` step bound -/

set_option maxHeartbeats 1000000 in
/-- Full bitmap-list copy simulation with the fine-grained step bound. Retains
`copyLoopThm`'s source success, distinct registers, domain equality/inclusion,
good word dimension, register reads and separated list/frame/memory assertion,
and bounds the run by `copyLoopSteps width (bitmaps.length - index)` steps. -/
theorem copyLoopThmWithin {width : Nat} [NeZero width] {C F : Type}
    (temporary bitmap index _unusedIndex : Nat)
    (address offset finalAddress base : BitVec width)
    (bitmaps : List (BitVec width))
    (domain targetDomain : BitVec width → Prop) [DecidablePred domain]
    (memory finalMemory : BitVec width → WordLocW width)
    (rest : ((BitVec width × WordLocW width) → Prop) → Prop)
    (target : StackSemStateFiniteExact width C F)
    (hypothesis :
      StackSemStoreConsts.copyWordsExact index address offset bitmaps domain memory =
        some (finalAddress, finalMemory) ∧
      [1, 2, 3, temporary, bitmap].Nodup ∧
      targetDomain = (fun key => target.mdomain key = true) ∧
      goodDimindex width ∧
      (∀ key, domain key → targetDomain key) ∧
      getVar 2 target = some (.word address) ∧
      getVar 3 target = some (.word offset) ∧
      getVar bitmap target =
        some (.word (base + bytesInWord width * BitVec.ofNat width index)) ∧
      SetSep.star
        (SetSep.star (Misc.wordList base (bitmaps.map WordLocW.word)) rest)
        (memoryHOL memory domain) (SetSep.fun2Set (target.memory, targetDomain))) :
    ∃ (allowance : Nat) (unchanged : Bool) (value nextBitmap : BitVec width)
      (nextMemory : BitVec width → WordLocW width),
      evaluate (copyLoop temporary bitmap, {target with clock := target.clock + allowance}) =
        (none, {target with memory := nextMemory, regs := (((if unchanged then target.regs else target.regs.updateEq (temporary, .word value)).updateEq (2, .word finalAddress)).updateEq (1, .word 1)).updateEq (bitmap, .word nextBitmap)}) ∧
      SetSep.star
        (SetSep.star (Misc.wordList base (bitmaps.map WordLocW.word)) rest)
        (memoryHOL finalMemory domain) (SetSep.fun2Set (nextMemory, targetDomain)) ∧
      steps (copyLoop temporary bitmap, {target with clock := target.clock + allowance}) ≤
        copyLoopSteps width (bitmaps.length - index) := by
  fun_induction StackSemStoreConsts.copyWordsExact index address offset bitmaps domain memory
    generalizing finalAddress finalMemory target
  case case1 => cases hypothesis.1
  case case2 => cases hypothesis.1
  case case3 i a m bound pattern nextIndex nextAddress nextMemory patternRun sign ih =>
    rcases hypothesis with ⟨success, distinct, domainEq, good, subset,
      addressRead, offsetRead, bitmapRead, heap⟩
    have valid : i < bitmaps.length := by omega
    have patternEq : pattern = bitmaps[i] := by simp [pattern, getElem!_pos, valid]
    let loaded := loadBitmapState bitmap i base pattern target
    have reads := loadBitmapReads temporary bitmap i base pattern a offset target
      distinct addressRead offsetRead
    change getVar 1 loaded = _ ∧ getVar 2 loaded = _ ∧ getVar 3 loaded = _ ∧
      getVar bitmap loaded = _ ∧ loaded.clock = target.clock at reads
    obtain ⟨allowance, value, resultMemory, copyRun, copiedHeap, copySteps, copyStepsC⟩ :=
      copyEachThmWithin temporary bitmap (i + 1) nextIndex
        pattern a offset nextAddress base bitmaps domain targetDomain m nextMemory rest loaded
        ⟨patternRun, distinct, domainEq, good, reads.1, subset,
          reads.2.1, reads.2.2.1, reads.2.2.2.1, heap⟩
    let copied : StackSemStateFiniteExact width C F :=
      {loaded with memory := resultMemory, regs := (((if pattern = 1 then loaded.regs else loaded.regs.updateEq (temporary, .word value)).updateEq (2, .word nextAddress)).updateEq (1, .word 1)).updateEq (bitmap, .word (base + bytesInWord width * BitVec.ofNat width nextIndex))}
    change evaluate (copyEach temporary bitmap,
      {loaded with clock := loaded.clock + allowance}) = (none, copied) at copyRun
    have bTwo : bitmap ≠ 2 := by
      simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
      omega
    have bThree : bitmap ≠ 3 := by
      simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
      omega
    have tThree : temporary ≠ 3 := by
      simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
      omega
    have copiedReads : getVar 2 copied = some (.word nextAddress) ∧
        getVar 3 copied = some (.word offset) ∧
        getVar bitmap copied = some (.word
          (base + bytesInWord width * BitVec.ofNat width nextIndex)) := by
      change target.regs.lookup 3 = _ at offsetRead
      by_cases sentinel : pattern = BitVec.ofNat width 1 <;>
        simp [copied, loaded, loadBitmapState, getVar, sentinel,
          HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          Ne.symm bTwo, Ne.symm bThree, Ne.symm tThree, offsetRead]
    obtain ⟨recursiveAllowance, unchanged, recursiveValue, nextBitmap,
      finalTargetMemory, recursiveRun, finalHeap, recursiveSteps⟩ :=
      ih finalAddress finalMemory copied
        ⟨success, distinct, domainEq, good, subset,
          copiedReads.1, copiedReads.2.1, copiedReads.2.2, copiedHeap⟩
    have nextValid : nextIndex < bitmaps.length := by
      by_contra outside
      have outside : bitmaps.length ≤ nextIndex := by omega
      rw [StackSemStoreConsts.copyWordsExact, dif_pos outside] at success
      cases success
    let boosted := {target with clock := target.clock + (allowance + recursiveAllowance + 1)}
    let boostedLoaded := {loaded with clock := loaded.clock + (allowance + recursiveAllowance + 1)}
    let boostedCopied := {copied with clock := copied.clock + (recursiveAllowance + 1)}
    let next := loadBitmapState bitmap nextIndex base bitmaps[nextIndex] boostedCopied
    have firstRun := loadBitmapFromHeap temporary bitmap i base bitmaps domain m rest
      boosted distinct valid bitmapRead (by simpa [domainEq] using heap)
    have firstState : loadBitmapState bitmap i base bitmaps[i] boosted = boostedLoaded := by
      simp only [← patternEq, boosted, boostedLoaded, loaded, loadBitmapState]
    rw [firstState] at firstRun
    have boostedCopyRun := Flapjack.Compiler.Backend.StackProps.evaluateAddClock
      (recursiveAllowance + 1) (copyEach temporary bitmap)
      {loaded with clock := loaded.clock + allowance} none copied ⟨copyRun, by simp⟩
    have boostedCopy : evaluate (copyEach temporary bitmap, boostedLoaded) =
        (none, boostedCopied) := by
      simpa only [boostedLoaded, boostedCopied, Nat.add_assoc] using boostedCopyRun
    have reloadRun : evaluate
        (listSeqHOL [loadInst 1 bitmap, addBytesInWordInst bitmap], boostedCopied) =
        (none, next) :=
      loadBitmapFromHeap temporary bitmap nextIndex base bitmaps domain nextMemory rest
        boostedCopied distinct nextValid copiedReads.2.2
        (by simpa [domainEq, boostedCopied, copied, loaded, loadBitmapState] using copiedHeap)
    have reloadDecRun : evaluate
        (listSeqHOL [loadInst 1 bitmap, addBytesInWordInst bitmap], decClock boostedCopied) =
        (none, decClock next) := by
      have run := loadBitmapFromHeap temporary bitmap nextIndex base bitmaps domain nextMemory rest
        (decClock boostedCopied) distinct nextValid copiedReads.2.2
        (by simpa [domainEq, decClock, boostedCopied, copied, loaded, loadBitmapState] using copiedHeap)
      simpa only [next, loadBitmapState, decClock] using run
    have nonzero : next.clock ≠ 0 := by
      dsimp [next, loadBitmapState, boostedCopied]
      omega
    have loopRun := copyLoopNegative temporary bitmap pattern boosted boostedLoaded
      boostedCopied next firstRun reads.1 sign boostedCopy reloadRun reloadDecRun nonzero
    have reentryState : decClock boostedCopied =
        {copied with clock := copied.clock + recursiveAllowance} := by
      simp [decClock, boostedCopied]
    refine ⟨allowance + recursiveAllowance + 1,
      decide (pattern = 1) && unchanged, (if unchanged then value else recursiveValue),
      nextBitmap, finalTargetMemory, ?_, finalHeap, ?_⟩
    · change evaluate (copyLoop temporary bitmap, boosted) = _
      rw [loopRun, reentryState, recursiveRun]
      dsimp only [copied, loaded, loadBitmapState]
      congr 2
      apply HolFiniteMapExact.ext_lookup
      intro query
      simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
      have tOne : temporary ≠ 1 := by omega
      have tTwo : temporary ≠ 2 := by omega
      have tb : temporary ≠ bitmap := by omega
      cases unchanged <;>
        by_cases sentinel : pattern = BitVec.ofNat width 1 <;>
        by_cases qBitmap : query = bitmap <;>
        by_cases qOne : query = 1 <;>
        by_cases qTwo : query = 2 <;>
        by_cases qTemporary : query = temporary <;>
        simp [sentinel, qBitmap, qOne, qTwo, qTemporary, tOne, tTwo, tb,
          HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
    · -- step bound
      have bodyRun : evaluate
          (listSeqHOL [copyEach temporary bitmap, loadInst 1 bitmap,
            addBytesInWordInst bitmap], boostedLoaded) = (none, next) := by
        change evaluate ((.seq (copyEach temporary bitmap)
          (listSeqHOL [loadInst 1 bitmap, addBytesInWordInst bitmap]) : HolProg width),
          boostedLoaded) = _
        rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, boostedCopy]
        exact reloadRun
      -- the recursive `copyLoop` tail, to expose the outer loop's exit state
      rw [← reentryState] at recursiveRun
      obtain ⟨s0, hp1, hp2⟩ := evaluate_seq_none _ _ _ _ reloadDecRun
      simp only [listSeqHOL] at hp2
      obtain ⟨s1, hp1', hrest⟩ := evaluate_seq_none _ _ _ _ recursiveRun
      rw [hp1] at hp1'
      cases hp1'
      obtain ⟨s2, hp2', htail⟩ := evaluate_seq_none _ _ _ _ hrest
      rw [hp2] at hp2'
      cases hp2'
      obtain ⟨final, whileRunDec, copyRunFinal⟩ := evaluate_seq_none _ _ _ _ htail
      have whileEq := copyWhileReenter temporary bitmap pattern boostedLoaded next
        reads.1 sign nonzero bodyRun
      have whileRunBoosted : evaluate (whileProg .less 1 (.imm 0)
          (listSeqHOL [copyEach temporary bitmap, loadInst 1 bitmap, addBytesInWordInst bitmap]),
          boostedLoaded) = (none, final) := by
        rw [whileEq]
        exact whileRunDec
      obtain ⟨bs1, bp1, bp2⟩ := steps_prefix_runs bitmap boosted boostedLoaded firstRun
      obtain ⟨ds1, dp1, dp2⟩ := steps_prefix_runs bitmap (decClock boostedCopied) (decClock next) reloadDecRun
      have lhsLe := steps_copyLoop_le temporary bitmap boosted bs1 boostedLoaded final bp1 bp2 whileRunBoosted
      have rhsLe := steps_copyLoop_le temporary bitmap (decClock boostedCopied) ds1 (decClock next) final dp1 dp2 whileRunDec
      have whileStep := steps_while_step temporary bitmap pattern boostedLoaded next
        reads.1 sign bodyRun nonzero
      have copyLe : steps (copyEach temporary bitmap, boostedLoaded) ≤ 15 * (pattern.toNat + 1) + 3 :=
        copyStepsC boostedLoaded.clock (by dsimp [boostedLoaded, loaded, loadBitmapState]; omega)
      have hpatBound : pattern.toNat + 1 ≤ 2 ^ width := by
        have := pattern.isLt
        omega
      have hrec : steps (copyLoop temporary bitmap, decClock boostedCopied) ≤
          copyLoopSteps width (bitmaps.length - nextIndex) := by
        rw [reentryState]
        exact recursiveSteps
      have hmain : steps (copyLoop temporary bitmap, boosted) ≤
          6 + steps (copyEach temporary bitmap, boostedLoaded) +
            steps (copyLoop temporary bitmap, decClock boostedCopied) := by
        omega
      have hstep : steps (copyEach temporary bitmap, boostedLoaded) ≤ 15 * 2 ^ width + 3 := by
        omega
      have indexLe : i + 1 ≤ nextIndex :=
        StackSemStoreConsts.copyWordsForPattern_index_le pattern (i + 1) a offset bitmaps
          domain m nextIndex (nextAddress, nextMemory) patternRun
      have hnext : bitmaps.length - nextIndex + 1 ≤ bitmaps.length - i := by omega
      calc steps (copyLoop temporary bitmap, boosted)
          ≤ 6 + steps (copyEach temporary bitmap, boostedLoaded) +
              steps (copyLoop temporary bitmap, decClock boostedCopied) := hmain
        _ ≤ 6 + (15 * 2 ^ width + 3) + copyLoopSteps width (bitmaps.length - nextIndex) := by
            omega
        _ = copyLoopSteps width (bitmaps.length - nextIndex) + (15 * 2 ^ width + 9) := by ring
        _ = copyLoopSteps width (bitmaps.length - nextIndex + 1) :=
            copyLoopSteps_succ width (bitmaps.length - nextIndex)
        _ ≤ copyLoopSteps width (bitmaps.length - i) := copyLoopSteps_mono width hnext
  case case4 i a m bound pattern nextIndex nextAddress nextMemory patternRun sign =>
    rcases hypothesis with ⟨success, distinct, domainEq, good, subset,
      addressRead, offsetRead, bitmapRead, heap⟩
    cases Option.some.inj success
    have valid : i < bitmaps.length := by omega
    have patternEq : pattern = bitmaps[i] := by
      simp [pattern, getElem!_pos, valid]
    let loaded := loadBitmapState bitmap i base pattern target
    have reads := loadBitmapReads temporary bitmap i base pattern a offset target
      distinct addressRead offsetRead
    change getVar 1 loaded = _ ∧ getVar 2 loaded = _ ∧ getVar 3 loaded = _ ∧
      getVar bitmap loaded = _ ∧ loaded.clock = target.clock at reads
    have loadedHeap : SetSep.star
        (SetSep.star (Misc.wordList base (bitmaps.map WordLocW.word)) rest)
        (memoryHOL m domain) (SetSep.fun2Set (loaded.memory, targetDomain)) := heap
    obtain ⟨allowance, value, resultMemory, copyRun, finalHeap, copySteps, _copyStepsC⟩ :=
      copyEachThmWithin temporary bitmap (i + 1) nextIndex
        pattern a offset nextAddress base bitmaps domain targetDomain m nextMemory rest loaded
        ⟨patternRun, distinct, domainEq, good, reads.1, subset,
          reads.2.1, reads.2.2.1, reads.2.2.2.1, loadedHeap⟩
    have prefixRun := loadBitmapFromHeap temporary bitmap i base bitmaps domain m rest
      {target with clock := target.clock + allowance} distinct valid bitmapRead
      (by simpa [domainEq] using heap)
    have prefixLoaded : loadBitmapState bitmap i base bitmaps[i]
        {target with clock := target.clock + allowance} =
        {loaded with clock := loaded.clock + allowance} := by
      simp only [← patternEq, loaded, loadBitmapState]
    rw [prefixLoaded] at prefixRun
    have nonnegative : pattern.msb = false := by simpa using sign
    have loopRun := copyLoopNonnegative temporary bitmap pattern
      {target with clock := target.clock + allowance}
      {loaded with clock := loaded.clock + allowance} prefixRun reads.1 nonnegative
    refine ⟨allowance, decide (pattern = 1), value,
      base + bytesInWord width * BitVec.ofNat width nextIndex,
      resultMemory, ?_, finalHeap, ?_⟩
    · rw [loopRun, copyRun]
      dsimp only [loaded, loadBitmapState]
      congr 2
      apply HolFiniteMapExact.ext_lookup
      intro query
      simp only [List.nodup_cons, List.mem_cons, not_or] at distinct
      have tOne : temporary ≠ 1 := by omega
      have tb : temporary ≠ bitmap := by omega
      by_cases sentinel : pattern = BitVec.ofNat width 1 <;>
        by_cases qBitmap : query = bitmap <;>
        by_cases qOne : query = 1 <;>
        by_cases qTwo : query = 2 <;>
        by_cases qTemporary : query = temporary <;>
        simp [sentinel, qBitmap, qOne, qTwo, qTemporary, tOne, tb,
          HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
    · -- step bound
      have whileExitRun : evaluate (whileProg .less 1 (.imm 0)
          (listSeqHOL [copyEach temporary bitmap, loadInst 1 bitmap, addBytesInWordInst bitmap]),
          {loaded with clock := loaded.clock + allowance}) =
          (none, {loaded with clock := loaded.clock + allowance}) :=
        copyWhileExit temporary bitmap pattern _ reads.1 nonnegative
      obtain ⟨bs1, bp1, bp2⟩ := steps_prefix_runs bitmap
        {target with clock := target.clock + allowance}
        {loaded with clock := loaded.clock + allowance} prefixRun
      have lhsLe := steps_copyLoop_le temporary bitmap
        {target with clock := target.clock + allowance} bs1
        {loaded with clock := loaded.clock + allowance}
        {loaded with clock := loaded.clock + allowance} bp1 bp2 whileExitRun
      have whileLe := steps_while_exit temporary bitmap pattern
        {loaded with clock := loaded.clock + allowance} reads.1 nonnegative
      have hpatBound : pattern.toNat + 1 ≤ 2 ^ width := by
        have := pattern.isLt
        omega
      have hbase : 15 * 2 ^ width + 11 ≤ copyLoopSteps width (bitmaps.length - i) := by
        have h := copyLoopSteps_mono width (Nat.zero_le (bitmaps.length - i))
        simp only [copyLoopSteps, Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.zero_add] at h ⊢
        exact h
      omega

end SteppedFlapjack.StackRemoveSteps
