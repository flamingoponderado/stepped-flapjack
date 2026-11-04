import Flapjack.Compiler.Backend.LabToTarget.RemoveLabels
import Flapjack.Compiler.Backend.LabSem.State
import SteppedFlapjack.RiscVSteps.Defs

/-!
# Tick bounds for the `lab_to_target` simulation

Definitions for the bounded copy of Flapjack's `lab_to_target`
`compile_correct` (stepped-flapjack#2, phase B).

One source `lab` instruction is simulated by the machine code of its target
line: the encoding of the instruction followed by NOP padding. The encoder
bound `encoderCorrectWithin t steps` (phase A) counts the target ticks of
each encoded instruction. `StepsFit unit steps t` says that an instruction
running for `steps i` ticks takes at least `unit * steps i` bytes, so a line
of `b` bytes runs for at most `b / unit` ticks. For RISC-V, `unit = 4`.

The lines a run can execute are the lines of the target code `code2` and the
lines installed later from the code buffer. `lineByteBound` bounds the byte
length of both kinds, and `labTickBound` adds the one extra tick of an FFI
call or code-cache entry to give the per-instruction tick bound `L`.

This is stepped-flapjack infrastructure with no HOL counterpart.
-/

namespace SteppedFlapjack.LabToTargetSteps

open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmProps
open SteppedFlapjack.RiscVSteps

/-- The lines of all sections of `code`, in order. -/
def codeLines {width : Nat} [NeZero width] (code : LabProgHOL width) :
    List (LabLineHOL width) :=
  code.flatMap (·.lines)

/-- The largest byte length of a line of `code`. -/
def maxLineBytes {width : Nat} [NeZero width] (code : LabProgHOL width) : Nat :=
  ((codeLines code).map fun j => (lineBytes j).length).foldr max 0

/-- Every line of `code` is at most `maxLineBytes code` bytes long. -/
theorem le_maxLineBytes {width : Nat} [NeZero width] {code : LabProgHOL width}
    {j : LabLineHOL width} (h : j ∈ codeLines code) :
    (lineBytes j).length ≤ maxLineBytes code := by
  unfold maxLineBytes
  generalize codeLines code = ls at h
  induction ls with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · simp only [List.map_cons, List.foldr_cons]
      exact le_trans (ih h) (Nat.le_max_right _ _)

/-- `maxLineBytes code` is the least bound on the lines of `code`. -/
theorem maxLineBytes_le {width : Nat} [NeZero width] {code : LabProgHOL width} {M : Nat}
    (h : ∀ j ∈ codeLines code, (lineBytes j).length ≤ M) : maxLineBytes code ≤ M := by
  unfold maxLineBytes
  generalize codeLines code = ls at h
  induction ls with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact Nat.max_le.mpr ⟨h x (by simp), ih fun j hj => h j (by simp [hj])⟩

/-- A line of `code` is no longer than the whole program. -/
theorem lineBytes_length_le_progToBytes {width : Nat} [NeZero width]
    {code : LabProgHOL width} {j : LabLineHOL width} (h : j ∈ codeLines code) :
    (lineBytes j).length ≤ (progToBytes code).length := by
  rw [progToBytesMap]
  obtain ⟨sec, hsec, hj⟩ := List.mem_flatMap.mp h
  have h1 : List.Sublist (lineBytes j) (sec.lines.map lineBytes).flatten :=
    List.sublist_flatten_of_mem (List.mem_map_of_mem hj)
  have h2 : List.Sublist (sec.lines.map lineBytes).flatten
      (code.map (fun s => (s.lines.map lineBytes).flatten)).flatten :=
    List.sublist_flatten_of_mem (List.mem_map_of_mem (f := fun s => (s.lines.map lineBytes).flatten)
      hsec)
  exact (h1.trans h2).length_le

/-- The lines of an appended program. -/
theorem codeLines_append {width : Nat} [NeZero width] (a b : LabProgHOL width) :
    codeLines (a ++ b) = codeLines a ++ codeLines b := by
  simp [codeLines]

/-- A bound on the byte length of every line a run can execute: a line of the
target code `code2`, or a line installed later from the code buffer `cb`,
which has room for `cb.buffer.length + cb.spaceLeft` bytes. -/
def lineByteBound {width : Nat} [NeZero width] (code2 : LabProgHOL width)
    (cb : WordSemBuffer width 8) : Nat :=
  max (maxLineBytes code2) (cb.buffer.length + cb.spaceLeft)

/-- The per-instruction tick bound `L`: a line of at most
`lineByteBound code2 cb` bytes runs for at most `lineByteBound code2 cb / unit`
ticks, plus one tick for an FFI call or code-cache entry. -/
def labTickBound {width : Nat} [NeZero width] (unit : Nat) (code2 : LabProgHOL width)
    (cb : WordSemBuffer width 8) : Nat :=
  lineByteBound code2 cb / unit + 1

/-- Installing a program `secList` no longer than the code buffer's contents,
with at most the old space left, keeps `lineByteBound`. -/
theorem lineByteBound_install {width : Nat} [NeZero width] {code2 secList : LabProgHOL width}
    {cb0 cb : WordSemBuffer width 8} (hsec : (progToBytes secList).length ≤ cb0.buffer.length)
    (hcb : cb.buffer.length + cb.spaceLeft ≤ cb0.buffer.length + cb0.spaceLeft) :
    lineByteBound (code2 ++ secList) cb ≤ lineByteBound code2 cb0 := by
  unfold lineByteBound
  refine Nat.max_le.mpr ⟨maxLineBytes_le fun j hj => ?_, le_trans hcb (Nat.le_max_right _ _)⟩
  rcases List.mem_append.mp ((codeLines_append code2 secList) ▸ hj) with h | h
  · exact le_trans (le_maxLineBytes h) (Nat.le_max_left _ _)
  · exact le_trans (lineBytes_length_le_progToBytes h)
      (le_trans hsec (le_trans (Nat.le_add_right _ _) (Nat.le_max_right _ _)))

/-- `labTickBound` is monotone in `lineByteBound`. -/
theorem labTickBound_mono {width : Nat} [NeZero width] {unit : Nat}
    {code2 code2' : LabProgHOL width} {cb cb' : WordSemBuffer width 8}
    (h : lineByteBound code2' cb' ≤ lineByteBound code2 cb) :
    labTickBound unit code2' cb' ≤ labTickBound unit code2 cb :=
  Nat.add_le_add_right (Nat.div_le_div_right h) 1

/-- Flushing the code buffer returns its contents and keeps its space left. -/
theorem wordSemBufferFlush_some {width : Nat} [NeZero width] {cb0 cb : WordSemBuffer width 8}
    {a b : BitVec width} {flushed : List (BitVec 8)}
    (h : wordSemBufferFlush cb0 a b = some (flushed, cb)) :
    flushed = cb0.buffer ∧ cb.buffer = [] ∧ cb.spaceLeft = cb0.spaceLeft := by
  simp only [wordSemBufferFlush] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩
  · cases h

/-- An instruction that runs for `steps i` ticks takes at least `unit * steps i`
bytes to encode, with `unit` positive. -/
def StepsFit {width : Nat} [NeZero width] {β γ : Type} (unit : Nat)
    (steps : HolAsm width → Nat) (t : HolAsmTarget width β γ) : Prop :=
  0 < unit ∧ ∀ i, unit * steps i ≤ (t.config.encode i).length

/-- A line of `code2` of at least `unit * l` bytes gives `l ≤ L - 1`. -/
theorem le_labTickBound_of_bytes {width : Nat} [NeZero width] {unit l : Nat}
    {code2 : LabProgHOL width} {cb : WordSemBuffer width 8} {bytes : List (BitVec 8)}
    (hunit : 0 < unit) (hl : unit * l ≤ bytes.length)
    (hb : bytes.length ≤ maxLineBytes code2) :
    l ≤ labTickBound unit code2 cb - 1 := by
  simp only [labTickBound, Nat.add_sub_cancel]
  refine (Nat.le_div_iff_mul_le hunit).mpr ?_
  rw [Nat.mul_comm]
  exact le_trans hl (le_trans hb (Nat.le_max_left _ _))

/-- One source instruction: `l ≤ L` ticks followed by a run within the bound
for one clock less gives a run within the bound. -/
theorem tick_step_bound {L c k l : Nat} (hc : c ≠ 0) (hk : k ≤ (L - 1) * (c - 1))
    (hl : l ≤ L) : k + l - 1 ≤ (L - 1) * c := by
  obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hk
  rw [Nat.mul_succ]
  omega

/-- One source instruction with an extra tick: `l + 1 ≤ L` ticks followed by
a run within the bound for one clock less gives a run within the bound. -/
theorem tick_step_bound_succ {L c k l : Nat} (hc : c ≠ 0) (hk : k ≤ (L - 1) * (c - 1))
    (hl : l ≤ L - 1) : k + l ≤ (L - 1) * c := by
  obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hk
  rw [Nat.mul_succ]
  omega

/-- A final source instruction of at most `L - 1` ticks is within the bound. -/
theorem tick_last_bound {L c l : Nat} (hc : c ≠ 0) (hl : l ≤ L - 1) : l ≤ (L - 1) * c :=
  le_trans hl (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hc))

/-- A smaller tick bound for one clock less is a bound for the larger one. -/
theorem tick_bound_mono {L L' c k : Nat} (hL : L' ≤ L) (hk : k ≤ (L' - 1) * c) :
    k ≤ (L - 1) * c :=
  le_trans hk (Nat.mul_le_mul_right _ (by omega))

end SteppedFlapjack.LabToTargetSteps
