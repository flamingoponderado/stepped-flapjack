import SteppedFlapjack.StackRemoveSteps.CodeBounds

/-! Finite bounds for code and the oracle entries consumed by a run.

Unlike a bound on an arbitrary whole oracle, these bounds are computed from
finite lists. An installation advances the prefix and spends the bitmap words
in its first entry. -/

namespace SteppedFlapjack.StackRemoveSteps.CompCorrect
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
variable {width : Nat} [NeZero width] {C F : Type}

def oraclePrefixBound (B : Nat) (bounds : BitVec width × BitVec width) (K n : Nat)
    (s : StackSemStateFiniteExact width C F) : Prop :=
  ∀ index, index < n → ∀ name program,
    (name, program) ∈ (s.compileOracle index).2.1 → leafCost B bounds program ≤ K

def maxListNat : List Nat → Nat
  | [] => 0
  | x :: xs => max x (maxListNat xs)

theorem le_maxListNat_of_mem (x : Nat) (xs : List Nat) (h : x ∈ xs) : x ≤ maxListNat xs := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    simp only [List.mem_cons] at h
    simp only [maxListNat]
    rcases h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

def oraclePrefixCost (B : Nat) (bounds : BitVec width × BitVec width) (n : Nat)
    (s : StackSemStateFiniteExact width C F) : Nat :=
  maxListNat ((List.range n).flatMap fun index =>
    ((s.compileOracle index).2.1.map fun entry => leafCost B bounds entry.2))

theorem oraclePrefixCost_bound (B : Nat) (bounds : BitVec width × BitVec width) (n : Nat)
    (s : StackSemStateFiniteExact width C F) :
    oraclePrefixBound B bounds (oraclePrefixCost B bounds n s) n s := by
  intro index hi name program hm
  apply le_maxListNat_of_mem
  apply List.mem_flatMap.mpr
  refine ⟨index, List.mem_range.mpr hi, ?_⟩
  exact List.mem_map.mpr ⟨(name, program), hm, rfl⟩

theorem oraclePrefixBound_shift {B K n : Nat} {bounds : BitVec width × BitVec width}
    (s t : StackSemStateFiniteExact width C F)
    (h : oraclePrefixBound B bounds K (n + 1) s)
    (shift : t.compileOracle = holShiftSeq 1 s.compileOracle) :
    oraclePrefixBound B bounds K n t := by
  intro index hi name program hm
  rw [shift] at hm
  exact h (index + 1) (by omega) name program hm

/-- The first oracle entry is covered whenever the prefix is nonempty. -/
theorem oraclePrefixBound_head {B K n : Nat} {bounds : BitVec width × BitVec width}
    (s : StackSemStateFiniteExact width C F)
    (h : oraclePrefixBound B bounds K (n + 1) s)
    (name : Nat) (program : HolProg width)
    (hm : (name, program) ∈ (s.compileOracle 0).2.1) :
    leafCost B bounds program ≤ K :=
  h 0 (by omega) name program hm

/-- Installing the first prefix entry preserves the initial code bound. -/
theorem install_codeBound_of_prefix {B K n : Nat} {bounds : BitVec width × BitVec width}
    (s : StackSemStateFiniteExact width C F)
    (hcode : codeBound B bounds K s) (horacle : oraclePrefixBound B bounds K (n + 1) s)
    (label : Nat) (program : HolProg width)
    (hlookup : sptLookup label (sptUnion s.code (sptFromAList (s.compileOracle 0).2.1)) = some program) :
    leafCost B bounds program ≤ K :=
  install_codeBound s (s.compileOracle 0).2.1 hcode
    (oraclePrefixBound_head s horacle) label program hlookup

/-- A finite upper bound on the costs of programs in the initial code tree. -/
def codeCost (B : Nat) (bounds : BitVec width × BitVec width)
    (s : StackSemStateFiniteExact width C F) : Nat :=
  maxListNat ((sptToAList s.code).map fun entry => leafCost B bounds entry.2)

theorem codeCost_bound (B : Nat) (bounds : BitVec width × BitVec width)
    (s : StackSemStateFiniteExact width C F) : codeBound B bounds (codeCost B bounds s) s := by
  intro label program hlookup
  have hlist : sptAListLookup label (sptToAList s.code) = some program := by
    have heq := sptLookup_sptFromAList_sptToAList label s.code
    rw [hlookup] at heq
    simpa only [sptLookup_sptFromAList] using heq
  have hmem := sptAListLookup_mem label (sptToAList s.code) program hlist
  apply le_maxListNat_of_mem
  exact List.mem_map.mpr ⟨(label, program), hmem, rfl⟩

/-- The initial code tree and a finite oracle prefix share this computable factor. -/
def initialCodeOracleCost (B : Nat) (bounds : BitVec width × BitVec width) (n : Nat)
    (s : StackSemStateFiniteExact width C F) : Nat :=
  max (codeCost B bounds s) (oraclePrefixCost B bounds n s)

theorem initialCodeOracleCost_bounds (B : Nat) (bounds : BitVec width × BitVec width) (n : Nat)
    (s : StackSemStateFiniteExact width C F) :
    codeBound B bounds (initialCodeOracleCost B bounds n s) s ∧
    oraclePrefixBound B bounds (initialCodeOracleCost B bounds n s) n s := by
  constructor
  · intro label program hlookup
    exact (codeCost_bound B bounds s label program hlookup).trans (le_max_left _ _)
  · intro index hi name program hm
    exact (oraclePrefixCost_bound B bounds n s index hi name program hm).trans (le_max_right _ _)

/-- A positive factor for the initial program, code tree and finite oracle prefix. -/
def initialRunCost (B : Nat) (bounds : BitVec width × BitVec width) (n : Nat)
    (program : HolProg width) (s : StackSemStateFiniteExact width C F) : Nat :=
  max 1 (max (leafCost B bounds program) (initialCodeOracleCost B bounds n s))

theorem initialRunCost_bounds (B : Nat) (bounds : BitVec width × BitVec width) (n : Nat)
    (program : HolProg width) (s : StackSemStateFiniteExact width C F) :
    1 ≤ initialRunCost B bounds n program s ∧
    leafCost B bounds program ≤ initialRunCost B bounds n program s ∧
    codeBound B bounds (initialRunCost B bounds n program s) s ∧
    oraclePrefixBound B bounds (initialRunCost B bounds n program s) n s := by
  have h := initialCodeOracleCost_bounds B bounds n s
  have hc : initialCodeOracleCost B bounds n s ≤ initialRunCost B bounds n program s :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _), ?_, ?_⟩
  · intro label code hl
    exact (h.1 label code hl).trans hc
  · intro index hi name code hm
    exact (h.2 index hi name code hm).trans hc

/-- Total bitmap words supplied by the first `n` oracle entries. -/
def oracleBitmapBudget (n : Nat) (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => (oracle 0).2.2.length + oracleBitmapBudget n (holShiftSeq 1 oracle)

/-- Bitmap space needed by the initial state and the first `n` installations. -/
def initialBitmapBudget (n : Nat) (s : StackSemStateFiniteExact width C F) : Nat :=
  s.bitmaps.length + oracleBitmapBudget n s.compileOracle

/-- Computable factor for an initial program and a bounded number of installs. -/
def computedRunCost (bounds : BitVec width × BitVec width) (n : Nat)
    (program : HolProg width) (s : StackSemStateFiniteExact width C F) : Nat :=
  initialRunCost (initialBitmapBudget n s) bounds n program s

theorem computedRunCost_bounds (bounds : BitVec width × BitVec width) (n : Nat)
    (program : HolProg width) (s : StackSemStateFiniteExact width C F) :
    s.bitmaps.length ≤ initialBitmapBudget n s ∧
    1 ≤ computedRunCost bounds n program s ∧
    leafCost (initialBitmapBudget n s) bounds program ≤ computedRunCost bounds n program s ∧
    codeBound (initialBitmapBudget n s) bounds (computedRunCost bounds n program s) s ∧
    oraclePrefixBound (initialBitmapBudget n s) bounds (computedRunCost bounds n program s) n s := by
  constructor
  · simp only [initialBitmapBudget]; omega
  · exact initialRunCost_bounds (initialBitmapBudget n s) bounds n program s

/-- A successful installation spends the first entry of the finite budget. -/
theorem oracleBitmapBudget_install {n limit : Nat}
    (s t : StackSemStateFiniteExact width C F)
    (horacle : t.compileOracle = holShiftSeq 1 s.compileOracle)
    (hbitmap : t.bitmaps = s.bitmaps ++ (s.compileOracle 0).2.2)
    (h : s.bitmaps.length + oracleBitmapBudget (n + 1) s.compileOracle ≤ limit) :
    t.bitmaps.length + oracleBitmapBudget n t.compileOracle ≤ limit := by
  rw [horacle, hbitmap, List.length_append]
  simp only [oracleBitmapBudget] at h
  omega

theorem oracleBitmapBudget_add (n m : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)) :
    oracleBitmapBudget (n + m) oracle =
      oracleBitmapBudget n oracle + oracleBitmapBudget m (holShiftSeq n oracle) := by
  induction n generalizing oracle with
  | zero =>
    have hzero : holShiftSeq 0 oracle = oracle := by
      funext i
      simp [holShiftSeq]
    simp [oracleBitmapBudget, hzero]
  | succ n ih =>
    simp only [Nat.succ_add, oracleBitmapBudget, ih]
    have shift : holShiftSeq n (holShiftSeq 1 oracle) = holShiftSeq (n + 1) oracle := by
      funext i
      simp only [holShiftSeq]
      congr 1
    rw [shift]
    omega

theorem oraclePrefixBound_take {B K n m : Nat} {bounds : BitVec width × BitVec width}
    (s : StackSemStateFiniteExact width C F) (h : oraclePrefixBound B bounds K n s)
    (hm : m ≤ n) : oraclePrefixBound B bounds K m s := by
  intro index hi name program hmem
  exact h index (by omega) name program hmem

theorem oraclePrefixBound_drop {B K n used : Nat} {bounds : BitVec width × BitVec width}
    (s t : StackSemStateFiniteExact width C F) (h : oraclePrefixBound B bounds K n s)
    (hused : used ≤ n) (horacle : t.compileOracle = holShiftSeq used s.compileOracle) :
    oraclePrefixBound B bounds K (n - used) t := by
  intro index hi name program hm
  rw [horacle] at hm
  exact h (index + used) (by omega) name program hm

theorem oracleBitmapBudget_drop {n used cap : Nat}
    (s t : StackSemStateFiniteExact width C F)
    (hused : used ≤ n) (horacle : t.compileOracle = holShiftSeq used s.compileOracle)
    (hbitmap : t.bitmaps.length ≤ s.bitmaps.length + oracleBitmapBudget used s.compileOracle)
    (hcap : s.bitmaps.length + oracleBitmapBudget n s.compileOracle ≤ cap) :
    t.bitmaps.length + oracleBitmapBudget (n - used) t.compileOracle ≤ cap := by
  have hn : used + (n - used) = n := by omega
  have hs := oracleBitmapBudget_add used (n - used) s.compileOracle
  rw [hn] at hs
  rw [horacle]
  omega

end SteppedFlapjack.StackRemoveSteps.CompCorrect
