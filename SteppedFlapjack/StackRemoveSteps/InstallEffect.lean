import SteppedFlapjack.StackRemoveSteps.OraclePrefix
/-! Exact installation effects and finite-prefix budget preservation. -/

namespace SteppedFlapjack.StackRemoveSteps.CompCorrect
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.StackSemStateOps Flapjack.StackSemControl Flapjack.StackSemEvaluate
open Flapjack.Compiler.Encoders.Asm
variable {width : Nat} [NeZero width] {C F : Type}

theorem evaluate_install_effect (ptr len dptr dlen ret : Nat)
    (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.install ptr len dptr dlen ret : HolProg width), s) = (r, t)) :
    (t.code = s.code ∧ t.compileOracle = s.compileOracle ∧ t.bitmaps = s.bitmaps) ∨
    (t.code = sptUnion s.code (sptFromAList (s.compileOracle 0).2.1) ∧
     t.compileOracle = holShiftSeq 1 s.compileOracle ∧
     t.bitmaps = s.bitmaps ++ (s.compileOracle 0).2.2) := by
  classical
  cases h1 : getVar ptr s with
  | none =>
    rw [evaluate_install] at h; simp only [h1] at h
    obtain ⟨-, rfl⟩ := h; exact Or.inl ⟨rfl, rfl, rfl⟩
  | some v1 =>
    cases v1 with
    | loc l o =>
      rw [evaluate_install] at h; simp only [h1] at h
      obtain ⟨-, rfl⟩ := h; exact Or.inl ⟨rfl, rfl, rfl⟩
    | word w1 =>
      cases h2 : getVar len s with
      | none =>
        rw [evaluate_install] at h; simp only [h1, h2] at h
        obtain ⟨-, rfl⟩ := h; exact Or.inl ⟨rfl, rfl, rfl⟩
      | some v2 =>
        cases v2 with
        | loc l o =>
          rw [evaluate_install] at h; simp only [h1, h2] at h
          obtain ⟨-, rfl⟩ := h; exact Or.inl ⟨rfl, rfl, rfl⟩
        | word w2 =>
          cases h3 : getVar dptr s with
          | none =>
            rw [evaluate_install] at h; simp only [h1, h2, h3] at h
            obtain ⟨-, rfl⟩ := h; exact Or.inl ⟨rfl, rfl, rfl⟩
          | some v3 =>
            cases v3 with
            | loc l o =>
              rw [evaluate_install] at h; simp only [h1, h2, h3] at h
              obtain ⟨-, rfl⟩ := h; exact Or.inl ⟨rfl, rfl, rfl⟩
            | word w3 =>
              cases h4 : getVar dlen s with
              | none =>
                rw [evaluate_install] at h; simp only [h1, h2, h3, h4] at h
                obtain ⟨-, rfl⟩ := h; exact Or.inl ⟨rfl, rfl, rfl⟩
              | some v4 =>
                cases v4 with
                | loc l o =>
                  rw [evaluate_install] at h; simp only [h1, h2, h3, h4] at h
                  obtain ⟨-, rfl⟩ := h; exact Or.inl ⟨rfl, rfl, rfl⟩
                | word w4 =>
                  rcases hcfg : s.compileOracle 0 with ⟨cfg, progs, bm⟩
                  cases hb1 : wordSemBufferFlush s.codeBuffer w1 w2 with
                  | none =>
                    rw [evaluate_install] at h; simp only [h1, h2, h3, h4, hcfg, hb1] at h
                    obtain ⟨-, rfl⟩ := h; exact Or.inl ⟨rfl, rfl, rfl⟩
                  | some p1 =>
                    rcases p1 with ⟨bytes, cb⟩
                    cases hb2 : (if s.useStack then wordSemBufferFlush s.dataBuffer w3 w4 else some (bm, s.dataBuffer)) with
                    | none =>
                      rw [evaluate_install] at h; simp only [h1, h2, h3, h4, hcfg, hb1, hb2] at h
                      obtain ⟨-, rfl⟩ := h; exact Or.inl ⟨rfl, rfl, rfl⟩
                    | some p2 =>
                      rcases p2 with ⟨data, db⟩
                      cases hcomp : s.compile cfg progs with
                      | none =>
                        rw [evaluate_install] at h; simp only [h1, h2, h3, h4, hcfg, hb1, hb2, hcomp] at h
                        obtain ⟨-, rfl⟩ := h; exact Or.inl ⟨rfl, rfl, rfl⟩
                      | some cp =>
                        rcases cp with ⟨bytes', cfg'⟩
                        cases hp : progs with
                        | nil =>
                          rw [hp] at hcomp
                          rw [evaluate_install] at h; simp only [h1, h2, h3, h4, hcfg, hb1, hb2, hp, hcomp] at h
                          obtain ⟨-, rfl⟩ := h; exact Or.inl ⟨rfl, rfl, rfl⟩
                        | cons entry rest =>
                          rcases entry with ⟨k, prog⟩
                          rw [hp] at hcomp
                          rw [evaluate_install] at h; simp only [h1, h2, h3, h4, hcfg, hb1, hb2, hp, hcomp] at h
                          split_ifs at h
                          · obtain ⟨-, rfl⟩ := h
                            apply Or.inr
                            exact ⟨rfl, rfl, rfl⟩
                          · obtain ⟨-, rfl⟩ := h; exact Or.inl ⟨rfl, rfl, rfl⟩

/-- A single install either preserves a finite budget or consumes its head. -/
theorem evaluate_install_prefix {B K n : Nat} {bounds : BitVec width × BitVec width}
    (ptr len dptr dlen ret : Nat) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (h : evaluate ((.install ptr len dptr dlen ret : HolProg width), s) = (r, t))
    (hc : codeBound B bounds K s) (ho : oraclePrefixBound B bounds K (n + 1) s)
    (hb : s.bitmaps.length + oracleBitmapBudget (n + 1) s.compileOracle ≤ B) :
    ∃ used ≤ 1, codeBound B bounds K t ∧
      oraclePrefixBound B bounds K (n + 1 - used) t ∧
      t.bitmaps.length + oracleBitmapBudget (n + 1 - used) t.compileOracle ≤ B := by
  rcases evaluate_install_effect ptr len dptr dlen ret s t r h with unchanged | installed
  · rcases unchanged with ⟨hcode, horacle, hbitmap⟩
    refine ⟨0, by omega, codeBound_congr hcode hc, ?_, ?_⟩
    · intro index hi name program hm
      rw [horacle] at hm
      exact ho index (by omega) name program hm
    · simpa only [Nat.sub_zero, horacle, hbitmap] using hb
  · rcases installed with ⟨hcode, horacle, hbitmap⟩
    refine ⟨1, by omega, ?_, ?_, ?_⟩
    · intro label program hlookup
      rw [hcode] at hlookup
      exact install_codeBound_of_prefix s hc ho label program hlookup
    · simpa only [Nat.add_sub_cancel_right] using oraclePrefixBound_shift s t ho horacle
    · simpa only [Nat.add_sub_cancel_right] using oracleBitmapBudget_install s t horacle hbitmap hb

end SteppedFlapjack.StackRemoveSteps.CompCorrect
