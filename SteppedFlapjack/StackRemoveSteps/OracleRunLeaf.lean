import SteppedFlapjack.StackRemoveSteps.OracleRunControl
/-! Oracle and bitmap effects of all non-recursive instructions. -/

namespace SteppedFlapjack.StackRemoveSteps.CompCorrect
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.StackSemEvaluate
open Flapjack.StackSemStateOps Flapjack.Compiler.Encoders.Asm SteppedFlapjack.StackSteps
variable {width : Nat} [NeZero width] {C F : Type}
theorem bufferWrite_fields_code
    (r1 r2 : Nat) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (h : evaluate ((.codeBufferWrite r1 r2 : HolProg width), s) = (r, t))
    : t.compileOracle = s.compileOracle ∧ t.bitmaps = s.bitmaps := by
  have hp : t.compileOracle = s.compileOracle ∧ t.bitmaps = s.bitmaps := by
    cases h1 : getVar r1 s with
    | none =>
      rw [evaluate_codeBufferWrite] at h
      simp only [h1] at h
      obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
    | some v1 =>
      cases v1 with
      | loc l o =>
        rw [evaluate_codeBufferWrite] at h
        simp only [h1] at h
        obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
      | word w1 =>
        cases h2 : getVar r2 s with
        | none =>
          rw [evaluate_codeBufferWrite] at h
          simp only [h1, h2] at h
          obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
        | some v2 =>
          cases v2 with
          | loc l o =>
            rw [evaluate_codeBufferWrite] at h
            simp only [h1, h2] at h
            obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
          | word w2 =>
            rw [evaluate_codeBufferWrite] at h
            simp only [h1, h2] at h
            cases hw : wordSemBufferWrite s.codeBuffer w1 (BitVec.setWidth 8 w2) with
            | some newCb =>
              simp only [hw] at h
              obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
            | none =>
              simp only [hw] at h
              obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
  exact hp
theorem bufferWrite_fields_data
    (r1 r2 : Nat) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (h : evaluate ((.dataBufferWrite r1 r2 : HolProg width), s) = (r, t))
    : t.compileOracle = s.compileOracle ∧ t.bitmaps = s.bitmaps := by
  by_cases hs : ¬ s.useStack
  · rw [evaluate_dataBufferWrite] at h
    simp only [if_pos hs] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨rfl, rfl⟩
  · have hp : t.compileOracle = s.compileOracle ∧ t.bitmaps = s.bitmaps := by
      cases h1 : getVar r1 s with
      | none =>
        rw [evaluate_dataBufferWrite] at h
        simp only [if_neg hs, h1] at h
        obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
      | some v1 =>
        cases v1 with
        | loc l o =>
          rw [evaluate_dataBufferWrite] at h
          simp only [if_neg hs, h1] at h
          obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
        | word w1 =>
          cases h2 : getVar r2 s with
          | none =>
            rw [evaluate_dataBufferWrite] at h
            simp only [if_neg hs, h1, h2] at h
            obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
          | some v2 =>
            cases v2 with
            | loc l o =>
              rw [evaluate_dataBufferWrite] at h
              simp only [if_neg hs, h1, h2] at h
              obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
            | word w2 =>
              rw [evaluate_dataBufferWrite] at h
              simp only [if_neg hs, h1, h2] at h
              cases hw : wordSemBufferWrite s.dataBuffer w1 w2 with
              | some newCb =>
                simp only [hw] at h
                obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
              | none =>
                simp only [hw] at h
                obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
    exact hp

theorem oracleRunEffect_codeBufferWrite (r1 r2 : Nat)
    (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.codeBufferWrite r1 r2 : HolProg width), s) = (r, t)) :
    oracleRunEffect (steps (.codeBufferWrite r1 r2, s)) s t := by
  have fields := bufferWrite_fields_code r1 r2 s t r h
  exact oracleRunEffect_of_fields _ s t fields.1 fields.2

theorem oracleRunEffect_dataBufferWrite (r1 r2 : Nat)
    (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.dataBufferWrite r1 r2 : HolProg width), s) = (r, t)) :
    oracleRunEffect (steps (.dataBufferWrite r1 r2, s)) s t := by
  have fields := bufferWrite_fields_data r1 r2 s t r h
  exact oracleRunEffect_of_fields _ s t fields.1 fields.2
theorem oracleRunEffect_skip
    (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.skip : HolProg width), s) = (r, t)) :
    oracleRunEffect (steps ((.skip : HolProg width), s)) s t := by
  rw [evaluate_skip] at h
  obtain ⟨-, rfl⟩ := h
  exact oracleRunEffect_of_fields _ _ _ rfl rfl


theorem oracleRunEffect_break
    (n : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.break n : HolProg width), s) = (r, t)) :
    oracleRunEffect (steps ((.break n : HolProg width), s)) s t := by
  rw [evaluate_break] at h
  obtain ⟨-, rfl⟩ := h
  exact oracleRunEffect_of_fields _ _ _ rfl rfl


theorem oracleRunEffect_continue
    (n : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.continue n : HolProg width), s) = (r, t)) :
    oracleRunEffect (steps ((.continue n : HolProg width), s)) s t := by
  rw [evaluate_continue] at h
  obtain ⟨-, rfl⟩ := h
  exact oracleRunEffect_of_fields _ _ _ rfl rfl


theorem oracleRunEffect_halt
    (v : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.halt v : HolProg width), s) = (r, t)) :
    oracleRunEffect (steps ((.halt v : HolProg width), s)) s t := by
  cases hv : getVar v s with
  | none => rw [evaluate_halt, hv] at h; obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
  | some w =>
    rw [evaluate_halt, hv] at h; obtain ⟨-, rfl⟩ := h
    exact oracleRunEffect_of_fields _ _ _ rfl rfl


theorem oracleRunEffect_tick
    (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.tick : HolProg width), s) = (r, t)) :
    oracleRunEffect (steps ((.tick : HolProg width), s)) s t := by
  rw [evaluate_tick] at h
  split_ifs at h with hc
  · obtain ⟨-, rfl⟩ := h
    exact oracleRunEffect_of_fields _ _ _ rfl rfl
  · obtain ⟨-, rfl⟩ := h
    exact oracleRunEffect_of_fields _ _ _ rfl rfl

theorem oracleRunEffect_ret
    (n : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.ret n : HolProg width), s) = (r, t)) :
    oracleRunEffect (steps ((.ret n : HolProg width), s)) s t := by
  cases hv : getVar n s with
  | none => rw [evaluate_ret, hv] at h; obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
  | some w =>
    cases w with
    | loc l1 l2 => rw [evaluate_ret, hv] at h; obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
    | word w => rw [evaluate_ret, hv] at h; obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl


theorem oracleRunEffect_raise
    (n : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.raise n : HolProg width), s) = (r, t)) :
    oracleRunEffect (steps ((.raise n : HolProg width), s)) s t := by
  cases hv : getVar n s with
  | none => rw [evaluate_raise, hv] at h; obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
  | some w =>
    cases w with
    | loc l1 l2 => rw [evaluate_raise, hv] at h; obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
    | word w => rw [evaluate_raise, hv] at h; obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl


theorem oracleRunEffect_locValue
    (r0 l1 l2 : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.locValue r0 l1 l2 : HolProg width), s) = (r, t)) :
    oracleRunEffect (steps ((.locValue r0 l1 l2 : HolProg width), s)) s t := by
  rw [evaluate_locValue] at h
  split_ifs at h with hc
  · obtain ⟨-, rfl⟩ := h
    exact oracleRunEffect_of_fields _ _ _ rfl rfl
  · obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl


theorem oracleRunEffect_stackAlloc
    (n : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.stackAlloc n : HolProg width), s) = (r, t)) :
    oracleRunEffect (steps ((.stackAlloc n : HolProg width), s)) s t := by
  rw [evaluate_stackAlloc] at h
  split_ifs at h with hc
  · obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
  · obtain ⟨-, rfl⟩ := h
    exact oracleRunEffect_of_fields _ _ _ rfl rfl
  · obtain ⟨-, rfl⟩ := h
    exact oracleRunEffect_of_fields _ _ _ rfl rfl


theorem oracleRunEffect_stackFree
    (n : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.stackFree n : HolProg width), s) = (r, t)) :
    oracleRunEffect (steps ((.stackFree n : HolProg width), s)) s t := by
  rw [evaluate_stackFree] at h
  split_ifs at h with hc
  · obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
  · obtain ⟨-, rfl⟩ := h
    exact oracleRunEffect_of_fields _ _ _ rfl rfl
  · obtain ⟨-, rfl⟩ := h
    exact oracleRunEffect_of_fields _ _ _ rfl rfl


theorem oracleRunEffect_stackLoad
    (r0 n : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.stackLoad r0 n : HolProg width), s) = (r, t)) :
    oracleRunEffect (steps ((.stackLoad r0 n : HolProg width), s)) s t := by
  rw [evaluate_stackLoad] at h
  split_ifs at h with hc
  · obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
  · obtain ⟨-, rfl⟩ := h
    exact oracleRunEffect_of_fields _ _ _ rfl rfl
  · obtain ⟨-, rfl⟩ := h
    exact oracleRunEffect_of_fields _ _ _ rfl rfl


theorem oracleRunEffect_stackGetSize
    (r0 : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.stackGetSize r0 : HolProg width), s) = (r, t)) :
    oracleRunEffect (steps ((.stackGetSize r0 : HolProg width), s)) s t := by
  rw [evaluate_stackGetSize] at h
  split_ifs at h with hc
  · obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
  · obtain ⟨-, rfl⟩ := h
    exact oracleRunEffect_of_fields _ _ _ rfl rfl


theorem oracleRunEffect_bitmapLoad
    (r0 v : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.bitmapLoad r0 v : HolProg width), s) = (r, t)) :
    oracleRunEffect (steps ((.bitmapLoad r0 v : HolProg width), s)) s t := by
  rw [evaluate_bitmapLoad] at h
  split_ifs at h with hc
  · obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
  · cases hv : getVar v s with
    | none => simp only [hv] at h; obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
    | some w =>
      cases w
      case loc l1 l2 => simp only [hv] at h; obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
      case word wd =>
        simp only [hv] at h
        split_ifs at h with hc
        · obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
        · obtain ⟨-, rfl⟩ := h
          exact oracleRunEffect_of_fields _ _ _ rfl rfl

theorem oracleRunEffect_stackStore
    (r0 n : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.stackStore r0 n : HolProg width), s) = (r, t)) :
    oracleRunEffect (steps ((.stackStore r0 n : HolProg width), s)) s t := by
  rw [evaluate_stackStore] at h
  split_ifs at h with hc
  · obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
  · obtain ⟨-, rfl⟩ := h
    exact oracleRunEffect_of_fields _ _ _ rfl rfl
  · cases hv : getVar r0 s
    case none =>
      simp only [hv] at h; obtain ⟨-, rfl⟩ := h
      exact oracleRunEffect_of_fields _ _ _ rfl rfl
    case some val =>
      simp only [hv] at h; obtain ⟨-, rfl⟩ := h
      exact oracleRunEffect_of_fields _ _ _ rfl rfl


theorem oracleRunEffect_stackSetSize
    (r0 : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.stackSetSize r0 : HolProg width), s) = (r, t)) :
    oracleRunEffect (steps ((.stackSetSize r0 : HolProg width), s)) s t := by
  rw [evaluate_stackSetSize] at h
  split_ifs at h with hc
  · obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
  · cases hv : getVar r0 s
    case none =>
      simp only [hv] at h; obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
    case some val =>
      cases val
      case loc l1 l2 => simp only [hv] at h; obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
      case word wd =>
        simp only [hv] at h
        split_ifs at h with hc
        · obtain ⟨-, rfl⟩ := h
          exact oracleRunEffect_of_fields _ _ _ rfl rfl
        · obtain ⟨-, rfl⟩ := h
          exact oracleRunEffect_of_fields _ _ _ rfl rfl

theorem oracleRunEffect_stackLoadAny
    (r0 rn : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.stackLoadAny r0 rn : HolProg width), s) = (r, t)) :
    oracleRunEffect (steps ((.stackLoadAny r0 rn : HolProg width), s)) s t := by
  cases hv : getVar rn s with
  | none =>
    rw [evaluate_stackLoadAny] at h; simp only [hv] at h
    split_ifs at h
    · obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
    · obtain ⟨-, rfl⟩ := h
      exact oracleRunEffect_of_fields _ _ _ rfl rfl
  | some v =>
    cases v with
    | loc l o =>
      rw [evaluate_stackLoadAny] at h; simp only [hv] at h
      split_ifs at h
      · obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
      · obtain ⟨-, rfl⟩ := h
        exact oracleRunEffect_of_fields _ _ _ rfl rfl
    | word w =>
      rw [evaluate_stackLoadAny] at h; simp only [hv] at h
      split_ifs at h
      · obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
      · obtain ⟨-, rfl⟩ := h
        exact oracleRunEffect_of_fields _ _ _ rfl rfl
      · obtain ⟨-, rfl⟩ := h
        exact oracleRunEffect_of_fields _ _ _ rfl rfl


theorem oracleRunEffect_stackStoreAny
    (r0 rn : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.stackStoreAny r0 rn : HolProg width), s) = (r, t)) :
    oracleRunEffect (steps ((.stackStoreAny r0 rn : HolProg width), s)) s t := by
  cases h1 : getVar r0 s with
  | none =>
    rw [evaluate_stackStoreAny] at h; simp only [h1] at h
    split_ifs at h
    · obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
    · obtain ⟨-, rfl⟩ := h
      exact oracleRunEffect_of_fields _ _ _ rfl rfl
  | some value =>
    cases h2 : getVar rn s with
    | none =>
      rw [evaluate_stackStoreAny] at h; simp only [h1, h2] at h
      split_ifs at h
      · obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
      · obtain ⟨-, rfl⟩ := h
        exact oracleRunEffect_of_fields _ _ _ rfl rfl
    | some v =>
      cases v with
      | loc l o =>
        rw [evaluate_stackStoreAny] at h; simp only [h1, h2] at h
        split_ifs at h
        · obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
        · obtain ⟨-, rfl⟩ := h
          exact oracleRunEffect_of_fields _ _ _ rfl rfl
      | word w =>
        rw [evaluate_stackStoreAny] at h; simp only [h1, h2] at h
        split_ifs at h
        · obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
        · obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
        · obtain ⟨-, rfl⟩ := h
          exact oracleRunEffect_of_fields _ _ _ rfl rfl


theorem oracleRunEffect_ffi
    (ffiIndex : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat)
    (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.ffi ffiIndex ptr len ptr2 len2 ret : HolProg width), s) = (r, t))
    : oracleRunEffect (steps ((.ffi ffiIndex ptr len ptr2 len2 ret : HolProg width), s)) s t := by
  cases h1 : getVar len s with
  | none =>
    rw [evaluate_ffi] at h; simp only [h1] at h
    obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
  | some v1 =>
    cases v1 with
    | loc l o =>
      rw [evaluate_ffi] at h; simp only [h1] at h
      obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
    | word w1 =>
      cases h2 : getVar ptr s with
      | none =>
        rw [evaluate_ffi] at h; simp only [h1, h2] at h
        obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
      | some v2 =>
        cases v2 with
        | loc l o =>
          rw [evaluate_ffi] at h; simp only [h1, h2] at h
          obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
        | word w2 =>
          cases h3 : getVar len2 s with
          | none =>
            rw [evaluate_ffi] at h; simp only [h1, h2, h3] at h
            obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
          | some v3 =>
            cases v3 with
            | loc l o =>
              rw [evaluate_ffi] at h; simp only [h1, h2, h3] at h
              obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
            | word w3 =>
              cases h4 : getVar ptr2 s with
              | none =>
                rw [evaluate_ffi] at h; simp only [h1, h2, h3, h4] at h
                obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
              | some v4 =>
                cases v4 with
                | loc l o =>
                  rw [evaluate_ffi] at h; simp only [h1, h2, h3, h4] at h
                  obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
                | word w4 =>
                  rw [evaluate_ffi] at h; simp only [h1, h2, h3, h4] at h
                  cases hb1 : readBytearrayWordHOL w2 w1.toNat (memLoadByteAuxExact s.memory s.mdomain s.be) with
                  | none =>
                    simp only [hb1] at h; obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
                  | some bytes =>
                    cases hb2 : readBytearrayWordHOL w4 w3.toNat (memLoadByteAuxExact s.memory s.mdomain s.be) with
                    | none =>
                      simp only [hb1, hb2] at h; obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
                    | some bytes2 =>
                      cases hf : callFFIHOL s.ffi (.extCall ffiIndex) bytes bytes2 with
                      | final outcome =>
                        simp only [hb1, hb2, hf] at h; obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
                      | ret newFfi newBytes =>
                        simp only [hb1, hb2, hf] at h; obtain ⟨-, rfl⟩ := h
                        exact oracleRunEffect_of_fields _ _ _ rfl rfl


theorem oracleRunEffect_get
    (v : Nat) (name : StoreName) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (h : evaluate ((.get v name : HolProg width), s) = (r, t)) :
    oracleRunEffect (steps ((.get v name : HolProg width), s)) s t := by
  cases hs : s.store.lookup (StackSemRegisterTransfers.storeOfSyntax name) with
  | none =>
    rw [evaluate_get, hs] at h
    split_ifs at h with hc <;> (obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl)
  | some x =>
    rw [evaluate_get, hs] at h
    split_ifs at h with hc
    · obtain ⟨-, rfl⟩ := h
      exact oracleRunEffect_of_fields _ _ _ rfl rfl
    · obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl


theorem oracleRunEffect_set
    (name : StoreName) (v : Nat) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (h : evaluate ((.set name v : HolProg width), s) = (r, t)) :
    oracleRunEffect (steps ((.set name v : HolProg width), s)) s t := by
  cases hv : getVar v s with
  | none =>
    rw [evaluate_set, hv] at h
    split_ifs at h with hc <;> (obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl)
  | some w =>
    rw [evaluate_set, hv] at h
    split_ifs at h with hc
    · obtain ⟨-, rfl⟩ := h
      exact oracleRunEffect_of_fields _ _ _ rfl rfl
    · obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl


theorem oracleRunEffect_opCurrHeap
    (binop : HolBinop) (v src : Nat) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (h : evaluate ((.opCurrHeap binop v src : HolProg width), s) = (r, t)) :
    oracleRunEffect (steps ((.opCurrHeap binop v src : HolProg width), s)) s t := by
  cases hw : StackSemExpressions.wordExp s (.op binop [.var src, .lookup .currHeap]) with
  | none =>
    rw [evaluate_opCurrHeap, hw] at h
    split_ifs at h with hc <;> (obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl)
  | some w =>
    rw [evaluate_opCurrHeap, hw] at h
    split_ifs at h with hc
    · obtain ⟨-, rfl⟩ := h
      exact oracleRunEffect_of_fields _ _ _ rfl rfl
    · obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl

theorem gc_oracleBitmap (s t : StackSemStateFiniteExact width C F)
    (h : StackSemAllocation.gc s = some t) :
    t.compileOracle = s.compileOracle ∧ t.bitmaps = s.bitmaps := by
  simp only [StackSemAllocation.gc] at h
  split at h
  · simp_all
  · rcases he : StackSem.encStack s.bitmaps (List.drop s.stackSpace s.stack) with _ | roots
    · simp [he] at h
    · rcases hg : s.gcFun (roots, s.memory, s.mdomain, s.store) with _ | ⟨r', mem, st⟩
      · simp [he, hg] at h
      · rcases hd : StackSem.decStack s.bitmaps r' (List.drop s.stackSpace s.stack) with _ | stack'
        · simp [he, hg, hd] at h
        · simp [he, hg, hd] at h
          subst t
          simp

/-- Allocation keeps the oracle and bitmap list. -/
theorem alloc_oracleBitmap (v : BitVec width) (s : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F)
    (run : StackSemAllocation.alloc v s = (result, post)) :
    post.compileOracle = s.compileOracle ∧ post.bitmaps = s.bitmaps := by
  simp only [StackSemAllocation.alloc] at run
  rcases hc : StackSemAllocation.gc (setStore .allocSize (.word v) s) with _ | collected
  · simp [hc] at run
    obtain ⟨-, rfl⟩ := run
    exact ⟨rfl, rfl⟩
  · have hg := gc_oracleBitmap _ _ hc
    simp only [StackSemStateOps.setStore] at hg
    rcases hs : collected.store.lookup .allocSize with _ | amount
    · simp [hc, hs] at run
      obtain ⟨-, rfl⟩ := run
      exact hg
    · rcases hsp : StackSemAllocation.hasSpace amount collected.store with _ | sp
      · simp [hc, hs, hsp] at run
        obtain ⟨-, rfl⟩ := run
        exact hg
      · cases sp
        · simp [hc, hs, hsp] at run
          obtain ⟨-, rfl⟩ := run
          exact hg
        · simp [hc, hs, hsp] at run
          obtain ⟨-, rfl⟩ := run
          exact hg


theorem oracleRunEffect_alloc
    (n : Nat) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (h : evaluate ((.alloc n : HolProg width), s) = (r, t))
    : oracleRunEffect (steps ((.alloc n : HolProg width), s)) s t := by
  cases hv : getVar n s with
  | none =>
    rw [evaluate_alloc] at h
    simp only [hv] at h
    split_ifs at h <;> obtain ⟨-, rfl⟩ := h <;> exact oracleRunEffect_of_fields _ _ _ rfl rfl
  | some v =>
    cases v with
    | loc l o =>
      rw [evaluate_alloc] at h
      simp only [hv] at h
      split_ifs at h <;> obtain ⟨-, rfl⟩ := h <;> exact oracleRunEffect_of_fields _ _ _ rfl rfl
    | word w =>
      rw [evaluate_alloc] at h
      simp only [hv] at h
      split_ifs at h
      · obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
      · have hp := alloc_oracleBitmap w s r t h
        exact oracleRunEffect_of_fields _ _ _ hp.1 hp.2


theorem storeConstSem_oracleBitmap {resultWidth : Nat} [NeZero resultWidth]
    (t1 t2 : Nat) (s t : StackSemStateFiniteExact width C F)
    (h : (StackSemStoreConsts.storeConstSem (resultWidth := resultWidth) t1 t2 s).2 = t) :
    t.compileOracle = s.compileOracle ∧ t.bitmaps = s.bitmaps := by
  rw [← h]
  by_cases hnodup : ¬ [0, 1, 2, 3, t1, t2].Nodup
  · simp [StackSemStoreConsts.storeConstSem, if_pos hnodup]
  · simp only [StackSemStoreConsts.storeConstSem, if_neg hnodup]
    cases h1 : getVar 1 s with
    | none => simp
    | some v1 =>
      cases h2 : getVar 2 s with
      | none => simp
      | some v2 =>
        cases h3 : getVar 3 s with
        | none => simp
        | some v3 =>
          cases v1 with
          | word i =>
            cases v2 with
            | word a =>
              cases v3 with
              | word off =>
                cases hc : StackSemStoreConsts.copyWordsExact i.toNat a off s.bitmaps (fun x => s.mdomain x = true) s.memory with
                | none => simp [hc]
                | some p =>
                  obtain ⟨a', m⟩ := p
                  simp [hc]
                  split <;> exact ⟨rfl, rfl⟩
              | loc l => simp
            | loc l => simp
          | loc l => simp

theorem oracleRunEffect_storeConsts
    (t1 t2 : Nat) (stubOpt : Option Nat) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (h : evaluate ((.storeConsts t1 t2 stubOpt : HolProg width), s) = (r, t))
    : oracleRunEffect (steps ((.storeConsts t1 t2 stubOpt : HolProg width), s)) s t := by
  rw [evaluate_storeConsts] at h
  split_ifs at h
  all_goals try (obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl)
  have hp := storeConstSem_oracleBitmap (resultWidth := width) t1 t2 s t (congrArg Prod.snd h)
  exact oracleRunEffect_of_fields _ _ _ hp.1 hp.2


theorem stackShMemLoad_bitmap (r : Nat) (address : BitVec width)
    (s : StackSemStateFiniteExact width C F) :
    (StackSemShMem.shMemLoad r address s).2.bitmaps = s.bitmaps := by
  simp only [StackSemShMem.shMemLoad]
  split_ifs with hd
  · cases hc : callFFIHOL s.ffi (.sharedMem .mappedRead) [0] (panWordToBytesHOL address false) with
    | final outcome => simp
    | ret newFfi newBytes => simp
  · simp
theorem stackShMemLoadByte_bitmap (r : Nat) (address : BitVec width)
    (s : StackSemStateFiniteExact width C F) :
    (StackSemShMem.shMemLoadByte r address s).2.bitmaps = s.bitmaps := by
  simp only [StackSemShMem.shMemLoadByte]
  split_ifs with hd
  · cases hc : callFFIHOL s.ffi (.sharedMem .mappedRead) [1] (panWordToBytesHOL address false) with
    | final outcome => simp
    | ret newFfi newBytes => simp
  · simp
theorem stackShMemLoad16_bitmap (r : Nat) (address : BitVec width)
    (s : StackSemStateFiniteExact width C F) :
    (StackSemShMem.shMemLoad16 r address s).2.bitmaps = s.bitmaps := by
  simp only [StackSemShMem.shMemLoad16]
  split_ifs with hd
  · cases hc : callFFIHOL s.ffi (.sharedMem .mappedRead) [2] (panWordToBytesHOL address false) with
    | final outcome => simp
    | ret newFfi newBytes => simp
  · simp
theorem stackShMemLoad32_bitmap (r : Nat) (address : BitVec width)
    (s : StackSemStateFiniteExact width C F) :
    (StackSemShMem.shMemLoad32 r address s).2.bitmaps = s.bitmaps := by
  simp only [StackSemShMem.shMemLoad32]
  split_ifs with hd
  · cases hc : callFFIHOL s.ffi (.sharedMem .mappedRead) [4] (panWordToBytesHOL address false) with
    | final outcome => simp
    | ret newFfi newBytes => simp
  · simp
theorem stackShMemStore_bitmap (r : Nat) (address : BitVec width)
    (s : StackSemStateFiniteExact width C F) :
    (StackSemShMem.shMemStore r address s).2.bitmaps = s.bitmaps := by
  cases hv : getVar r s with
  | none => simp [StackSemShMem.shMemStore, hv]
  | some v =>
    cases v with
    | word w =>
      simp only [StackSemShMem.shMemStore, hv]
      split_ifs with hd
      · cases hc : callFFIHOL s.ffi (.sharedMem .mappedWrite) [0] (panWordToBytesHOL w false ++ panWordToBytesHOL address false) with
        | final outcome => simp
        | ret newFfi newBytes => simp
      · simp
    | loc l => simp [StackSemShMem.shMemStore, hv]
theorem stackShMemStoreByte_bitmap (r : Nat) (address : BitVec width)
    (s : StackSemStateFiniteExact width C F) :
    (StackSemShMem.shMemStoreByte r address s).2.bitmaps = s.bitmaps := by
  cases hv : getVar r s with
  | none => simp [StackSemShMem.shMemStoreByte, hv]
  | some v =>
    cases v with
    | word w =>
      simp only [StackSemShMem.shMemStoreByte, hv]
      split_ifs with hd
      · cases hc : callFFIHOL s.ffi (.sharedMem .mappedWrite) [1] ([getByteHOL8 0 w false] ++ panWordToBytesHOL address false) with
        | final outcome => simp
        | ret newFfi newBytes => simp
      · simp
    | loc l => simp [StackSemShMem.shMemStoreByte, hv]
theorem stackShMemStore16_bitmap (r : Nat) (address : BitVec width)
    (s : StackSemStateFiniteExact width C F) :
    (StackSemShMem.shMemStore16 r address s).2.bitmaps = s.bitmaps := by
  cases hv : getVar r s with
  | none => simp [StackSemShMem.shMemStore16, hv]
  | some v =>
    cases v with
    | word w =>
      simp only [StackSemShMem.shMemStore16, hv]
      split_ifs with hd
      · cases hc : callFFIHOL s.ffi (.sharedMem .mappedWrite) [2] ((panWordToBytesHOL w false).take 2 ++ panWordToBytesHOL address false) with
        | final outcome => simp
        | ret newFfi newBytes => simp
      · simp
    | loc l => simp [StackSemShMem.shMemStore16, hv]
theorem stackShMemStore32_bitmap (r : Nat) (address : BitVec width)
    (s : StackSemStateFiniteExact width C F) :
    (StackSemShMem.shMemStore32 r address s).2.bitmaps = s.bitmaps := by
  cases hv : getVar r s with
  | none => simp [StackSemShMem.shMemStore32, hv]
  | some v =>
    cases v with
    | word w =>
      simp only [StackSemShMem.shMemStore32, hv]
      split_ifs with hd
      · cases hc : callFFIHOL s.ffi (.sharedMem .mappedWrite) [4] ((panWordToBytesHOL w false).take 4 ++ panWordToBytesHOL address false) with
        | final outcome => simp
        | ret newFfi newBytes => simp
      · simp
    | loc l => simp [StackSemShMem.shMemStore32, hv]
theorem stackShMemOp_bitmap (op : WordMemOp) (r : Nat) (address : BitVec width)
    (s t : StackSemStateFiniteExact width C F)
    (h : (StackSemShMem.shMemOp op r address s).2 = t) : t.bitmaps = s.bitmaps := by
  rw [← h]
  cases op
  case load => exact stackShMemLoad_bitmap r address s
  case load8 => exact stackShMemLoadByte_bitmap r address s
  case load16 => exact stackShMemLoad16_bitmap r address s
  case load32 => exact stackShMemLoad32_bitmap r address s
  case store => exact stackShMemStore_bitmap r address s
  case store8 => exact stackShMemStoreByte_bitmap r address s
  case store16 => exact stackShMemStore16_bitmap r address s
  case store32 => exact stackShMemStore32_bitmap r address s


theorem oracleRunEffect_shMemOp
    (op : HolMemop) (r0 a : Nat) (w : BitVec width)
    (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.shMemOp op r0 (.addr a w) : HolProg width), s) = (r, t))
    : oracleRunEffect (steps ((.shMemOp op r0 (.addr a w) : HolProg width), s)) s t := by
  cases ha : StackSemExpressions.wordExp s (.op .add [.var a, .const w]) with
  | none =>
    rw [evaluate_shMemOp] at h; simp only [ha] at h
    obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
  | some address =>
    rw [evaluate_shMemOp] at h; simp only [ha] at h
    split_ifs at h
    · obtain ⟨-, rfl⟩ := h
      exact oracleRunEffect_of_fields _ _ _ rfl rfl
    · have hh := congrArg Prod.snd h
      have hb := stackShMemOp_bitmap _ _ _ _ _ hh
      have ho := stackShMemOp_oracle _ _ _ _ _ hh
      exact oracleRunEffect_of_fields _ _ _ ho hb


theorem setVar_bitmapOracle (v : Nat) (x : WordLocW width) (s : StackSemStateFiniteExact width C F) :
    (setVar v x s).bitmaps = s.bitmaps ∧ (setVar v x s).compileOracle = s.compileOracle :=
  ⟨rfl, rfl⟩

/-- Store writes keep `bitmaps` and `compileOracle`. -/
theorem setStore_bitmapOracle (v : WordStoreHOL) (x : WordLocW width)
    (s : StackSemStateFiniteExact width C F) :
    (setStore v x s).bitmaps = s.bitmaps ∧ (setStore v x s).compileOracle = s.compileOracle :=
  ⟨rfl, rfl⟩

/-- FP register writes keep `bitmaps` and `compileOracle`. -/
theorem setFpVar_bitmapOracle (v : Nat) (x : BitVec 64) (s : StackSemStateFiniteExact width C F) :
    (setFpVar v x s).bitmaps = s.bitmaps ∧ (setFpVar v x s).compileOracle = s.compileOracle :=
  ⟨rfl, rfl⟩

/-- `emptyEnv` keeps `bitmaps` and `compileOracle`. -/
theorem emptyEnv_bitmapOracle (s : StackSemStateFiniteExact width C F) :
    (emptyEnv s).bitmaps = s.bitmaps ∧ (emptyEnv s).compileOracle = s.compileOracle :=
  ⟨rfl, rfl⟩

/-- `decClock` keeps `bitmaps` and `compileOracle`. -/
theorem decClock_bitmapOracle (s : StackSemStateFiniteExact width C F) :
    (decClock s).bitmaps = s.bitmaps ∧ (decClock s).compileOracle = s.compileOracle :=
  ⟨rfl, rfl⟩

/-- Memory writes keep `bitmaps` and `compileOracle`. -/
theorem memStore_bitmapOracle (a : BitVec width) (w : WordLocW width)
    (s t : StackSemStateFiniteExact width C F) (h : memStore a w s = some t) :
    t.bitmaps = s.bitmaps ∧ t.compileOracle = s.compileOracle := by
  simp only [StackSemStateOps.memStore] at h
  split at h
  · obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
  · simp at h

/-- Expression assignment keeps `bitmaps` and `compileOracle`. -/
theorem assign_bitmapOracle (reg : Nat) (exp : WordLangExpHOL (BitVec width))
    (s t : StackSemStateFiniteExact width C F)
    (h : StackSemExpressions.assign reg exp s = some t) :
    t.bitmaps = s.bitmaps ∧ t.compileOracle = s.compileOracle := by
  simp only [StackSemExpressions.assign] at h
  split at h
  · simp at h
  · obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩

/-- Int-to-FP conversions keep `bitmaps` and `compileOracle`. -/
theorem fpToInt_bitmapOracle (d1 d2 : Nat) (s t : StackSemStateFiniteExact width C F)
    (h : StackSemFpRegisterInstructions.instFpToInt d1 d2 s = some t) :
    t.bitmaps = s.bitmaps ∧ t.compileOracle = s.compileOracle := by
  simp only [StackSemFpRegisterInstructions.instFpToInt] at h
  cases hg : getFpVar d2 s with
  | none => simp [hg] at h
  | some f =>
    cases hi : holFp64ToInt .roundTiesToEven f with
    | none => simp [hg, hi] at h
    | some i =>
      simp only [hg, hi] at h
      split_ifs at h
      all_goals try (obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩)
      all_goals try (cases hf : getFpVar (d1 / 2) s)
      all_goals try (simp [hf] at h)
      all_goals try (obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩)

/-- FP-to-int conversions keep `bitmaps` and `compileOracle`. -/
theorem fpFromInt_bitmapOracle (d1 d2 : Nat) (s t : StackSemStateFiniteExact width C F)
    (h : StackSemFpRegisterInstructions.instFpFromInt d1 d2 s = some t) :
    t.bitmaps = s.bitmaps ∧ t.compileOracle = s.compileOracle := by
  simp only [StackSemFpRegisterInstructions.instFpFromInt] at h
  split_ifs at h
  all_goals try (cases hg : getFpVar d2 s)
  all_goals try (cases hk : getFpVar (d2 / 2) s)
  all_goals try (simp [hg] at h)
  all_goals try (simp [hk] at h)
  all_goals try (obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩)

theorem mem_bitmapOracle (op : HolMemop) (r a : Nat) (w : BitVec width)
    (s t : StackSemStateFiniteExact width C F)
    (h : StackSemIntegerInstructions.instInteger (.mem op r (.addr a w)) s = some (some t)) :
    t.bitmaps = s.bitmaps ∧ t.compileOracle = s.compileOracle := by
  cases op
  case load =>
    simp only [StackSemIntegerInstructions.instInteger] at h
    cases ha : StackSemExpressions.wordExp s (.op .add [.var a, .const w]) with
    | none => simp [ha] at h
    | some av =>
      cases hm : memLoad av s with
      | none => simp [ha, hm] at h
      | some wv =>
        simp [ha, hm] at h
        subst t
        exact setVar_bitmapOracle _ _ _
  case load8 =>
    simp only [StackSemIntegerInstructions.instInteger] at h
    cases ha : StackSemExpressions.wordExp s (.op .add [.var a, .const w]) with
    | none => simp [ha] at h
    | some av =>
      cases hm : memLoadByteAuxExact s.memory s.mdomain s.be av with
      | none => simp [ha, hm] at h
      | some wv =>
        simp [ha, hm] at h
        subst t
        exact setVar_bitmapOracle _ _ _
  case load16 =>
    simp only [StackSemIntegerInstructions.instInteger] at h
    simp at h
  case load32 =>
    simp only [StackSemIntegerInstructions.instInteger] at h
    cases ha : StackSemExpressions.wordExp s (.op .add [.var a, .const w]) with
    | none => simp [ha] at h
    | some av =>
      cases hm : memLoad32Exact s.memory s.mdomain s.be av with
      | none => simp [ha, hm] at h
      | some wv =>
        simp [ha, hm] at h
        subst t
        exact setVar_bitmapOracle _ _ _
  case store =>
    simp only [StackSemIntegerInstructions.instInteger] at h
    cases ha : StackSemExpressions.wordExp s (.op .add [.var a, .const w]) with
    | none => simp [ha] at h
    | some av =>
      cases hr : getVar r s with
      | none => simp [ha, hr] at h
      | some wv =>
        cases hm : memStore av wv s with
        | none => simp [ha, hr, hm] at h
        | some s1 =>
          simp [ha, hr, hm] at h
          subst t
          exact memStore_bitmapOracle _ _ _ _ hm
  case store8 =>
    simp only [StackSemIntegerInstructions.instInteger] at h
    cases ha : StackSemExpressions.wordExp s (.op .add [.var a, .const w]) with
    | none => simp [ha] at h
    | some av =>
      cases hr : getVar r s with
      | none => simp [ha, hr] at h
      | some wv =>
        cases wv with
        | word ww =>
          cases hm : memStoreByteAuxExact s.memory s.mdomain s.be av (ww.setWidth 8) with
          | none => simp [ha, hr, hm] at h
          | some newM =>
            simp [ha, hr, hm] at h
            subst t
            exact ⟨rfl, rfl⟩
        | loc l => simp [ha, hr] at h
  case store16 =>
    simp only [StackSemIntegerInstructions.instInteger] at h
    simp at h
  case store32 =>
    simp only [StackSemIntegerInstructions.instInteger] at h
    cases ha : StackSemExpressions.wordExp s (.op .add [.var a, .const w]) with
    | none => simp [ha] at h
    | some av =>
      cases hr : getVar r s with
      | none => simp [ha, hr] at h
      | some wv =>
        cases wv with
        | word ww =>
          cases hm : memStore32Exact s.memory s.mdomain s.be av (ww.setWidth 32) with
          | none => simp [ha, hr, hm] at h
          | some newM =>
            simp [ha, hr, hm] at h
            subst t
            exact ⟨rfl, rfl⟩
        | loc l => simp [ha, hr] at h
theorem instHOL_bitmapOracle (i : HolInst width) (s t : StackSemStateFiniteExact width C F)
    (h : StackSemInst.instHOL i s = some t) :
    t.bitmaps = s.bitmaps ∧ t.compileOracle = s.compileOracle := by
  cases i
  case skip =>
    simp [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger] at h ⊢
    rw [← h]; exact ⟨rfl, rfl⟩
  case const dest w =>
    simp [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger] at h
    exact assign_bitmapOracle _ _ _ _ h
  case arith operation =>
    cases operation <;> simp [StackSemInst.instHOL, StackSemIntegerInstructions.instInteger] at h ⊢
    all_goals try (split_ifs at h)
    all_goals try (split at h)
    all_goals try (simp at h)
    all_goals try (exact assign_bitmapOracle _ _ _ _ h)
    all_goals try (obtain ⟨-, h⟩ := h)
    all_goals try (exact setVar_bitmapOracle _ _ _)
    all_goals try (rw [← h]; exact ⟨rfl, rfl⟩)
  case mem op dest addr =>
    simp only [StackSemInst.instHOL] at h
    cases addr with
    | addr a w =>
      cases hi : StackSemIntegerInstructions.instInteger (.mem op dest (.addr a w)) s with
      | none => simp [hi] at h
      | some o =>
        cases o with
        | none => simp [hi] at h
        | some t' =>
          simp [hi] at h
          subst t
          exact mem_bitmapOracle op dest a w s t' hi
  case fp op =>
    cases op <;> simp [StackSemInst.instHOL, StackSemFpInstructions.instFp,
      StackSemFpRegisterInstructions.instFpRegister,
      StackSemFpRegisterInstructions.instFpSqrt] at h ⊢
    all_goals try (split_ifs at h)
    all_goals try (split at h)
    all_goals try (simp at h)
    all_goals try (rw [← h]; exact ⟨rfl, rfl⟩)
    all_goals try (exact fpToInt_bitmapOracle _ _ _ _ h)
    all_goals try (exact fpFromInt_bitmapOracle _ _ _ _ h)

theorem oracleRunEffect_inst
    (i : HolInst width) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.inst i : HolProg width), s) = (r, t))
    : oracleRunEffect (steps ((.inst i : HolProg width), s)) s t := by
  rcases hi : StackSemInst.instHOL i s with _ | ss
  · rw [evaluate_inst, hi] at h; obtain ⟨-, rfl⟩ := h; exact oracleRunEffect_of_fields _ _ _ rfl rfl
  · rw [evaluate_inst, hi] at h; obtain ⟨-, rfl⟩ := h
    have hf := instHOL_bitmapOracle i s _ hi
    exact oracleRunEffect_of_fields _ _ _ hf.2 hf.1


/-- All non-recursive evaluator cases consume at most their single step in oracle entries. -/
theorem oracleRunEffect_leaf (p : HolProg width) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width)) (h : evaluate (p, s) = (r, t))
    (leaf : isRecursive p = false) : oracleRunEffect (steps (p, s)) s t := by
  cases p <;> first
    | exact oracleRunEffect_skip _ _ _ h
    | exact oracleRunEffect_break _ _ _ _ h
    | exact oracleRunEffect_continue _ _ _ _ h
    | exact oracleRunEffect_halt _ _ _ _ h
    | exact oracleRunEffect_tick _ _ _ h
    | exact oracleRunEffect_ret _ _ _ _ h
    | exact oracleRunEffect_raise _ _ _ _ h
    | exact oracleRunEffect_locValue _ _ _ _ _ _ h
    | exact oracleRunEffect_inst _ _ _ _ h
    | exact oracleRunEffect_get _ _ _ _ _ h
    | exact oracleRunEffect_set _ _ _ _ _ h
    | exact oracleRunEffect_opCurrHeap _ _ _ _ _ _ h
    | exact oracleRunEffect_stackAlloc _ _ _ _ h
    | exact oracleRunEffect_stackFree _ _ _ _ h
    | exact oracleRunEffect_stackLoad _ _ _ _ _ h
    | exact oracleRunEffect_stackGetSize _ _ _ _ h
    | exact oracleRunEffect_bitmapLoad _ _ _ _ _ h
    | exact oracleRunEffect_stackStore _ _ _ _ _ h
    | exact oracleRunEffect_stackSetSize _ _ _ _ h
    | exact oracleRunEffect_codeBufferWrite _ _ _ _ _ h
    | exact oracleRunEffect_dataBufferWrite _ _ _ _ _ h
    | exact oracleRunEffect_alloc _ _ _ _ h
    | exact oracleRunEffect_storeConsts _ _ _ _ _ _ h
    | exact oracleRunEffect_stackLoadAny _ _ _ _ _ h
    | exact oracleRunEffect_stackStoreAny _ _ _ _ _ h
    | exact oracleRunEffect_ffi _ _ _ _ _ _ _ _ _ h
    | (simp [isRecursive] at leaf)
  case shMemOp op reg addr =>
    cases addr with
    | addr a w => exact oracleRunEffect_shMemOp op reg a w s t r h
  case install ptr len dptr dlen ret =>
    rw [steps_leaf _ s (by simp [isRecursive])]
    exact oracleRunEffect_install ptr len dptr dlen ret s t r h

end SteppedFlapjack.StackRemoveSteps.CompCorrect
