import SteppedFlapjack.StackRemoveSteps.CodeOrigin
/-! Code-tree preservation for non-install leaf instructions. -/

namespace SteppedFlapjack.StackRemoveSteps.CompCorrect
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.StackSemStateOps Flapjack.StackSemControl Flapjack.StackSemEvaluate
open Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.StackSteps
variable {width : Nat} [NeZero width] {C F : Type}
theorem leafCode_skip
    (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.skip : HolProg width), s) = (r, t))
    : t.code = s.code := by
  rw [evaluate_skip] at h
  obtain ⟨-, rfl⟩ := h
  rfl


theorem leafCode_break
    (n : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.break n : HolProg width), s) = (r, t))
    : t.code = s.code := by
  rw [evaluate_break] at h
  obtain ⟨-, rfl⟩ := h
  rfl


theorem leafCode_continue
    (n : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.continue n : HolProg width), s) = (r, t))
    : t.code = s.code := by
  rw [evaluate_continue] at h
  obtain ⟨-, rfl⟩ := h
  rfl


theorem leafCode_halt
    (v : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.halt v : HolProg width), s) = (r, t))
    : t.code = s.code := by
  cases hv : getVar v s with
  | none => rw [evaluate_halt, hv] at h; obtain ⟨-, rfl⟩ := h; rfl
  | some w =>
    rw [evaluate_halt, hv] at h; obtain ⟨-, rfl⟩ := h
    exact (emptyEnv_code s).1


theorem leafCode_tick
    (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.tick : HolProg width), s) = (r, t))
    : t.code = s.code := by
  rw [evaluate_tick] at h
  split_ifs at h with hc
  · obtain ⟨-, rfl⟩ := h
    exact (emptyEnv_code s).1
  · obtain ⟨-, rfl⟩ := h
    exact (decClock_code s).1

theorem leafCode_ret
    (n : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.ret n : HolProg width), s) = (r, t))
    : t.code = s.code := by
  cases hv : getVar n s with
  | none => rw [evaluate_ret, hv] at h; obtain ⟨-, rfl⟩ := h; rfl
  | some w =>
    cases w with
    | loc l1 l2 => rw [evaluate_ret, hv] at h; obtain ⟨-, rfl⟩ := h; rfl
    | word w => rw [evaluate_ret, hv] at h; obtain ⟨-, rfl⟩ := h; rfl


theorem leafCode_raise
    (n : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.raise n : HolProg width), s) = (r, t))
    : t.code = s.code := by
  cases hv : getVar n s with
  | none => rw [evaluate_raise, hv] at h; obtain ⟨-, rfl⟩ := h; rfl
  | some w =>
    cases w with
    | loc l1 l2 => rw [evaluate_raise, hv] at h; obtain ⟨-, rfl⟩ := h; rfl
    | word w => rw [evaluate_raise, hv] at h; obtain ⟨-, rfl⟩ := h; rfl


theorem leafCode_locValue
    (r0 l1 l2 : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.locValue r0 l1 l2 : HolProg width), s) = (r, t))
    : t.code = s.code := by
  rw [evaluate_locValue] at h
  split_ifs at h with hc
  · obtain ⟨-, rfl⟩ := h
    exact (setVar_code _ _ _).1
  · obtain ⟨-, rfl⟩ := h; rfl


theorem leafCode_inst
    (i : HolInst width) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.inst i : HolProg width), s) = (r, t))
    : t.code = s.code := by
  rcases hi : StackSemInst.instHOL i s with _ | ss
  · rw [evaluate_inst, hi] at h; obtain ⟨-, rfl⟩ := h; rfl
  · rw [evaluate_inst, hi] at h; obtain ⟨-, rfl⟩ := h
    exact (instHOL_code i s _ hi).1


theorem leafCode_get
    (v : Nat) (name : StoreName) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (h : evaluate ((.get v name : HolProg width), s) = (r, t))
    : t.code = s.code := by
  cases hs : s.store.lookup (StackSemRegisterTransfers.storeOfSyntax name) with
  | none =>
    rw [evaluate_get, hs] at h
    split_ifs at h with hc <;> (obtain ⟨-, rfl⟩ := h; rfl)
  | some x =>
    rw [evaluate_get, hs] at h
    split_ifs at h with hc
    · obtain ⟨-, rfl⟩ := h
      exact (setVar_code _ _ _).1
    · obtain ⟨-, rfl⟩ := h; rfl


theorem leafCode_set
    (name : StoreName) (v : Nat) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (h : evaluate ((.set name v : HolProg width), s) = (r, t))
    : t.code = s.code := by
  cases hv : getVar v s with
  | none =>
    rw [evaluate_set, hv] at h
    split_ifs at h with hc <;> (obtain ⟨-, rfl⟩ := h; rfl)
  | some w =>
    rw [evaluate_set, hv] at h
    split_ifs at h with hc
    · obtain ⟨-, rfl⟩ := h
      exact (setStore_code _ _ _).1
    · obtain ⟨-, rfl⟩ := h; rfl


theorem leafCode_opCurrHeap
    (binop : HolBinop) (v src : Nat) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (h : evaluate ((.opCurrHeap binop v src : HolProg width), s) = (r, t))
    : t.code = s.code := by
  cases hw : StackSemExpressions.wordExp s (.op binop [.var src, .lookup .currHeap]) with
  | none =>
    rw [evaluate_opCurrHeap, hw] at h
    split_ifs at h with hc <;> (obtain ⟨-, rfl⟩ := h; rfl)
  | some w =>
    rw [evaluate_opCurrHeap, hw] at h
    split_ifs at h with hc
    · obtain ⟨-, rfl⟩ := h
      exact (setVar_code _ _ _).1
    · obtain ⟨-, rfl⟩ := h; rfl

theorem leafCode_stackAlloc
    (n : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.stackAlloc n : HolProg width), s) = (r, t))
    : t.code = s.code := by
  rw [evaluate_stackAlloc] at h
  split_ifs at h with hc
  · obtain ⟨-, rfl⟩ := h; rfl
  · obtain ⟨-, rfl⟩ := h
    exact (emptyEnv_code s).1
  · obtain ⟨-, rfl⟩ := h
    rfl


theorem leafCode_stackFree
    (n : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.stackFree n : HolProg width), s) = (r, t))
    : t.code = s.code := by
  rw [evaluate_stackFree] at h
  split_ifs at h with hc
  · obtain ⟨-, rfl⟩ := h; rfl
  · obtain ⟨-, rfl⟩ := h
    exact (emptyEnv_code s).1
  · obtain ⟨-, rfl⟩ := h
    rfl


theorem leafCode_stackLoad
    (r0 n : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.stackLoad r0 n : HolProg width), s) = (r, t))
    : t.code = s.code := by
  rw [evaluate_stackLoad] at h
  split_ifs at h with hc
  · obtain ⟨-, rfl⟩ := h; rfl
  · obtain ⟨-, rfl⟩ := h
    exact (setVar_code _ _ _).1
  · obtain ⟨-, rfl⟩ := h
    exact (emptyEnv_code s).1


theorem leafCode_stackGetSize
    (r0 : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.stackGetSize r0 : HolProg width), s) = (r, t))
    : t.code = s.code := by
  rw [evaluate_stackGetSize] at h
  split_ifs at h with hc
  · obtain ⟨-, rfl⟩ := h; rfl
  · obtain ⟨-, rfl⟩ := h
    exact (setVar_code _ _ _).1


theorem leafCode_bitmapLoad
    (r0 v : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.bitmapLoad r0 v : HolProg width), s) = (r, t))
    : t.code = s.code := by
  rw [evaluate_bitmapLoad] at h
  split_ifs at h with hc
  · obtain ⟨-, rfl⟩ := h; rfl
  · cases hv : getVar v s with
    | none => simp only [hv] at h; obtain ⟨-, rfl⟩ := h; rfl
    | some w =>
      cases w
      case loc l1 l2 => simp only [hv] at h; obtain ⟨-, rfl⟩ := h; rfl
      case word wd =>
        simp only [hv] at h
        split_ifs at h with hc
        · obtain ⟨-, rfl⟩ := h; rfl
        · obtain ⟨-, rfl⟩ := h
          exact (setVar_code _ _ _).1

theorem leafCode_stackStore
    (r0 n : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.stackStore r0 n : HolProg width), s) = (r, t))
    : t.code = s.code := by
  rw [evaluate_stackStore] at h
  split_ifs at h with hc
  · obtain ⟨-, rfl⟩ := h; rfl
  · obtain ⟨-, rfl⟩ := h
    exact (emptyEnv_code s).1
  · cases hv : getVar r0 s
    case none =>
      simp only [hv] at h; obtain ⟨-, rfl⟩ := h
      exact (emptyEnv_code s).1
    case some val =>
      simp only [hv] at h; obtain ⟨-, rfl⟩ := h
      rfl


theorem leafCode_stackSetSize
    (r0 : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.stackSetSize r0 : HolProg width), s) = (r, t))
    : t.code = s.code := by
  rw [evaluate_stackSetSize] at h
  split_ifs at h with hc
  · obtain ⟨-, rfl⟩ := h; rfl
  · cases hv : getVar r0 s
    case none =>
      simp only [hv] at h; obtain ⟨-, rfl⟩ := h; rfl
    case some val =>
      cases val
      case loc l1 l2 => simp only [hv] at h; obtain ⟨-, rfl⟩ := h; rfl
      case word wd =>
        simp only [hv] at h
        split_ifs at h with hc
        · obtain ⟨-, rfl⟩ := h
          exact (emptyEnv_code s).1
        · obtain ⟨-, rfl⟩ := h
          exact (setVar_code _ _ _).1

theorem leafCode_codeBufferWrite
    (r1 r2 : Nat) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (h : evaluate ((.codeBufferWrite r1 r2 : HolProg width), s) = (r, t))
    : t.code = s.code := by
  have hp : t.code = s.code ∧ t.compileOracle = s.compileOracle := by
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
  exact hp.1

theorem leafCode_dataBufferWrite
    (r1 r2 : Nat) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (h : evaluate ((.dataBufferWrite r1 r2 : HolProg width), s) = (r, t))
    : t.code = s.code := by
  by_cases hs : ¬ s.useStack
  · rw [evaluate_dataBufferWrite] at h
    simp only [if_pos hs] at h
    obtain ⟨-, rfl⟩ := h
    rfl
  · have hp : t.code = s.code ∧ t.compileOracle = s.compileOracle := by
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
    exact hp.1

theorem leafCode_alloc
    (n : Nat) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (h : evaluate ((.alloc n : HolProg width), s) = (r, t))
    : t.code = s.code := by
  cases hv : getVar n s with
  | none =>
    rw [evaluate_alloc] at h
    simp only [hv] at h
    split_ifs at h <;> obtain ⟨-, rfl⟩ := h <;> rfl
  | some v =>
    cases v with
    | loc l o =>
      rw [evaluate_alloc] at h
      simp only [hv] at h
      split_ifs at h <;> obtain ⟨-, rfl⟩ := h <;> rfl
    | word w =>
      rw [evaluate_alloc] at h
      simp only [hv] at h
      split_ifs at h
      · obtain ⟨-, rfl⟩ := h; rfl
      · have hp := alloc_code w s r t h
        exact hp.1


theorem leafCode_storeConsts
    (t1 t2 : Nat) (stubOpt : Option Nat) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width))
    (h : evaluate ((.storeConsts t1 t2 stubOpt : HolProg width), s) = (r, t))
    : t.code = s.code := by
  rw [evaluate_storeConsts] at h
  split_ifs at h
  all_goals try (obtain ⟨-, rfl⟩ := h; rfl)
  have hp := storeConstSem_code (resultWidth := width) t1 t2 s t (congrArg Prod.snd h)
  exact hp.1


theorem leafCode_stackLoadAny
    (r0 rn : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.stackLoadAny r0 rn : HolProg width), s) = (r, t))
    : t.code = s.code := by
  cases hv : getVar rn s with
  | none =>
    rw [evaluate_stackLoadAny] at h; simp only [hv] at h
    split_ifs at h
    · obtain ⟨-, rfl⟩ := h; rfl
    · obtain ⟨-, rfl⟩ := h
      exact (emptyEnv_code s).1
  | some v =>
    cases v with
    | loc l o =>
      rw [evaluate_stackLoadAny] at h; simp only [hv] at h
      split_ifs at h
      · obtain ⟨-, rfl⟩ := h; rfl
      · obtain ⟨-, rfl⟩ := h
        exact (emptyEnv_code s).1
    | word w =>
      rw [evaluate_stackLoadAny] at h; simp only [hv] at h
      split_ifs at h
      · obtain ⟨-, rfl⟩ := h; rfl
      · obtain ⟨-, rfl⟩ := h
        exact (setVar_code _ _ _).1
      · obtain ⟨-, rfl⟩ := h
        exact (emptyEnv_code s).1


theorem leafCode_stackStoreAny
    (r0 rn : Nat) (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.stackStoreAny r0 rn : HolProg width), s) = (r, t))
    : t.code = s.code := by
  cases h1 : getVar r0 s with
  | none =>
    rw [evaluate_stackStoreAny] at h; simp only [h1] at h
    split_ifs at h
    · obtain ⟨-, rfl⟩ := h; rfl
    · obtain ⟨-, rfl⟩ := h
      exact (emptyEnv_code s).1
  | some value =>
    cases h2 : getVar rn s with
    | none =>
      rw [evaluate_stackStoreAny] at h; simp only [h1, h2] at h
      split_ifs at h
      · obtain ⟨-, rfl⟩ := h; rfl
      · obtain ⟨-, rfl⟩ := h
        exact (emptyEnv_code s).1
    | some v =>
      cases v with
      | loc l o =>
        rw [evaluate_stackStoreAny] at h; simp only [h1, h2] at h
        split_ifs at h
        · obtain ⟨-, rfl⟩ := h; rfl
        · obtain ⟨-, rfl⟩ := h
          exact (emptyEnv_code s).1
      | word w =>
        rw [evaluate_stackStoreAny] at h; simp only [h1, h2] at h
        split_ifs at h
        · obtain ⟨-, rfl⟩ := h; rfl
        · obtain ⟨-, rfl⟩ := h; rfl
        · obtain ⟨-, rfl⟩ := h
          exact (emptyEnv_code s).1


theorem leafCode_shMemOp
    (op : HolMemop) (r0 a : Nat) (w : BitVec width)
    (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.shMemOp op r0 (.addr a w) : HolProg width), s) = (r, t))
    : t.code = s.code := by
  cases ha : StackSemExpressions.wordExp s (.op .add [.var a, .const w]) with
  | none =>
    rw [evaluate_shMemOp] at h; simp only [ha] at h
    obtain ⟨-, rfl⟩ := h; rfl
  | some address =>
    rw [evaluate_shMemOp] at h; simp only [ha] at h
    split_ifs at h
    · obtain ⟨-, rfl⟩ := h
      exact (emptyEnv_code s).1
    · have hh := congrArg Prod.snd h
      have hc := stackShMemOp_code _ _ _ _ _ hh
      exact hc.trans (decClock_code s).1


theorem leafCode_ffi
    (ffiIndex : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat)
    (s t : StackSemStateFiniteExact width C F) (r : Option (StackSemResult width))
    (h : evaluate ((.ffi ffiIndex ptr len ptr2 len2 ret : HolProg width), s) = (r, t))
    : t.code = s.code := by
  cases h1 : getVar len s with
  | none =>
    rw [evaluate_ffi] at h; simp only [h1] at h
    obtain ⟨-, rfl⟩ := h; rfl
  | some v1 =>
    cases v1 with
    | loc l o =>
      rw [evaluate_ffi] at h; simp only [h1] at h
      obtain ⟨-, rfl⟩ := h; rfl
    | word w1 =>
      cases h2 : getVar ptr s with
      | none =>
        rw [evaluate_ffi] at h; simp only [h1, h2] at h
        obtain ⟨-, rfl⟩ := h; rfl
      | some v2 =>
        cases v2 with
        | loc l o =>
          rw [evaluate_ffi] at h; simp only [h1, h2] at h
          obtain ⟨-, rfl⟩ := h; rfl
        | word w2 =>
          cases h3 : getVar len2 s with
          | none =>
            rw [evaluate_ffi] at h; simp only [h1, h2, h3] at h
            obtain ⟨-, rfl⟩ := h; rfl
          | some v3 =>
            cases v3 with
            | loc l o =>
              rw [evaluate_ffi] at h; simp only [h1, h2, h3] at h
              obtain ⟨-, rfl⟩ := h; rfl
            | word w3 =>
              cases h4 : getVar ptr2 s with
              | none =>
                rw [evaluate_ffi] at h; simp only [h1, h2, h3, h4] at h
                obtain ⟨-, rfl⟩ := h; rfl
              | some v4 =>
                cases v4 with
                | loc l o =>
                  rw [evaluate_ffi] at h; simp only [h1, h2, h3, h4] at h
                  obtain ⟨-, rfl⟩ := h; rfl
                | word w4 =>
                  rw [evaluate_ffi] at h; simp only [h1, h2, h3, h4] at h
                  cases hb1 : readBytearrayWordHOL w2 w1.toNat (memLoadByteAuxExact s.memory s.mdomain s.be) with
                  | none =>
                    simp only [hb1] at h; obtain ⟨-, rfl⟩ := h; rfl
                  | some bytes =>
                    cases hb2 : readBytearrayWordHOL w4 w3.toNat (memLoadByteAuxExact s.memory s.mdomain s.be) with
                    | none =>
                      simp only [hb1, hb2] at h; obtain ⟨-, rfl⟩ := h; rfl
                    | some bytes2 =>
                      cases hf : callFFIHOL s.ffi (.extCall ffiIndex) bytes bytes2 with
                      | final outcome =>
                        simp only [hb1, hb2, hf] at h; obtain ⟨-, rfl⟩ := h; rfl
                      | ret newFfi newBytes =>
                        simp only [hb1, hb2, hf] at h; obtain ⟨-, rfl⟩ := h
                        rfl


/-- A non-recursive instruction other than install leaves the code tree unchanged. -/
theorem leafCode_preserved (p : HolProg width) (s t : StackSemStateFiniteExact width C F)
    (r : Option (StackSemResult width)) (h : evaluate (p, s) = (r, t))
    (leaf : isRecursive p = false)
    (notInstall : ∀ ptr len dptr dlen ret, p ≠ .install ptr len dptr dlen ret) :
    t.code = s.code := by
  cases p <;> first
    | exact leafCode_skip _ _ _ h
    | exact leafCode_break _ _ _ _ h
    | exact leafCode_continue _ _ _ _ h
    | exact leafCode_halt _ _ _ _ h
    | exact leafCode_tick _ _ _ h
    | exact leafCode_ret _ _ _ _ h
    | exact leafCode_raise _ _ _ _ h
    | exact leafCode_locValue _ _ _ _ _ _ h
    | exact leafCode_inst _ _ _ _ h
    | exact leafCode_get _ _ _ _ _ h
    | exact leafCode_set _ _ _ _ _ h
    | exact leafCode_opCurrHeap _ _ _ _ _ _ h
    | exact leafCode_stackAlloc _ _ _ _ h
    | exact leafCode_stackFree _ _ _ _ h
    | exact leafCode_stackLoad _ _ _ _ _ h
    | exact leafCode_stackGetSize _ _ _ _ h
    | exact leafCode_bitmapLoad _ _ _ _ _ h
    | exact leafCode_stackStore _ _ _ _ _ h
    | exact leafCode_stackSetSize _ _ _ _ h
    | exact leafCode_codeBufferWrite _ _ _ _ _ h
    | exact leafCode_dataBufferWrite _ _ _ _ _ h
    | exact leafCode_alloc _ _ _ _ h
    | exact leafCode_storeConsts _ _ _ _ _ _ h
    | exact leafCode_stackLoadAny _ _ _ _ _ h
    | exact leafCode_stackStoreAny _ _ _ _ _ h
    | exact leafCode_ffi _ _ _ _ _ _ _ _ _ h
    | (simp [isRecursive] at leaf)
  case shMemOp op reg addr =>
    cases addr with
    | addr a w => exact leafCode_shMemOp op reg a w s t r h
  case install ptr len dptr dlen ret =>
    exact (notInstall ptr len dptr dlen ret rfl).elim

end SteppedFlapjack.StackRemoveSteps.CompCorrect
