import SteppedFlapjack.LoopLiveSteps.TailEntryBound

/-! Code-table preservation for successful direct-tail-entry prefixes. -/
namespace SteppedFlapjack.LoopLiveSteps
open Flapjack Flapjack.LoopSemStateFiniteExact
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.LoopSteps
variable {width : Nat} [NeZero width] {F : Type}

/-- A result cut never changes the Loop code table. -/
theorem cutRes_code (live : NumSet) (res : Option (LoopResultExact width))
    (s : LoopSemStateFiniteExact width F) : (cutRes live (res,s)).2.code = s.code := by
  cases res with
  | some r => rfl
  | none =>
    by_cases h : sptSubsetLive live s.locals <;> by_cases hc : s.clock = 0 <;> simp [cutRes,cutState,h,hc,decClock]

/-- A loop-free branch preserves the code table. -/
theorem branch_code {p : HolLoopProg width} (shape : LoopBranch p)
    (s post : LoopSemStateFiniteExact width F) (res : Option (LoopResultExact width))
    (run : evaluate p s = (res,post)) : post.code = s.code := by
  induction shape generalizing s post res with
  | skip | tick | assign _ _ | store _ _ | setGlobal _ _ | ret _ | «break» _ | «continue» _ =>
    all_goals rw [evaluate] at run
    all_goals repeat' first | split at run | cases run
    all_goals simp_all [setVar,setGlobals,decClock,memStore,LoopSemStateFiniteExact.callEnv]
    all_goals aesop
  | @seq a b ha hb iha ihb =>
    rw [evaluate_seq] at run
    rcases first : evaluate a s with ⟨out,middle⟩
    rw [first] at run
    have h1 := iha s middle out first
    cases out with
    | none =>
      simp only at run
      exact (ihb middle post res run).trans h1
    | some r =>
      simp only [Prod.mk.injEq] at run
      obtain ⟨_,rfl⟩ := run
      exact h1
  | @mark p hp ih =>
    have inner : evaluate p s = (res,post) := by simpa only [evaluate] using run
    exact ih s post res inner
  | @ite cmp r ri live a b ha hb iha ihb =>
    simp only [evaluate] at run
    rcases hx : sptLookup r s.locals with _ | (x | ⟨_,_⟩) <;>
      rcases hy : getVarImm ri s with _ | (y | ⟨_,_⟩) <;> simp only [hx,hy] at run <;>
      try (cases run; rfl)
    by_cases hcmp : Flapjack.Compiler.Encoders.Asm.wordCmpHOL cmp x y = true
    · simp only [hcmp,if_true] at run
      rcases branch : evaluate a s with ⟨br,mid⟩
      have hc := cutRes_code live br mid
      have hb := iha s mid br branch
      rw [branch] at run
      have hp : (cutRes live (br,mid)).2 = post := congrArg Prod.snd run
      rw [hp] at hc
      exact hc.trans hb
    · simp only [hcmp,Bool.false_eq_true,if_false] at run
      rcases branch : evaluate b s with ⟨br,mid⟩
      have hc := cutRes_code live br mid
      have hb := ihb s mid br branch
      rw [branch] at run
      have hp : (cutRes live (br,mid)).2 = post := congrArg Prod.snd run
      rw [hp] at hc
      exact hc.trans hb

/-- Any entry prefix that continues preserves its code table, since it cannot
have reached a tail call. -/
theorem tailEntry_none_code {p : HolLoopProg width} (shape : TailEntryShape p)
    (s post : LoopSemStateFiniteExact width F) (run : evaluate p s = (none,post)) : post.code = s.code := by
  induction shape generalizing s post with
  | branch h => exact branch_code h s post none run
  | call loc => exact ((directTail_ne_none loc s) (by rw [run])).elim
  | @seq a b ha hb iha ihb =>
    rw [evaluate_seq] at run
    rcases first : evaluate a s with ⟨out,middle⟩
    rw [first] at run
    cases out with
    | none => simp only at run; exact (ihb middle post run).trans (iha s middle first)
    | some r => simp only [Prod.mk.injEq,Option.some_ne_none] at run; exact run.1.elim
  | @mark p hp ih =>
    have inner : evaluate p s = (none,post) := by simpa only [evaluate] using run
    exact ih s post inner

end SteppedFlapjack.LoopLiveSteps
