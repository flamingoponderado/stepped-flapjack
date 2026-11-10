import SteppedFlapjack.WordToStackSteps.TailCallSteps

/-! Structural bounds for StackSem returning calls. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.StackSteps SteppedFlapjack.StackAllocSteps
variable {width : Nat} [NeZero width]

def handlerCost (k : Nat) (handler : Option (HolProg width × Nat × Nat)) : Nat :=
  match handler with | none => 0 | some (p, _, _) => linearLoopCost k p

/-- One returning target call costs its callee plus at most one continuation.
All bounds are structural and use a common upper bound on the initial clock. -/
theorem targetReturningCall_bound {C F : Type} (ret : HolProg width) (link l1 l2 : Nat)
    (dest : Sum Nat Nat) (handler : Option (HolProg width × Nat × Nat)) (k : Nat)
    (s : StackSemStateFiniteExact width C F) (clockBound : s.clock ≤ k)
    (codeShape : ∀ label p, sptLookup label s.code = some p → loopOnly p = true)
    (retShape : loopOnly ret = true)
    (handlerShape : ∀ p a b, handler = some (p, a, b) → loopOnly p = true) :
    steps (.call (some (ret, link, l1, l2)) dest handler, s) ≤
      1 + loopCodeCost k s.code + linearLoopCost k ret + handlerCost k handler := by
  rw [steps_call_some]
  cases found : findCode dest (s.regs.eraseEq link) s.code with
  | none => simp [handlerCost]; omega
  | some callee =>
    by_cases zero : s.clock = 0
    · simp [zero, handlerCost]; omega
    · simp only [zero, if_false, StackSemEvaluateClock.fixClockEvaluate]
      have ⟨label, lookup⟩ := findCode_entry dest {s with regs := s.regs.eraseEq link} callee found
      have calleeCost := linearLoopCostBound k callee (codeShape label callee lookup)
        (decClock (setVar link (.loc l1 l2) s)) (by simp only [decClock, setVar]; omega)
      have maxCost := loopCodeCost_bound k s.code label callee lookup
      rcases run : evaluate (callee, decClock (setVar link (.loc l1 l2) s)) with ⟨res, post⟩
      have postClock := StackSemEvaluateClock.evaluateClock callee _ res post run
      have postBound : post.clock ≤ k := by simp only [decClock, setVar] at postClock; omega
      have returnCost := linearLoopCostBound k ret retShape post postBound
      cases res with
      | none => simp [handlerCost]; omega
      | some res =>
        cases res <;> simp only
        all_goals try { simp [handlerCost]; omega }
        case result x =>
          by_cases hx : x = .loc l1 l2 <;> simp [hx, handlerCost] <;> omega
        case exception x =>
          cases handler with
          | none => simp [handlerCost]; omega
          | some h =>
            obtain ⟨hp, a, b⟩ := h
            have cost := linearLoopCostBound k hp (handlerShape hp a b rfl) post postBound
            by_cases hx : x = .loc a b <;> simp [handlerCost, hx] <;> omega


/-- The generated return-value copying code contains no calls or loops. -/
theorem loopOnly_copyRetAux (k f n : Nat) : loopOnly (copyRetAuxNative (width := width) k f n) = true := by
  induction n with
  | zero => rfl
  | succ n ih => simp [copyRetAuxNative, listSeq, loopOnly, ih]

theorem loopOnly_seqStackFree (n : Nat) (p : HolProg width) (hp : loopOnly p = true) :
    loopOnly (seqStackFreeNative n p) = true := by
  simp only [seqStackFreeNative]
  split <;> simp [loopOnly, hp]

/-- Return-value copying preserves call-free continuation shape. -/
theorem loopOnly_copyRet {β γ : Type} (perf isHandle : Bool) (kf : Nat × Nat × γ)
    (vs : List β) (p : HolProg width) (hp : loopOnly p = true) :
    loopOnly (copyRetNative perf isHandle kf vs p) = true := by
  simp only [copyRetNative]
  split
  · exact hp
  · simp only [loopOnly, Bool.and_eq_true]
    exact ⟨loopOnly_copyRetAux _ _ _, loopOnly_seqStackFree _ _ hp⟩

theorem loopOnly_popHandler {β γ : Type} (perf : Bool) (kf : Nat × β × γ)
    (p : HolProg width) (hp : loopOnly p = true) : loopOnly (popHandlerNative perf kf p) = true := by
  simp [popHandlerNative, loopOnly, hp]

theorem loopOnly_stackMove (n start offset r : Nat) (p : HolProg width) (hp : loopOnly p = true) :
    loopOnly (stackMoveNative n start offset r p) = true := by
  induction n generalizing start with
  | zero => exact hp
  | succ n ih => simp [stackMoveNative, loopOnly, ih]

theorem loopOnly_stackArgs {α β : Type} (dest : Sum α β) (count : Nat) (kf : Nat × Nat × Nat) :
    loopOnly (stackArgsNative (width := width) dest count kf) = true := by
  exact loopOnly_stackMove _ _ _ _ _ rfl

theorem loopOnly_wLive (live : Spt Unit × Spt Unit) (bs : AppList (BitVec width) × Nat)
    (kf : Nat × Nat × Nat) : loopOnly (wLiveNative live bs kf).1 = true := by
  simp only [wLiveNative]
  split <;> rfl

theorem loopOnly_pushHandler (a b : Nat) (kf : Nat × Nat × Nat) :
    loopOnly (pushHandlerNative (width := width) false a b kf) = true := by
  rfl

theorem loopOnly_handlerArgs (dest : Sum Nat Nat) (count : Nat) (kf : Nat × Nat × Nat) :
    loopOnly (stackHandlerArgsNative (width := width) false dest count kf) = true := by
  exact loopOnly_stackArgs dest count _


/-- The source-code fragment and original compiler relation establish the
callee code shape required by the returning-call target bound. -/
theorem relatedReturningCall_bound {C F : Type} (ac : AsmConfigExact width)
    (regCount frame stackFrame : Nat) (lens : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) (target : StackSemStateFiniteExact width C F)
    (related : Flapjack.WordToStackProofs.stateRel ac regCount frame stackFrame source target lens 0)
    (code : ∀ label arity prog, sptLookup label source.code = some (arity, prog) → LoopBlock prog)
    (ret : HolProg width) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat)) (clock : Nat) (clockBound : target.clock ≤ clock)
    (retShape : loopOnly ret = true)
    (handlerShape : ∀ p a b, handler = some (p, a, b) → loopOnly p = true) :
    steps (.call (some (ret, link, l1, l2)) dest handler, target) ≤
      1 + loopCodeCost clock target.code + linearLoopCost clock ret + handlerCost clock handler :=
  targetReturningCall_bound ret link l1 l2 dest handler clock target clockBound
    (relatedLoopCode ac regCount frame stackFrame source target lens related code) retShape handlerShape


/-- The native return wrapper around a compiled loop-block continuation is
itself loop-only, both with and without handler-frame restoration. -/
theorem generatedReturn_loopOnly (ac : AsmConfigExact width) (p : WordLangProgHOL (BitVec width))
    (block : LoopBlock p) (bs : AppList (BitVec width) × Nat) (kf : Nat × Nat × Nat)
    (values : List Nat) (hasHandler : Bool) :
    loopOnly (.seq .skip (copyRetNative false hasHandler kf values
      (if hasHandler then popHandlerNative false kf (compNative ac false p bs kf).1
       else (compNative ac false p bs kf).1))) = true := by
  have body := loopWord_compiled ac p (loopBlock_loop block) bs kf
  simp only [loopOnly, Bool.true_and]
  apply loopOnly_copyRet
  cases hasHandler with
  | false => exact body
  | true => exact loopOnly_popHandler false kf _ body

end SteppedFlapjack.WordToStackSteps
