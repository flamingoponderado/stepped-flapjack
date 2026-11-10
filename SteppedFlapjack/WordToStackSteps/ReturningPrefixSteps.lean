import SteppedFlapjack.WordToStackSteps.ReturningTargetSteps

/-! Prefix composition for compiled returning calls. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.StackSemControl
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open SteppedFlapjack.StackSteps SteppedFlapjack.StackAllocSteps
variable {width : Nat} [NeZero width]

/-- Setup nodes used by call lowering cannot install or call code. -/
def setupOnly : HolProg width → Bool
  | .seq a b => setupOnly a && setupOnly b
  | .skip | .stackAlloc _ | .stackLoad _ _ | .stackStore _ _ | .stackGetSize _
  | .stackFree _ | .get _ _ | .set _ _ | .locValue _ _ _ | .inst _ => true
  | _ => false

theorem setupOnly_loopOnly (p : HolProg width) (hp : setupOnly p = true) : loopOnly p = true := by
  cases h : p <;> simp_all [setupOnly, loopOnly]
  case seq a b => exact ⟨setupOnly_loopOnly a hp.1, setupOnly_loopOnly b hp.2⟩
termination_by sizeOf p
decreasing_by all_goals subst p; simp_wf <;> omega

/-- Executing call setup preserves the exact target code tree. -/
theorem setupOnly_code {C F : Type} (p : HolProg width) (hp : setupOnly p = true)
    (s post : StackSemStateFiniteExact width C F) (res : Option (StackSemResult width))
    (run : evaluate (p, s) = (res, post)) : post.code = s.code := by
  cases h : p <;> simp_all only [setupOnly, Bool.and_eq_true, Bool.false_eq_true]
  case seq a b =>
    rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate] at run
    rcases he : evaluate (a, s) with ⟨r, mid⟩
    have ha := setupOnly_code a hp.1 s mid r he
    rw [he] at run
    cases r with
    | none => exact (setupOnly_code b hp.2 mid post res run).trans ha
    | some r => simp only [Prod.mk.injEq] at run; obtain ⟨_, rfl⟩ := run; exact ha
  case inst i =>
    rw [evaluate_inst] at run
    split at run
    · rename_i next primitive
      simp only [Prod.mk.injEq] at run
      obtain ⟨_, rfl⟩ := run
      obtain ⟨_, _, _, _, _, sameCode, _, _, _, _, _, _, _⟩ :=
        StackPropsInstructionConstants.instConst i s next primitive
      exact sameCode
    · simp only [Prod.mk.injEq] at run
      obtain ⟨_, rfl⟩ := run
      rfl
  all_goals
    first
    | rw [evaluate_skip] at run
    | rw [evaluate_stackAlloc] at run
    | rw [evaluate_stackFree] at run
    | rw [evaluate_stackLoad] at run
    | rw [evaluate_stackStore] at run
    | rw [evaluate_stackGetSize] at run
    | rw [evaluate_get] at run
    | rw [evaluate_set] at run
    | rw [evaluate_locValue] at run
  all_goals
    repeat' split at run
  all_goals
    have hc := congrArg (fun x => x.2.code) run
    exact hc.symm
termination_by sizeOf p
decreasing_by all_goals subst p; simp_wf <;> omega


/-- A setup block followed by a returning call has a structural bound that
includes both the setup and all possible callee/continuation outcomes. -/
theorem setupReturning_bound {C F : Type} (setup ret : HolProg width)
    (link l1 l2 : Nat) (dest : Sum Nat Nat) (handler : Option (HolProg width × Nat × Nat))
    (k : Nat) (s : StackSemStateFiniteExact width C F) (clockBound : s.clock ≤ k)
    (setupShape : setupOnly setup = true)
    (codeShape : ∀ label p, sptLookup label s.code = some p → loopOnly p = true)
    (retShape : loopOnly ret = true)
    (handlerShape : ∀ p a b, handler = some (p, a, b) → loopOnly p = true) :
    steps (.seq setup (.call (some (ret, link, l1, l2)) dest handler), s) ≤
      2 + linearLoopCost k setup + loopCodeCost k s.code + linearLoopCost k ret + handlerCost k handler := by
  have setupCost := linearLoopCostBound k setup (setupOnly_loopOnly setup setupShape) s clockBound
  rw [steps_seq, StackSemEvaluateClock.fixClockEvaluate]
  rcases run : evaluate (setup, s) with ⟨res, post⟩
  cases res with
  | some _ => simp only; omega
  | none =>
    have sameCode := setupOnly_code setup setupShape s post none run
    have postClock := StackSemEvaluateClock.evaluateClock setup s none post run
    have postBound : post.clock ≤ k := postClock.trans clockBound
    have postShape : ∀ label p, sptLookup label post.code = some p → loopOnly p = true := by
      simpa only [sameCode] using codeShape
    have callCost := targetReturningCall_bound ret link l1 l2 dest handler k post postBound postShape retShape handlerShape
    simp only [sameCode] at callCost
    simp only
    omega

/-- The destination setup produced by the native compiler belongs to the
code-preserving setup fragment. -/
theorem setupOnly_stackLoad (loads : List (Nat × Nat)) (p : HolProg width)
    (hp : setupOnly p = true) : setupOnly (wStackLoadNative loads p) = true := by
  induction loads with
  | nil => exact hp
  | cons pair rest ih => cases pair; simp [wStackLoadNative, setupOnly, ih]

theorem setupOnly_callDest (dest : Option Nat) (args : List Nat) (kf : Nat × Nat × Nat) :
    setupOnly (callDestNative (width := width) dest args kf).1 = true := by
  cases dest with
  | some _ => rfl
  | none =>
    simp only [callDestNative]
    split
    · rfl
    · apply setupOnly_stackLoad; rfl

theorem setupOnly_stackMove (n start offset r : Nat) (p : HolProg width) (hp : setupOnly p = true) :
    setupOnly (stackMoveNative n start offset r p) = true := by
  induction n generalizing start with
  | zero => exact hp
  | succ n ih => simp [stackMoveNative, setupOnly, ih]

theorem setupOnly_stackArgs {α β : Type} (dest : Sum α β) (count : Nat) (kf : Nat × Nat × Nat) :
    setupOnly (stackArgsNative (width := width) dest count kf) = true := by
  exact setupOnly_stackMove _ _ _ _ _ rfl

theorem setupOnly_wLive (live : Spt Unit × Spt Unit) (bs : AppList (BitVec width) × Nat)
    (kf : Nat × Nat × Nat) : setupOnly (wLiveNative live bs kf).1 = true := by
  simp only [wLiveNative]
  split <;> rfl

theorem setupOnly_pushHandler (a b : Nat) (kf : Nat × Nat × Nat) :
    setupOnly (pushHandlerNative (width := width) false a b kf) = true := by
  rfl

theorem setupOnly_handlerArgs (dest : Sum Nat Nat) (count : Nat) (kf : Nat × Nat × Nat) :
    setupOnly (stackHandlerArgsNative (width := width) false dest count kf) = true := by
  exact setupOnly_stackArgs dest count _


/-- A right-associated sequence of code-preserving setup blocks ending in a
single call. -/
inductive SetupWrap (call : HolProg width) : HolProg width → Prop
  | done : SetupWrap call call
  | step {prep rest} : setupOnly prep = true → SetupWrap call rest → SetupWrap call (.seq prep rest)

def setupChainCost (k : Nat) : HolProg width → Nat
  | .seq a b => 1 + linearLoopCost k a + setupChainCost k b
  | _ => 0

/-- Every generated setup chain preserves the code bound until the call and
adds its own computable structural execution cost. -/
theorem setupChainReturning_bound {C F : Type} (ret : HolProg width) (link l1 l2 : Nat)
    (dest : Sum Nat Nat) (handler : Option (HolProg width × Nat × Nat)) (program : HolProg width)
    (chain : SetupWrap (.call (some (ret, link, l1, l2)) dest handler) program)
    (k : Nat) (s : StackSemStateFiniteExact width C F) (clockBound : s.clock ≤ k)
    (codeShape : ∀ label p, sptLookup label s.code = some p → loopOnly p = true)
    (retShape : loopOnly ret = true)
    (handlerShape : ∀ p a b, handler = some (p, a, b) → loopOnly p = true) :
    steps (program, s) ≤ setupChainCost k program + 1 + loopCodeCost k s.code +
      linearLoopCost k ret + handlerCost k handler := by
  induction chain generalizing s with
  | done =>
    have h := targetReturningCall_bound ret link l1 l2 dest handler k s clockBound codeShape retShape handlerShape
    simpa [setupChainCost] using h
  | @step prep rest shape chain ih =>
    have prepCost := linearLoopCostBound k prep (setupOnly_loopOnly prep shape) s clockBound
    rw [steps_seq, StackSemEvaluateClock.fixClockEvaluate]
    rcases run : evaluate (prep, s) with ⟨res, post⟩
    cases res with
    | some _ => simp only [setupChainCost]; omega
    | none =>
      have sameCode := setupOnly_code prep shape s post none run
      have postClock := StackSemEvaluateClock.evaluateClock prep s none post run
      have postShape : ∀ label p, sptLookup label post.code = some p → loopOnly p = true := by
        simpa only [sameCode] using codeShape
      have bound := ih post (postClock.trans clockBound) postShape
      simp only [sameCode] at bound
      simp only [setupChainCost]
      omega


/-- Computable target cost of a right-associated call-setup chain. -/
def returningChainCost (k : Nat) (code : Spt (HolProg width)) : HolProg width → Nat
  | .seq a b => 1 + linearLoopCost k a + returningChainCost k code b
  | .call (some (ret, _, _, _)) _ handler =>
      1 + loopCodeCost k code + linearLoopCost k ret + handlerCost k handler
  | _ => 0

theorem setupChain_cost (ret : HolProg width) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat)) (program : HolProg width)
    (chain : SetupWrap (.call (some (ret, link, l1, l2)) dest handler) program)
    (k : Nat) (code : Spt (HolProg width)) :
    returningChainCost k code program = setupChainCost k program + 1 + loopCodeCost k code +
      linearLoopCost k ret + handlerCost k handler := by
  induction chain with
  | done => simp [returningChainCost, setupChainCost]
  | step hs chain ih => simp only [returningChainCost, setupChainCost, ih]; omega

theorem setupChainReturning_cost {C F : Type} (ret : HolProg width) (link l1 l2 : Nat)
    (dest : Sum Nat Nat) (handler : Option (HolProg width × Nat × Nat)) (program : HolProg width)
    (chain : SetupWrap (.call (some (ret, link, l1, l2)) dest handler) program)
    (k : Nat) (s : StackSemStateFiniteExact width C F) (clockBound : s.clock ≤ k)
    (codeShape : ∀ label p, sptLookup label s.code = some p → loopOnly p = true)
    (retShape : loopOnly ret = true)
    (handlerShape : ∀ p a b, handler = some (p, a, b) → loopOnly p = true) :
    steps (program, s) ≤ returningChainCost k s.code program := by
  rw [setupChain_cost ret link l1 l2 dest handler program chain k s.code]
  exact setupChainReturning_bound ret link l1 l2 dest handler program chain k s clockBound codeShape retShape handlerShape


/-- The actual native returning-call compiler output has a computable target
step bound whenever the callee code and generated continuations are loop-only. -/
theorem compiledReturning_bound {C F : Type} (ac : AsmConfigExact width)
    (values : List Nat) (live : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec width))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (bs : AppList (BitVec width) × Nat) (kf : Nat × Nat × Nat)
    (s : StackSemStateFiniteExact width C F)
    (codeShape : ∀ label p, sptLookup label s.code = some p → loopOnly p = true)
    (retShape : loopWord retCode = true)
    (handlerShape : ∀ v p a b, handler = some (v, p, a, b) → loopWord p = true) :
    steps ((compNative ac false (.call (some (values, live, retCode, l1, l2)) dest args handler) bs kf).1, s) ≤
      returningChainCost s.clock s.code
        (compNative ac false (.call (some (values, live, retCode, l1, l2)) dest args handler) bs kf).1 := by
  rcases hcd : callDestNative (width := width) dest args kf with ⟨q0, destination⟩
  have q0Shape : setupOnly q0 = true := by
    simpa only [hcd] using setupOnly_callDest (width := width) dest args kf
  rcases hlive : wLiveNative live bs kf with ⟨q1, b1⟩
  have q1Shape : setupOnly q1 = true := by
    simpa only [hlive] using setupOnly_wLive live bs kf
  rcases hret : compNative ac false retCode b1 kf with ⟨q2, b2⟩
  have q2Shape : loopOnly q2 = true := by
    simpa only [hret] using loopWord_compiled ac retCode retShape b1 kf
  cases handler with
  | none =>
    let q3 := (.seq .skip (copyRetNative false false kf values q2) : HolProg width)
    let call := (.call (some (q3, 0, l1, l2)) destination none : HolProg width)
    let program := (.seq q0 (.seq q1 (.seq (stackArgsNative destination (args.length + 1) kf) (.seq .skip call))) : HolProg width)
    have chain : SetupWrap call program := .step q0Shape (.step q1Shape (.step (setupOnly_stackArgs destination _ kf) (.step rfl .done)))
    have q3Shape : loopOnly q3 = true := by
      dsimp [q3]
      simp only [loopOnly, Bool.true_and]
      exact loopOnly_copyRet false false kf values q2 q2Shape
    have bound := setupChainReturning_cost q3 0 l1 l2 destination none program chain s.clock s (Nat.le_refl _) codeShape q3Shape (by simp)
    simpa only [compNative, hcd, hlive, hret, Bool.false_eq_true, if_false, q3, call, program] using bound
  | some h =>
    obtain ⟨v, hprog, h1, h2⟩ := h
    have hpShape : loopWord hprog = true := handlerShape v hprog h1 h2 rfl
    rcases hhandler : compNative ac false hprog b2 kf with ⟨q4, b3⟩
    have q4Shape : loopOnly q4 = true := by
      simpa only [hhandler] using loopWord_compiled ac hprog hpShape b2 kf
    let q3 := (.seq .skip (copyRetNative false true kf values (popHandlerNative false kf q2)) : HolProg width)
    let call := (.call (some (q3, 0, l1, l2)) destination (some (q4, h1, h2)) : HolProg width)
    let program := (.seq q0 (.seq q1 (.seq (pushHandlerNative false h1 h2 kf)
      (.seq (stackHandlerArgsNative false destination (args.length + 1) kf) (.seq .skip call)))) : HolProg width)
    have chain : SetupWrap call program := .step q0Shape (.step q1Shape
      (.step (setupOnly_pushHandler h1 h2 kf) (.step (setupOnly_handlerArgs destination _ kf) (.step rfl .done))))
    have q3Shape : loopOnly q3 = true := by
      dsimp [q3]
      simp only [loopOnly, Bool.true_and]
      exact loopOnly_copyRet false true kf values _ (loopOnly_popHandler false kf q2 q2Shape)
    have handlers : ∀ p a b, some (q4, h1, h2) = some (p, a, b) → loopOnly p = true := by
      intro p a b eq
      cases eq
      exact q4Shape
    have bound := setupChainReturning_cost q3 0 l1 l2 destination (some (q4, h1, h2)) program chain s.clock s (Nat.le_refl _) codeShape q3Shape handlers
    simpa only [compNative, hcd, hlive, hret, hhandler, Bool.false_eq_true, if_false, q3, call, program] using bound


/-- For related states, source loop-block code and continuations discharge all
shape conditions of the actual compiled returning-call bound. -/
theorem compiledReturning_related_bound {C F : Type} (ac : AsmConfigExact width)
    (values : List Nat) (live : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec width))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (bs : AppList (BitVec width) × Nat) (k f frame : Nat) (lens : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) (target : StackSemStateFiniteExact width C F)
    (related : Flapjack.WordToStackProofs.stateRel ac k f frame source target lens 0)
    (code : ∀ label arity p, sptLookup label source.code = some (arity, p) → LoopBlock p)
    (retBlock : LoopBlock retCode)
    (handlerBlock : ∀ v p a b, handler = some (v, p, a, b) → LoopBlock p) :
    steps ((compNative ac false (.call (some (values, live, retCode, l1, l2)) dest args handler) bs (k, f, frame)).1, target) ≤
      returningChainCost source.clock target.code
        (compNative ac false (.call (some (values, live, retCode, l1, l2)) dest args handler) bs (k, f, frame)).1 := by
  have shape := relatedLoopCode ac k f frame source target lens related code
  have handlerShape : ∀ v p a b, handler = some (v, p, a, b) → loopWord p = true := by
    intro v p a b h
    exact loopBlock_loop (handlerBlock v p a b h)
  have bound := compiledReturning_bound ac values live retCode l1 l2 dest args handler bs (k, f, frame) target shape
    (loopBlock_loop retBlock) handlerShape
  have clocks : source.clock = target.clock := related.1
  rw [clocks]
  exact bound

end SteppedFlapjack.WordToStackSteps
