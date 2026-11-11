import SteppedFlapjack.WordSimpSteps.StackMaximum
import SteppedFlapjack.WordToStackSteps.DirectTailLocal
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.CodeOnlyGrows
open Flapjack Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
namespace SteppedFlapjack.WordSimpSteps
variable {width : Nat} [NeZero width] {C F : Type}
set_option maxHeartbeats 1000000 in
/-- Branch instructions preserve the frame-size table. -/
theorem branch_stackSize_preserved {p : WordLangProgHOL (BitVec width)} (hp : Branch p) :
    ∀ s : WordSemStateFiniteExact width C F, (evaluate p s).2.stackSize = s.stackSize := by
  induction hp with
  | seq ha hb iha ihb =>
    intro s
    rw [evaluate, fix_clock_evaluate]
    rcases h : evaluate _ s with ⟨res,t⟩
    have first := iha s
    rw [h] at first
    cases res with
    | none => simp only; exact (ihb t).trans first
    | some r => exact first
  | ite cmp r ri ha hb iha ihb =>
    intro s
    rw [evaluate]
    cases getVar r s <;> cases getVarImm ri s <;> simp only
    split <;> first | rfl | exact iha s | exact ihb s
  | assign _ _ | inst _ | move _ _ | get _ _ | opCurrHeap _ _ _ | set _ _ | store _ _ | skip | tick | ret _ _ | «break» _ | «continue» _ =>
    intro s
    rw [evaluate]
    repeat (first | split)
    all_goals try rfl
    all_goals try (rename_i h; have hh := instConstFull _ _ _ h; exact hh.2.2.2.2.2.2.2.2.2.2.2.2)
    all_goals try (rename_i h; have hh := memStoreConst _ _ _ _ h; exact hh.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
    all_goals split <;> rfl


open SteppedFlapjack.WordToStackSteps
set_option maxHeartbeats 1000000 in
/-- Call-free, no-install code preserves the maximum stack usage. -/
theorem loopBlock_stackMax {p : WordLangProgHOL (BitVec width)} (hp : LoopBlock p) :
    noInstallSubprogsHOL p = true → ∀ s : WordSemStateFiniteExact width C F, (evaluate p s).2.stackMax = s.stackMax := by
  induction hp with
  | seq ha hb iha ihb =>
    intro ni s
    simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] at ni
    rw [evaluate, fix_clock_evaluate]
    rcases h : evaluate _ s with ⟨res,t⟩
    have first := iha ni.1 s
    rw [h] at first
    cases res with
    | none => simp only; exact (ihb ni.2 t).trans first
    | some r => exact first
  | ite cmp r ri ha hb iha ihb =>
    intro ni s
    simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] at ni
    rw [evaluate]
    cases getVar r s <;> cases getVarImm ri s <;> simp only
    split <;> first | rfl | exact iha ni.1 s | exact ihb ni.2 s
  | loop names exits h ih =>
    intro ni
    exact loop_stackMax names exits (ih ni)
  | install _ _ _ _ _ => simp [noInstallSubprogsHOL,notCreatedSubprogsWithMemOp]
  | inst _ | ret _ _ | move _ _ | opCurrHeap _ _ _ | ffi _ _ _ _ _ _ | set _ _ | codeBufferWrite _ _ | dataBufferWrite _ _ | get _ _ | locValue _ _ | skip | tick | «break» _ | «continue» _ =>
    intro ni s
    rw [evaluate]
    repeat (first | split)
    all_goals try rfl
    all_goals try (rename_i h; have hh := instConstFull _ _ _ h; exact hh.2.2.2.2.2.2.2.2.2.2.2.1)
    all_goals try (split <;> rfl)
    all_goals repeat (first | split)
    all_goals rfl

set_option maxHeartbeats 1000000 in
/-- A tail call preserves a stack limit when its reached callee does.
The callee premise is the inductive hypothesis for nested calls. -/
theorem directTail_stackMax_from_callee (loc size m L arity stackWords : Nat) (args : List Nat)
    (callee : WordLangProgHOL (BitVec width))
    (calleeBound : ∀ (t : WordSemStateFiniteExact width C F) (n : Nat),
      t.stackMax = some n → n ≤ L →
      ∃ n', (evaluate callee t).2.stackMax = some n' ∧ n' ≤ L)
    (s : WordSemStateFiniteExact width C F)
    (lookup : sptLookup loc s.code = some (arity,callee)) (frame : sptLookup loc s.stackSize = some size)
    (argsArity : args.length = arity)
    (stack : wordSemStackSize s.stack = some stackWords) (maximum : s.stackMax = some m)
    (mFits : m ≤ L) (frameFits : stackWords+size ≤ L) :
    ∃ m', (evaluate (.call none (some loc) args none) s).2.stackMax = some m' ∧ m' ≤ L ∧
      (evaluate (.call none (some loc) args none) s).1 ≠ none := by
  cases hv : WordSemStateFiniteExact.getVars args s with
  | none =>
    refine ⟨m,?_,mFits,?_⟩ <;> rw [evaluate] <;> simp [hv,maximum]
  | some values =>
    have len : values.length = arity := (WordSemStateFiniteExact.getVarsLengthLemma args s values hv).trans argsArity
    have found : wordSemFindCode (some loc) values s.code s.stackSize = some (values,callee,some size) := by
      simp [wordSemFindCode,lookup,frame,len]
    by_cases hz : s.clock = 0
    · refine ⟨m,?_,mFits,?_⟩ <;> rw [evaluate] <;> simp [hv,wordSemBadDestArgs,wordSemAddRetLoc,found,hz,flushState,maximum]
    · let env := WordSemStateFiniteExact.callEnv values (some size) (decClock s)
      have init : env.stackMax = some (max m (stackWords+size)) := by
        simp [env,WordSemStateFiniteExact.callEnv,decClock,maximum,stack,wordSemOptionMax,wordSemOptionAdd]
      obtain ⟨n',h,hFits⟩ := calleeBound env (max m (stackWords+size)) init (Nat.max_le.mpr ⟨mFits,frameFits⟩)
      rcases he : evaluate callee env with ⟨result,post⟩
      rw [he] at h
      refine ⟨n',?_,hFits,?_⟩ <;> rw [evaluate]
      · simp only [hv,wordSemBadDestArgs,wordSemAddRetLoc,found,hz,↓reduceDIte,Option.some_ne_none,false_and,decide_false,Bool.false_eq_true,if_false]
        rw [show evaluate callee (WordSemStateFiniteExact.callEnv values (some size) (decClock s)) = (result,post) from he]
        change (if wordSemBadFunReturn result then (some .error,post) else (result,post)).2.stackMax = _
        split <;> exact h
      · simp only [hv,wordSemBadDestArgs,wordSemAddRetLoc,found,hz,↓reduceDIte,Option.some_ne_none,false_and,decide_false,Bool.false_eq_true,if_false]
        rw [show evaluate callee (WordSemStateFiniteExact.callEnv values (some size) (decClock s)) = (result,post) from he]
        change (if wordSemBadFunReturn result then (some .error,post) else (result,post)).1 ≠ none
        cases result with
        | none => simp [wordSemBadFunReturn]
        | some r => split <;> simp

/-- A call-free callee preserves the initial stack limit. -/
theorem directTail_stackMax_bound (loc size m L arity stackWords : Nat) (args : List Nat)
    (callee : WordLangProgHOL (BitVec width))
    (shape : LoopBlock callee) (noInstall : noInstallSubprogsHOL callee = true)
    (s : WordSemStateFiniteExact width C F)
    (lookup : sptLookup loc s.code = some (arity,callee)) (frame : sptLookup loc s.stackSize = some size)
    (argsArity : args.length = arity)
    (stack : wordSemStackSize s.stack = some stackWords) (maximum : s.stackMax = some m)
    (mFits : m ≤ L) (frameFits : stackWords+size ≤ L) :
    ∃ m', (evaluate (.call none (some loc) args none) s).2.stackMax = some m' ∧ m' ≤ L ∧
      (evaluate (.call none (some loc) args none) s).1 ≠ none := by
  apply directTail_stackMax_from_callee loc size m L arity stackWords args callee
    (fun t n maxEq fits => ⟨n,(loopBlock_stackMax shape noInstall t).trans maxEq,fits⟩)
    s lookup frame argsArity stack maximum mFits frameFits

/-- A returning call accounts for its saved caller frame, optional handler
slots, and callee frame in the actual maximum stack usage. -/
theorem pushed_call_frame_usage (s : WordSemStateFiniteExact width C F)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (args : List (WordLocW width)) (callerSize calleeSize stackWords maximum : Nat)
    (caller : s.localsSize = some callerSize) (stack : wordSemStackSize s.stack = some stackWords)
    (maxEq : s.stackMax = some maximum) :
    let slots := if handler.isSome then 3 else 0
    let pushed := pushEnv envs handler s
    let called := callEnv args (some calleeSize) pushed
    wordSemStackSize pushed.stack = some (callerSize + slots + stackWords) ∧
    called.stackMax = some (max maximum (callerSize + slots + stackWords + calleeSize)) := by
  simp only [wordSemStackSize,wordSemStackSizeFrame,wordSemOptionAdd] at stack
  cases handler with
  | none =>
    simp [pushEnv,WordSemStateFiniteExact.callEnv,wordSemStackSize,wordSemStackSizeFrame,wordSemOptionAdd,wordSemOptionMax,caller,maxEq,stack]
  | some h =>
    obtain ⟨v,p,l1,l2⟩ := h
    simp [pushEnv,WordSemStateFiniteExact.callEnv,wordSemStackSize,wordSemStackSizeFrame,wordSemOptionAdd,wordSemOptionMax,caller,maxEq,stack]
    omega

/-- Stack words used by each saved frame, including handler slots. -/
def stackFrameCost (frame : WordSemStackFrame width) : Nat :=
  (wordSemStackSizeFrame frame).getD 0

/-- Exact word count of a stack whose frames have known sizes. -/
def stackWords (stack : List (WordSemStackFrame width)) : Nat :=
  stack.foldr (fun f n => stackFrameCost f + n) 1

/-- Each saved frame has a known size within the program frame maximum. -/
def stackFramesFit (limit : Nat) (stack : List (WordSemStackFrame width)) : Prop :=
  ∀ f ∈ stack, match f with
    | .stackFrame (some n) _ _ _ => n ≤ limit
    | _ => False

/-- A stack of bounded frames has a concrete linear bound in its depth. -/
theorem stackWords_exact_bound (limit : Nat) (stack : List (WordSemStackFrame width))
    (fits : stackFramesFit limit stack) :
    wordSemStackSize stack = some (stackWords stack) ∧
      stackWords stack ≤ 1 + (limit + 3) * stack.length := by
  induction stack with
  | nil => simp [wordSemStackSize, stackWords]
  | cons f fs ih =>
    have hf := fits f (by simp)
    obtain ⟨n, hn, hbound⟩ : ∃ n, wordSemStackSizeFrame f = some n ∧ n ≤ limit + 3 := by
      cases f with
      | stackFrame size nongc gc handler =>
        cases size with
        | none => simp at hf
        | some size =>
          cases handler <;> simp [wordSemStackSizeFrame] at * <;> omega
    have ft : stackFramesFit limit fs := by
      intro g hg
      exact fits g (by simp [hg])
    obtain ⟨heq, hle⟩ := ih ft
    have hs : stackFrameCost f = n := by simp [stackFrameCost, hn]
    constructor
    · change wordSemOptionAdd (wordSemStackSizeFrame f) (wordSemStackSize fs) =
        some (stackFrameCost f + stackWords fs)
      simp [hn, heq, hs, wordSemOptionAdd]
    · simp only [stackWords, List.foldr_cons, hs, List.length_cons, Nat.mul_add, Nat.mul_one]
      change n + stackWords fs ≤ 1 + ((limit + 3) * fs.length + (limit + 3))
      omega

/-- A returning call uses at most one more saved frame and one active frame. -/
theorem pushed_call_depth_bound {C F : Type} (s : WordSemStateFiniteExact width C F)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (args : List (WordLocW width)) (callerSize calleeSize maximum limit : Nat)
    (caller : s.localsSize = some callerSize) (maxEq : s.stackMax = some maximum)
    (callerFits : callerSize ≤ limit) (calleeFits : calleeSize ≤ limit)
    (fits : stackFramesFit limit s.stack) :
    (callEnv args (some calleeSize) (pushEnv envs handler s)).stackMax =
      some (max maximum (callerSize + (if handler.isSome then 3 else 0) +
        stackWords s.stack + calleeSize)) ∧
    callerSize + (if handler.isSome then 3 else 0) + stackWords s.stack + calleeSize ≤
      1 + (limit + 3) * (s.stack.length + 1) + limit := by
  obtain ⟨exactSize,bound⟩ := stackWords_exact_bound limit s.stack fits
  have use := pushed_call_frame_usage s envs handler args callerSize calleeSize
    (stackWords s.stack) maximum caller exactSize maxEq
  refine ⟨use.2, ?_⟩
  cases handler <;> simp [Nat.mul_add] <;> omega

/-- Saving a bounded caller preserves the per-frame stack invariant. -/
theorem stackFramesFit_push (s : WordSemStateFiniteExact width C F)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (callerSize limit : Nat) (caller : s.localsSize = some callerSize)
    (callerFits : callerSize ≤ limit) (fits : stackFramesFit limit s.stack) :
    stackFramesFit limit (pushEnv envs handler s).stack := by
  cases handler with
  | none =>
    simp only [pushEnv, stackFramesFit, List.mem_cons, forall_eq_or_imp]
    constructor
    · simpa [caller] using callerFits
    · exact fits
  | some h =>
    obtain ⟨v,p,l1,l2⟩ := h
    simp only [pushEnv, stackFramesFit, List.mem_cons, forall_eq_or_imp]
    constructor
    · simpa [caller] using callerFits
    · exact fits

/-- Restoring a caller recovers its bounded frame and the stack invariant. -/
theorem stackFramesFit_pop (s t : WordSemStateFiniteExact width C F) (limit : Nat)
    (fits : stackFramesFit limit s.stack) (popped : popEnv s = some t) :
    stackFramesFit limit t.stack ∧ ∃ size, t.localsSize = some size ∧ size ≤ limit := by
  cases hs : s.stack with
  | nil => simp [popEnv, hs] at popped
  | cons frame tail =>
    cases frame with
    | stackFrame size nongc gc handler =>
      have head := fits (.stackFrame size nongc gc handler) (by simp [hs])
      have rest : stackFramesFit limit tail := by
        intro f hf
        exact fits f (by simp [hs,hf])
      cases size with
      | none => simp at head
      | some size =>
        cases handler with
        | none =>
          simp [popEnv, hs] at popped
          subst t
          exact ⟨rest, size, rfl, head⟩
        | some h =>
          obtain ⟨a,b,c⟩ := h
          simp [popEnv, hs] at popped
          subst t
          exact ⟨rest, size, rfl, head⟩

/-- Restoring a caller frame leaves the recorded maximum unchanged. -/
theorem popEnv_stackMax (s t : WordSemStateFiniteExact width C F) (h : popEnv s = some t) : t.stackMax = s.stackMax := by
  unfold popEnv at h
  split at h <;> try contradiction
  all_goals simp only [Option.some.injEq] at h; subst t; rfl

set_option maxHeartbeats 1000000 in
/-- The callee, continuation and handler induction hypotheses bound every returning-call outcome. -/
theorem returningCall_stackMax_from_bounds
    (dest : Option Nat) (args names : List Nat) (cuts : WordLangCutsetsHOL)
    (continuation : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s middle : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (xs values : List (WordLocW width)) (callee : WordLangProgHOL (BitVec width))
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (callerSize calleeSize stackWords maximum limit : Nat)
    (hargs : getVars args s = some xs) (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest (wordSemAddRetLoc (some (names,cuts,continuation,l1,l2)) xs)
      s.code s.stackSize = some (values,callee,some calleeSize))
    (hvalid : ¬ (sptDomainEmpty cuts.1 ∨ ¬ names.Nodup))
    (hcut : wordSemCutEnvs cuts s.locals = some envs) (hclock : s.clock ≠ 0)
    (caller : s.localsSize = some callerSize) (stack : wordSemStackSize s.stack = some stackWords)
    (maxEq : s.stackMax = some maximum) (maxFits : maximum ≤ limit)
    (frameFits : callerSize + (if handler.isSome then 3 else 0) + stackWords + calleeSize ≤ limit)
    (bodyRun : evaluate callee (callEnv values (some calleeSize) (pushEnv envs handler (decClock s))) = (res,middle))
    (bodyIH : ∀ n, (callEnv values (some calleeSize) (pushEnv envs handler (decClock s))).stackMax = some n → n ≤ limit →
      ∃ n', middle.stackMax = some n' ∧ n' ≤ limit)
    (continuationIH : ∀ (t : WordSemStateFiniteExact width C F) n, t.stackMax = some n → n ≤ limit →
      ∃ n', (evaluate continuation t).2.stackMax = some n' ∧ n' ≤ limit)
    (handlerIH : ∀ v p a b, handler = some (v,p,a,b) → ∀ (t : WordSemStateFiniteExact width C F) n,
      t.stackMax = some n → n ≤ limit → ∃ n', (evaluate p t).2.stackMax = some n' ∧ n' ≤ limit) :
    ∃ n', (evaluate (.call (some (names,cuts,continuation,l1,l2)) dest args handler) s).2.stackMax = some n' ∧ n' ≤ limit := by
  have init := pushed_call_frame_usage (decClock s) envs handler values callerSize calleeSize stackWords maximum
    (by simpa [decClock] using caller) (by simpa [decClock] using stack) (by simpa [decClock] using maxEq)
  have bounded : max maximum (callerSize + (if handler.isSome then 3 else 0) + stackWords + calleeSize) ≤ limit := Nat.max_le.mpr ⟨maxFits,frameFits⟩
  obtain ⟨n,hmax,hn⟩ := bodyIH _ init.2 bounded
  rw [evaluate]
  simp only [hargs,hbad,Bool.false_eq_true,if_false,hfind,if_neg hvalid,hcut]
  rw [dif_neg hclock,fix_clock_evaluate,bodyRun]
  cases res with
  | none => exact ⟨n,hmax,hn⟩
  | some r =>
    cases r with
    | result x ys =>
      simp only
      split
      · exact ⟨n,hmax,hn⟩
      · cases hp : popEnv middle with
        | none => exact ⟨n,hmax,hn⟩
        | some restored =>
          simp only
          have hm := popEnv_stackMax middle restored hp
          split
          · apply continuationIH _ n (by simpa [setVars,hm] using hmax) hn
          · exact ⟨n,hm.trans hmax,hn⟩
    | exception x y =>
      simp only
      cases hh : handler with
      | none => exact ⟨n,hmax,hn⟩
      | some h =>
        obtain ⟨v,p,a,b⟩ := h
        simp only
        split
        · exact ⟨n,hmax,hn⟩
        · split
          · exact handlerIH v p a b hh _ n (by simpa [setVar] using hmax) hn
          · exact ⟨n,hmax,hn⟩
    | «break» _ | «continue» _ | error | timeOut | finalFfi _ | notEnoughSpace => exact ⟨n,hmax,hn⟩

/-- Timeout still records the saved caller and callee frame. -/
theorem returningCall_timeout_stackMax
    (dest : Option Nat) (args names : List Nat) (cuts : WordLangCutsetsHOL)
    (continuation : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F)
    (xs values : List (WordLocW width)) (callee : WordLangProgHOL (BitVec width))
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (callerSize calleeSize stackWords maximum : Nat)
    (hargs : getVars args s = some xs) (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest (wordSemAddRetLoc (some (names,cuts,continuation,l1,l2)) xs)
      s.code s.stackSize = some (values,callee,some calleeSize))
    (hvalid : ¬ (sptDomainEmpty cuts.1 ∨ ¬ names.Nodup))
    (hcut : wordSemCutEnvs cuts s.locals = some envs) (hclock : s.clock = 0)
    (caller : s.localsSize = some callerSize) (stack : wordSemStackSize s.stack = some stackWords)
    (maxEq : s.stackMax = some maximum) :
    (evaluate (.call (some (names,cuts,continuation,l1,l2)) dest args handler) s).2.stackMax =
      some (max maximum (callerSize + (if handler.isSome then 3 else 0) + stackWords + calleeSize)) := by
  have init := pushed_call_frame_usage s envs handler values callerSize calleeSize stackWords maximum caller stack maxEq
  rw [evaluate]
  simp only [hargs,hbad,Bool.false_eq_true,if_false,hfind,if_neg hvalid,hcut]
  rw [dif_pos hclock]
  simpa [flushState] using init.2

open SteppedFlapjack.WordAllocSteps
set_option maxHeartbeats 1000000 in
/-- Every reachable callee frame bounds the maximum usage of a tail entry. -/
theorem regTail_stackMax_bound {p : WordLangProgHOL (BitVec width)} (shape : RegTailShape p) :
  ∀ (s : WordSemStateFiniteExact width C F) (m L : Nat),
    wordSemStackSize s.stack = some 1 → s.stackMax = some m → m ≤ L → WordProps.noInstallCode s.code →
    (∀ loc, RegTailCalls p loc → ∃ arity callee size, sptLookup loc s.code = some (arity,callee) ∧
      LoopBlock callee ∧ sptLookup loc s.stackSize = some size ∧ 1+size ≤ L) →
    ∃ m', (evaluate p s).2.stackMax = some m' ∧ m' ≤ L ∧
      ((evaluate p s).1 = none → (evaluate p s).2.stackSize = s.stackSize) := by
  induction shape with
  | branch h =>
    intro s m L stack maximum fits noCode code
    exact ⟨m,(branch_stackMax h s).trans maximum,fits,fun _ => branch_stackSize_preserved h s⟩
  | call loc reg =>
    intro s m L stack maximum fits noCode code
    obtain ⟨arity,callee,size,lookup,calleeShape,frame,frameFits⟩ := code loc (.call loc reg)
    by_cases arityOne : arity = 1
    · subst arity
      have noInstall := noCode loc 1 callee lookup
      obtain ⟨m',max',bound,notNone⟩ := directTail_stackMax_bound loc size m L 1 1 [reg] callee calleeShape noInstall s lookup frame rfl stack maximum fits frameFits
      exact ⟨m',max',bound,fun h => False.elim (notNone h)⟩
    · cases hvar : getVar reg s with
      | none =>
        refine ⟨m,?_,fits,?_⟩ <;> rw [evaluate] <;> simp [WordSemStateFiniteExact.getVars,hvar,maximum]
      | some value =>
        have found : wordSemFindCode (some loc) [value] s.code s.stackSize = none := by
          simp [wordSemFindCode,lookup,Ne.symm arityOne]
        refine ⟨m,?_,fits,?_⟩ <;> rw [evaluate] <;> simp [WordSemStateFiniteExact.getVars,hvar,wordSemBadDestArgs,wordSemAddRetLoc,found,maximum]

  | @seq a b ha hb iha ihb =>
    intro s m L stack maximum fits noCode code
    have codeA := fun loc h => code loc (.left h)
    have codeB := fun loc h => code loc (.right h)
    obtain ⟨ma,maxA,boundA,sizeA⟩ := iha s m L stack maximum fits noCode codeA
    rw [evaluate,fix_clock_evaluate]
    rcases run : evaluate a s with ⟨result,mid⟩
    rw [run] at maxA sizeA
    cases result with
    | some r => exact ⟨ma,maxA,boundA,by simp⟩
    | none =>
      have sizeEq : mid.stackSize = s.stackSize := sizeA rfl
      have stackEq := WordSemStackEq.evaluate_NONE_stack_size_const a s mid run
      have codeEq : mid.code = s.code := by
        have h := WordSemStateFiniteExact.code_evaluate a s (regTail_noInstall ha) noCode
        rw [run] at h
        exact h
      have bCode : ∀ loc, RegTailCalls b loc → ∃ arity callee size, sptLookup loc mid.code = some (arity,callee) ∧
          LoopBlock callee ∧ sptLookup loc mid.stackSize = some size ∧ 1+size ≤ L := by
        intro loc call
        simpa only [codeEq,sizeEq] using codeB loc call
      obtain ⟨mb,maxB,boundB,sizeB⟩ := ihb mid ma L (stackEq.trans stack) maxA boundA
        (by simpa only [codeEq] using noCode) bCode
      refine ⟨mb,maxB,boundB,?_⟩
      intro hn
      exact (sizeB hn).trans sizeEq
end SteppedFlapjack.WordSimpSteps
