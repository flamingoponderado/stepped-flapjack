import SteppedFlapjack.LoopLiveSteps.ShrinkBranch
import SteppedFlapjack.LoopLiveSteps.TailEntryShape

/-! Kernel-computable liveness for the branch bodies of supported loops. -/
namespace SteppedFlapjack.LoopLiveSteps
open Flapjack SteppedFlapjack.LoopToWordSteps
variable {width : Nat} [NeZero width]

/-- Structural branch evaluator; outside the supported branch fragment its
result is immaterial. -/
def shrinkBranch (lt : List (NumSet × NumSet)) : HolLoopProg width → NumSet → HolLoopProg width × NumSet
  | .seq p q, live =>
      let (q, live) := shrinkBranch lt q live
      let (p, live) := shrinkBranch lt p live
      (.seq p q, live)
  | .ite cmp r ri p q ls, live =>
      let live := sptInter live ls
      let (p, lp) := shrinkBranch lt p live
      let (q, lq) := shrinkBranch lt q live
      let lr := match ri with | .reg r => sptInsert r () .ln | _ => .ln
      (.ite cmp r ri p q live, sptInsert r () (sptUnion lr (sptUnion lp lq)))
  | .mark p, live => shrinkBranch lt p live
  | .break n, _ => (.break n, match sptOel n lt with | some (_, brk) => brk | none => .ln)
  | .continue n, _ => (.continue n, match sptOel n lt with | some (cont, _) => cont | none => .ln)
  | .skip, live => (.skip,live)
  | .tick, live => (.tick,live)
  | .return vs, _ => (.return vs,sptListInsert vs .ln)
  | .raise v, _ => (.raise v,sptInsert v () .ln)
  | .assign n x, live =>
      match sptLookup n live with
      | none => (.skip,live)
      | some _ => (.assign n x,varsOfExpHOL x (sptDelete n live))
  | .store e n, live => (.store e n,varsOfExpHOL e (sptInsert n () live))
  | .setGlobal n e, live => (.setGlobal n e,varsOfExpHOL e live)
  | p, live => (p,live)

/-- The structural computation agrees with the original liveness pass on
all supported branch bodies, including their resulting live sets. -/
theorem shrinkBranch_eq {p : HolLoopProg width} (shape : LoopBranch p) :
    ∀ lt live, shrinkBranch lt p live = shrinkHOL lt p live := by
  induction shape with
  | skip | tick | assign _ _ | store _ _ | setGlobal _ _ | ret _ | «break» _ | «continue» _ =>
      intro lt live
      simp only [shrinkBranch,shrinkHOL] <;> rfl
  | @seq a b ha hb iha ihb =>
      intro lt live
      simp only [shrinkBranch,shrinkHOL,iha,ihb]
  | mark h ih => intro lt live; simp only [shrinkBranch,shrinkHOL,ih]
  | ite cmp r ri ls ha hb iha ihb =>
      intro lt live
      cases ri <;> simp only [shrinkBranch,shrinkHOL,iha,ihb]

/-- The original fixed-point iteration, with a visible recursion bound and
structural shrinking of its supported branch body. -/
def fixedpointBranch : Nat → List (NumSet × NumSet) → NumSet → NumSet → NumSet →
    HolLoopProg width → Option (HolLoopProg width × NumSet)
  | 0, _, _, _, _, _ => none
  | fuel+1, lt, liveIn, l1, l2, body =>
      let (b,l0) := shrinkBranch ((sptInter liveIn l1,l2)::lt) body l2
      if sptInter liveIn l0 = l1 then some (b,l0)
      else if sptSize (sptInter liveIn l0) ≤ sptSize l1 then none
      else fixedpointBranch fuel lt liveIn (sptInter liveIn l0) l2 body

/-- The number of iterations is bounded by the size of the loop live-in set.
This equality contains no assumption about termination or a successful result. -/
theorem fixedpointBranch_eq {body : HolLoopProg width} (shape : LoopBranch body)
    (fuel : Nat) (lt : List (NumSet × NumSet)) (liveIn l1 l2 : NumSet)
    (enough : sptSize liveIn - sptSize l1 < fuel) :
    fixedpointBranch fuel lt liveIn l1 l2 body = fixedpointHOL lt liveIn l1 l2 body := by
  induction fuel generalizing l1 with
  | zero => omega
  | succ fuel ih =>
    rw [fixedpointBranch, fixedpointHOL, shrinkBranch_eq shape]
    rcases h : shrinkHOL ((sptInter liveIn l1,l2)::lt) body l2 with ⟨b,l0⟩
    simp only
    split
    · rfl
    · split
      · rfl
      · rename_i stable progress
        apply ih
        have bound := sptSize_inter_le liveIn l0
        omega

/-- The actual fixed point is computable with one more iteration than the
number of live-in variables. -/
theorem fixedpointBranch_complete {body : HolLoopProg width} (shape : LoopBranch body)
    (lt : List (NumSet × NumSet)) (liveIn l1 l2 : NumSet) :
    fixedpointBranch (sptSize liveIn + 1) lt liveIn l1 l2 body =
      fixedpointHOL lt liveIn l1 l2 body := by
  apply fixedpointBranch_eq shape
  omega

/-- Executable shrinking for sequences of loops with branch-shaped bodies. -/
def shrinkSequence (lt : List (NumSet × NumSet)) :
    HolLoopProg width → NumSet → HolLoopProg width × NumSet
  | .seq p q, live =>
      let (q,live) := shrinkSequence lt q live
      let (p,live) := shrinkSequence lt p live
      (.seq p q,live)
  | .loop liveIn body liveOut, live =>
      let l2 := sptInter liveOut live
      let bex := sptUnion liveIn l2
      match fixedpointBranch (sptSize liveIn + 1) lt liveIn .ln bex body with
      | some (body,l0) =>
          let l := sptInter liveIn l0
          (.loop l body l2,l)
      | none =>
          let (body,_) := shrinkBranch ((liveIn,l2)::lt) body bex
          (.loop liveIn body l2,liveIn)
  | .mark p, live => shrinkSequence lt p live
  | .call none dest args _, live =>
      (.call none dest args none,sptUnion (sptFromAList (args.map fun x => (x,()))) live)
  | .call (some (names,callLive)) dest args none, live =>
      let after := sptListDelete names (sptInter live callLive)
      (.call (some (names,after)) dest args none,
        sptUnion (sptFromAList (args.map fun x => (x,()))) after)
  | .call (some (names,callLive)) dest args (some (exception,handler,normal,liveOut)), live =>
      let (normal', normalLive) := shrinkBranch lt normal live
      let (handler', handlerLive) := shrinkBranch lt handler live
      let before := sptInter callLive (sptUnion (sptListDelete names normalLive) (sptDelete exception handlerLive))
      (.call (some (names,before)) dest args (some (exception,handler',normal',sptInter live liveOut)),
        sptUnion (sptFromAList (args.map fun x => (x,()))) before)
  | p, live => shrinkBranch lt p live

/-- A returning call without a handler is computed exactly by the structural pass. -/
theorem shrinkSequence_returningCall_noHandler (lt : List (NumSet × NumSet))
    (names : List Nat) (callLive : NumSet) (dest : Option Nat) (args : List Nat)
    (live : NumSet) :
    shrinkSequence lt (.call (some (names,callLive)) dest args none : HolLoopProg width) live =
      shrinkHOL lt (.call (some (names,callLive)) dest args none : HolLoopProg width) live := by
  simp [shrinkSequence,shrinkHOL]

/-- The structural evaluator agrees with the real pass for a returning call
whose compiler-generated continuations raise or skip. -/
theorem shrinkSequence_returningCall (lt : List (NumSet × NumSet))
    (names : List Nat) (callLive : NumSet) (dest : Option Nat) (args : List Nat)
    (exception : Nat) (liveOut live : NumSet) :
    shrinkSequence lt (.call (some (names,callLive)) dest args
      (some (exception,.raise exception,.skip,liveOut)) : HolLoopProg width) live =
    shrinkHOL lt (.call (some (names,callLive)) dest args
      (some (exception,.raise exception,.skip,liveOut)) : HolLoopProg width) live := by
  simp [shrinkSequence,shrinkBranch,shrinkHOL]

/-- Sequence shrinking agrees with branch shrinking on loop-free programs. -/
theorem shrinkSequence_branch {p : HolLoopProg width} (shape : LoopBranch p) :
    ∀ lt live, shrinkSequence lt p live = shrinkBranch lt p live := by
  induction shape with
  | skip | tick | assign _ _ | store _ _ | setGlobal _ _ | ret _ | «break» _ | «continue» _ | ite _ _ _ _ _ _ _ _ =>
      intro lt live
      rfl
  | @seq a b ha hb iha ihb =>
      intro lt live
      simp only [shrinkSequence,shrinkBranch,iha,ihb]
  | mark h ih => intro lt live; simp only [shrinkSequence,shrinkBranch,ih]

/-- Inputs handled by the structural liveness computation: branch code,
loops with branch bodies, and direct calls with the compiler-generated handler. -/
inductive SimpleLoopSequenceSource {width : Nat} [NeZero width] : HolLoopProg width → Prop
  | branch {p} : LoopBranch p → SimpleLoopSequenceSource p
  | loop (live exits) {body} : LoopBranch body → SimpleLoopSequenceSource (.loop live body exits)
  | tail (loc : Nat) (args : List Nat) : SimpleLoopSequenceSource (.call none (some loc) args none)
  | returning (names : List Nat) (callLive : NumSet) (loc exception : Nat) (args : List Nat) (liveOut : NumSet) :
      SimpleLoopSequenceSource (.call (some (names,callLive)) (some loc) args
        (some (exception,.raise exception,.skip,liveOut)))
  | returningMarked (names : List Nat) (callLive : NumSet) (loc exception : Nat) (args : List Nat) (liveOut : NumSet) :
      SimpleLoopSequenceSource (.call (some (names,callLive)) (some loc) args
        (some (exception,.mark (.raise exception),.mark .skip,liveOut)))
  | seq {a b} : SimpleLoopSequenceSource a → SimpleLoopSequenceSource b → SimpleLoopSequenceSource (.seq a b)
  | mark {p} : SimpleLoopSequenceSource p → SimpleLoopSequenceSource (.mark p)

/-- Direct calls are preserved by the real call-target propagation pass. -/
theorem loopCall_simpleSequence {p : HolLoopProg width} (shape : SimpleLoopSequenceSource p) :
    ∀ env, (loopCallCompHOL env p).1 = p := by
  induction shape with
  | branch h => exact loopCall_branch h
  | loop live exits h => exact loopCall_sequence (.loop live exits h)
  | tail loc args => intro env; simp [loopCallCompHOL]
  | returning names callLive loc exception args liveOut => intro env; simp [loopCallCompHOL]
  | returningMarked names callLive loc exception args liveOut => intro env; simp [loopCallCompHOL]
  | @seq a b ha hb iha ihb =>
    intro env
    simp only [loopCallCompHOL]
    rw [iha env,ihb (loopCallCompHOL env a).2]
  | mark h ih => intro env; simp only [loopCallCompHOL,ih]

/-- The executable sequence pass returns exactly the original program and
live set for the supported nonnested-loop fragment. -/
theorem shrinkSequence_eq {p : HolLoopProg width} (shape : SimpleLoopSequenceSource p) :
    ∀ lt live, shrinkSequence lt p live = shrinkHOL lt p live := by
  induction shape with
  | branch h =>
      intro lt live
      rw [shrinkSequence_branch h,shrinkBranch_eq h]
  | @seq a b ha hb iha ihb =>
      intro lt live
      simp only [shrinkSequence,shrinkHOL,iha,ihb]
  | @loop liveIn liveOut body h =>
      intro lt live
      simp only [shrinkSequence,shrinkHOL,fixedpointBranch_complete h,shrinkBranch_eq h]; rfl
  | tail loc args => intro lt live; simp only [shrinkSequence,shrinkHOL]
  | returning names callLive loc exception args liveOut =>
      intro lt live
      exact shrinkSequence_returningCall lt names callLive (some loc) args exception liveOut live
  | returningMarked names callLive loc exception args liveOut =>
      intro lt live
      simp [shrinkSequence,shrinkBranch,shrinkHOL]
  | mark h ih => intro lt live; simp only [shrinkSequence,shrinkHOL,ih]

/-- The whole optimizer can be evaluated structurally on supported programs,
without unfolding the original well-founded liveness recursion. -/
def optimiseSequence (p : HolLoopProg width) : HolLoopProg width :=
  (markAllHOL (shrinkSequence [] p .ln).1).1

theorem optimiseSequence_eq {p : HolLoopProg width} (shape : SimpleLoopSequenceSource p) :
    optimiseSequence p = optimiseHOL p := by
  simp only [optimiseSequence,optimiseHOL,loopCall_simpleSequence shape .ln,compHOL,shrinkSequence_eq shape]


/-- A tail-only entry is covered by the shared call-aware optimizer. -/
theorem tailEntry_to_simple {p : HolLoopProg width} (shape : TailEntryShape p) : SimpleLoopSequenceSource p := by
  induction shape with
  | branch h => exact .branch h
  | call loc => exact .tail loc []
  | seq ha hb iha ihb => exact .seq iha ihb
  | mark h ih => exact .mark ih

/-- The shared executable optimizer handles the existing tail-call entries. -/
theorem optimiseSequence_tail_eq {p : HolLoopProg width} (shape : TailEntryShape p) :
    optimiseSequence p = optimiseHOL p :=
  optimiseSequence_eq (tailEntry_to_simple shape)

end SteppedFlapjack.LoopLiveSteps
