import SteppedFlapjack.LoopLiveSteps.CallPass
import Flapjack.Pancake.LoopLive

/-! Liveness shrinking on loop-free Loop branches. -/
namespace SteppedFlapjack.LoopLiveSteps
open Flapjack SteppedFlapjack.LoopToWordSteps
variable {width : Nat} [NeZero width]

/-- The actual liveness pass preserves the supported branch shape, including
assignment elimination and updated conditional live sets. -/
theorem shrink_branch {p : HolLoopProg width} (shape : LoopBranch p) :
    ∀ lt live, LoopBranch (shrinkHOL lt p live).1 := by
  induction shape with
  | skip => intro lt live; simp only [shrinkHOL]; exact .skip
  | tick => intro lt live; simp only [shrinkHOL]; exact .tick
  | assign v e =>
    intro lt live
    simp only [shrinkHOL]
    cases sptLookup v live <;> first | exact .skip | exact .assign _ _
  | store e v => intro lt live; simp only [shrinkHOL]; exact .store _ _
  | setGlobal v e => intro lt live; simp only [shrinkHOL]; exact .setGlobal _ _
  | ret vs => intro lt live; simp only [shrinkHOL]; exact .ret _
  | «break» n => intro lt live; simp only [shrinkHOL]; exact .break _
  | «continue» n => intro lt live; simp only [shrinkHOL]; exact .continue _
  | @seq a b ha hb iha ihb =>
    intro lt live
    simp only [shrinkHOL]
    exact .seq (iha lt (shrinkHOL lt b live).2) (ihb lt live)
  | mark h ih => intro lt live; simpa only [shrinkHOL] using ih lt live
  | ite cmp r ri ls ha hb iha ihb =>
    intro lt live
    cases ri <;> simp only [shrinkHOL] <;>
      exact .ite _ _ _ _ (iha lt (sptInter live ls)) (ihb lt (sptInter live ls))

/-- Any successful loop liveness fixed point returns a branch-shaped body. -/
theorem fixedpoint_branch {body : HolLoopProg width} (shape : LoopBranch body)
    (lt : List (NumSet × NumSet)) (liveIn l1 l2 : NumSet)
    (out : HolLoopProg width) (liveOut : NumSet)
    (result : fixedpointHOL lt liveIn l1 l2 body = some (out,liveOut)) : LoopBranch out := by
  induction hmeasure : sptSize liveIn - sptSize l1 using Nat.strongRecOn generalizing l1 with
  | _ measure ih =>
    rcases hsh : shrinkHOL ((sptInter liveIn l1,l2)::lt) body l2 with ⟨shrunk,l0⟩
    rw [fixedpointHOL] at result
    simp only [hsh] at result
    split at result
    · simp only [Option.some.injEq, Prod.mk.injEq] at result
      have branch := shrink_branch shape ((sptInter liveIn l1,l2)::lt) l2
      rw [hsh] at branch
      simpa only [result.1] using branch
    · split at result
      · cases result
      · rename_i stable progress
        apply ih (sptSize liveIn - sptSize (sptInter liveIn l0)) ?_ _ result rfl
        have bounded := sptSize_inter_le liveIn l0
        omega

/-- The liveness pass preserves supported sequences of branch-bodied loops. -/
theorem shrink_sequence {p : HolLoopProg width} (shape : LoopSequenceSource p) :
    ∀ lt live, LoopSequenceSource (shrinkHOL lt p live).1 := by
  induction shape with
  | branch h => intro lt live; exact .branch (shrink_branch h lt live)
  | @seq a b ha hb iha ihb =>
    intro lt live
    simp only [shrinkHOL]
    exact .seq (iha lt (shrinkHOL lt b live).2) (ihb lt live)
  | @loop liveIn liveOut body h =>
    intro lt live
    simp only [shrinkHOL]
    cases fixed : fixedpointHOL lt liveIn .ln (sptUnion liveIn (sptInter liveOut live)) body with
    | none => exact .loop _ _ (shrink_branch h _ _)
    | some pair =>
      cases pair with
      | mk body out => exact .loop _ _ (fixedpoint_branch h lt liveIn .ln _ body out fixed)

end SteppedFlapjack.LoopLiveSteps
