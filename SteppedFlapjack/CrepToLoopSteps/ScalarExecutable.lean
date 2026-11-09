import SteppedFlapjack.CrepToLoopSteps.ScalarLoopLive
import SteppedFlapjack.LoopLiveSteps.ExecutableBranch
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack SteppedFlapjack.LoopToWordSteps SteppedFlapjack.LoopLiveSteps
variable {width : Nat} [NeZero width]

def scalarFixedpoint (f : List (NumSet × NumSet) → NumSet → HolLoopProg width × NumSet) :
    Nat → List (NumSet × NumSet) → NumSet → NumSet → NumSet → Option (HolLoopProg width × NumSet)
  | 0, _, _, _, _ => none
  | fuel+1, lt, li, l1, l2 =>
      let (b,l0) := f ((sptInter li l1,l2)::lt) l2
      if sptInter li l0 = l1 then some (b,l0)
      else if sptSize (sptInter li l0) ≤ sptSize l1 then none
      else scalarFixedpoint f fuel lt li (sptInter li l0) l2

theorem scalarFixedpoint_eq {body : HolLoopProg width}
    (f : List (NumSet × NumSet) → NumSet → HolLoopProg width × NumSet)
    (hf : ∀ lt live, f lt live = shrinkHOL lt body live)
    (fuel : Nat) (lt : List (NumSet × NumSet)) (li l1 l2 : NumSet)
    (enough : sptSize li - sptSize l1 < fuel) :
    scalarFixedpoint f fuel lt li l1 l2 = fixedpointHOL lt li l1 l2 body := by
  induction fuel generalizing l1 with
  | zero => omega
  | succ fuel ih =>
    rw [scalarFixedpoint,fixedpointHOL,hf]
    rcases h : shrinkHOL ((sptInter li l1,l2)::lt) body l2 with ⟨b,l0⟩
    simp only
    split
    · rfl
    · split
      · rfl
      · rename_i stable progress
        apply ih
        have bound := sptSize_inter_le li l0
        omega

def shrinkScalar : Nat → List (NumSet × NumSet) → HolLoopProg width → NumSet → HolLoopProg width × NumSet
  | 0, _, _, _ => (.skip,.ln)
  | fuel+1, lt, .seq a b, live =>
      let (b,live) := shrinkScalar fuel lt b live
      let (a,live) := shrinkScalar fuel lt a live
      (.seq a b,live)
  | fuel+1, lt, .ite cmp r ri a b ls, live =>
      let live := sptInter live ls
      let (a,la) := shrinkScalar fuel lt a live
      let (b,lb) := shrinkScalar fuel lt b live
      let lr := match ri with | .reg r => sptInsert r () .ln | _ => .ln
      (.ite cmp r ri a b live,sptInsert r () (sptUnion lr (sptUnion la lb)))
  | fuel+1, lt, .loop li body lo, live =>
      let l2 := sptInter lo live
      let bex := sptUnion li l2
      let f := fun lt live => shrinkScalar fuel lt body live
      match scalarFixedpoint f (sptSize li+1) lt li .ln bex with
      | some (b,l0) => let l := sptInter li l0; (.loop l b l2,l)
      | none => let (b,_) := f ((li,l2)::lt) bex; (.loop li b l2,li)
  | fuel+1, lt, .mark p, live => shrinkScalar fuel lt p live
  | _+1, lt, p, live => shrinkBranch lt p live

/-- Structural depth counts control nodes without inspecting literal values. -/
def scalarDepth : HolLoopProg width → Nat
  | .seq a b => 1 + max (scalarDepth a) (scalarDepth b)
  | .ite _ _ _ a b _ => 1 + max (scalarDepth a) (scalarDepth b)
  | .loop _ body _ => 1 + scalarDepth body
  | .mark body => 1 + scalarDepth body
  | _ => 1

/-- The bounded evaluator agrees with liveness on loop-free branches. -/
theorem shrinkScalar_branch {p : HolLoopProg width} (shape : LoopBranch p) :
    ∀ fuel, scalarDepth p < fuel → ∀ lt live, shrinkScalar fuel lt p live = shrinkHOL lt p live := by
  induction shape with
  | skip | tick | assign _ _ | store _ _ | setGlobal _ _ | ret _ | «break» _ | «continue» _ =>
    intro fuel enough lt live
    cases fuel with
    | zero => omega
    | succ fuel => simp [shrinkScalar,shrinkBranch,shrinkHOL] <;> rfl
  | @seq a b ha hb iha ihb =>
    intro fuel enough lt live
    cases fuel with
    | zero => omega
    | succ fuel =>
      have aa : scalarDepth a < fuel := by
        simp only [scalarDepth] at enough
        omega
      have bb : scalarDepth b < fuel := by
        simp only [scalarDepth] at enough
        omega
      simp only [shrinkScalar,shrinkHOL,iha fuel aa,ihb fuel bb]
  | @ite cmp r ri ls a b ha hb iha ihb =>
    intro fuel enough lt live
    cases fuel with
    | zero => omega
    | succ fuel =>
      have aa : scalarDepth a < fuel := by
        simp only [scalarDepth] at enough
        omega
      have bb : scalarDepth b < fuel := by
        simp only [scalarDepth] at enough
        omega
      cases ri <;> simp only [shrinkScalar,shrinkHOL,iha fuel aa,ihb fuel bb]
  | @mark p h ih =>
    intro fuel enough lt live
    cases fuel with
    | zero => omega
    | succ fuel =>
      have pp : scalarDepth p < fuel := by
        simp only [scalarDepth] at enough
        omega
      simp only [shrinkScalar,shrinkHOL,ih fuel pp]

/-- A structural recursion budget computes the actual liveness pass. -/
theorem shrinkScalar_eq {p : HolLoopProg width} (shape : ScalarLoop p) :
    ∀ fuel, scalarDepth p < fuel → ∀ lt live, shrinkScalar fuel lt p live = shrinkHOL lt p live := by
  induction shape with
  | branch h => exact shrinkScalar_branch h
  | @seq a b ha hb iha ihb =>
    intro fuel enough lt live
    cases fuel with
    | zero => omega
    | succ fuel =>
      have aa : scalarDepth a < fuel := by
        simp only [scalarDepth] at enough
        omega
      have bb : scalarDepth b < fuel := by
        simp only [scalarDepth] at enough
        omega
      simp only [shrinkScalar,shrinkHOL,iha fuel aa,ihb fuel bb]
  | @ite cmp r ri ls a b ha hb iha ihb =>
    intro fuel enough lt live
    cases fuel with
    | zero => omega
    | succ fuel =>
      have aa : scalarDepth a < fuel := by
        simp only [scalarDepth] at enough
        omega
      have bb : scalarDepth b < fuel := by
        simp only [scalarDepth] at enough
        omega
      cases ri <;> simp only [shrinkScalar,shrinkHOL,iha fuel aa,ihb fuel bb]
  | @loop li lo body hb ih =>
    intro fuel enough lt live
    cases fuel with
    | zero => omega
    | succ fuel =>
      have small : scalarDepth body < fuel := by
        simp only [scalarDepth] at enough
        omega
      have hf := ih fuel small
      simp only [shrinkScalar,shrinkHOL]
      rw [scalarFixedpoint_eq (fun lt live => shrinkScalar fuel lt body live) hf
        (sptSize li + 1) lt li .ln (sptUnion li (sptInter lo live)) (by omega)]
      cases h : fixedpointHOL lt li .ln (sptUnion li (sptInter lo live)) body <;>
        simp only [hf]

/-- Computable optimizer for the recursive scalar Loop fragment. -/
def optimiseScalar (p : HolLoopProg width) : HolLoopProg width :=
  (markAllHOL (shrinkScalar (scalarDepth p + 1) [] p .ln).1).1

theorem optimiseScalar_eq {p : HolLoopProg width} (shape : ScalarLoop p) :
    optimiseScalar p = optimiseHOL p := by
  simp only [optimiseScalar,optimiseHOL,scalarLoop_call shape .ln,compHOL]
  rw [shrinkScalar_eq shape (scalarDepth p + 1) (by omega) [] .ln]

end SteppedFlapjack.CrepToLoopSteps
