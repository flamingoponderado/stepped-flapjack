import SteppedFlapjack.WordSsaSteps.Branch

/-! SSA output shape for recursive call-free programs. -/
namespace SteppedFlapjack.WordSsaSteps
open Flapjack Flapjack.Compiler.Backend.WordAlloc SteppedFlapjack.WordSimpSteps
open Flapjack.WordSemStateFiniteExact SteppedFlapjack.WordSteps
variable {width : Nat} [NeZero width] {C F : Type}

/-- SSA translation preserves the recursive call-free fragment, while adding loop setup and reconciliation. -/
theorem ssaLoopSequence_shape {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p) :
    ∀ ssa next targets, LoopSequence (ssaCcTrans p ssa next targets).1 := by
  induction shape with
  | branch h => intro ssa next targets; exact .branch (ssaBranch_shape h ssa next targets)
  | @seq a b ha hb iha ihb =>
    intro ssa next targets
    simp only [ssaCcTrans]
    rcases h : ssaCcTrans a ssa next targets with ⟨a',sa,na⟩
    rcases k : ssaCcTrans b sa na targets with ⟨b',sb,nb⟩
    have aa := iha ssa next targets
    have bb := ihb sa na targets
    simp only [h] at aa
    simp only [k] at bb
    exact .seq aa bb
  | @loop names exits body hb =>
    intro ssa next targets
    simp only [ssaCcTrans]
    rcases h : loopSetup (width := width) names exits ssa next with ⟨setup,refreshed,nr⟩
    rcases k : ssaCcTrans body (sptInter refreshed names) nr ((refreshed,names,exits)::targets) with ⟨body',outMap,outNext⟩
    have setupShape := loopSetup_branch (width := width) names exits ssa next
    have bodyShape := ssaBranch_shape hb (sptInter refreshed names) nr ((refreshed,names,exits)::targets)
    simp only [h] at setupShape
    simp only [k] at bodyShape
    have reconcileShape := reconcile_branch (width := width) outMap refreshed names
    cases hr : ssaReconcile (width := width) outMap refreshed names <;> simp only [hr] at reconcileShape ⊢
    all_goals first | exact .seq (.branch setupShape) (.loop _ _ bodyShape) |
      exact .seq (.branch setupShape) (.loop _ _ (.seq bodyShape reconcileShape))

  | @nestedLoop names exits body hb ih =>
    intro ssa next targets
    simp only [ssaCcTrans]
    rcases h : loopSetup (width := width) names exits ssa next with ⟨setup,refreshed,nr⟩
    rcases k : ssaCcTrans body (sptInter refreshed names) nr ((refreshed,names,exits)::targets) with ⟨body',outMap,outNext⟩
    have setupShape := loopSetup_branch (width := width) names exits ssa next
    have bodyShape := ih (sptInter refreshed names) nr ((refreshed,names,exits)::targets)
    simp only [h] at setupShape
    simp only [k] at bodyShape
    have reconcileShape := reconcile_branch (width := width) outMap refreshed names
    cases hr : ssaReconcile (width := width) outMap refreshed names <;> simp only [hr] at reconcileShape ⊢
    all_goals first | exact .seq (.branch setupShape) (.nestedLoop _ _ bodyShape) |
      exact .seq (.branch setupShape) (.nestedLoop _ _ (.seq bodyShape (.branch reconcileShape)))
  | @conditional cmp r ri a b ha hb iha ihb =>
    intro ssa next targets
    simp only [ssaCcTrans]
    rcases h : ssaCcTrans a ssa next targets with ⟨a',sa,na⟩
    rcases k : ssaCcTrans b ssa na targets with ⟨b',sb,nb⟩
    rcases z : fixInconsistencies (mkPrio a' b') sa sb nb with ⟨ac,bc,nf,sf⟩
    have aa := iha ssa next targets
    have bb := ihb ssa na targets
    have cons := fixInconsistencies_branch (width := width) (mkPrio a' b') sa sb nb
    simp only [h] at aa
    simp only [k] at bb
    simp only [z] at cons
    exact .conditional _ _ _ (.seq aa (.branch cons.1)) (.seq bb (.branch cons.2))

/-- The actual full SSA pass preserves recursive call-free programs. -/
theorem fullSsa_loopSequence_shape (count : Nat) {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p) :
    LoopSequence (fullSsaCcTrans count p) := by
  unfold fullSsaCcTrans setupSSA
  dsimp only
  rcases h : listNextVarRename (evenList count) .ln (limitVar p) with ⟨newNames,ssa,next⟩
  rcases k : ssaCcTrans p ssa next [] with ⟨body,sa,na⟩
  have hb := ssaLoopSequence_shape shape ssa next []
  simp only [k] at hb
  exact .seq (.branch (.move _ _)) hb

/-- The actual full SSA output has a syntax-based clock bound on visits. -/
theorem fullSsa_clock_bound (count : Nat) {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p)
    (s : WordSemStateFiniteExact width C F) :
    steps (fullSsaCcTrans count p) s ≤ sizeOf (fullSsaCcTrans count p) * (s.clock+1) :=
  loopSequence_clock_bound (fullSsa_loopSequence_shape count shape) s

end SteppedFlapjack.WordSsaSteps
