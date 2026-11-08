import SteppedFlapjack.CrepToLoopSteps.ScalarBranch
import SteppedFlapjack.CrepToLoopSteps.ScalarLoopShape
import SteppedFlapjack.CrepToLoopSteps.ScalarLoopWeight
import SteppedFlapjack.LoopSteps.BranchedStatic
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.LoopSemStateFiniteExact SteppedFlapjack.LoopToWordSteps
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
variable {width : Nat} [NeZero width]
def noMark : HolLoopProg width → Bool
  | .mark _ => false
  | .seq a b => noMark a && noMark b
  | .ite _ _ _ a b _ => noMark a && noMark b
  | .loop _ body _ => noMark body
  | _ => true

theorem scalar_prefix_unmarked {e : CrepExpHOL width} (shape : CompiledScalar e) :
    ∀ ctxt tmp live p, p ∈ (compileExpHOLExact ctxt tmp live e).1 → noMark p = true := by
  induction shape with
  | direct shape =>
    intro ctxt tmp live p member
    obtain ⟨value,compiled⟩ := directExpression_noCode shape ctxt tmp live
    simp [compiled] at member
  | @shift op a b ha hb iha ihb =>
    intro ctxt tmp live p member
    rcases ca : compileExpHOLExact ctxt tmp live a with ⟨ac,av,an,al⟩
    rcases cb : compileExpHOLExact ctxt an al b with ⟨bc,bv,bn,bl⟩
    simp only [compileExpHOLExact,ca,cb,List.mem_append] at member
    rcases member with h | h
    · apply iha ctxt tmp live p; simpa [ca] using h
    · apply ihb ctxt an al p; simpa [cb] using h
  | @op op a b ha hb iha ihb =>
    intro ctxt tmp live p member
    rcases ca : compileExpHOLExact ctxt tmp live a with ⟨ac,av,an,al⟩
    rcases cb : compileExpHOLExact ctxt an al b with ⟨bc,bv,bn,bl⟩
    simp only [compileExpHOLExact,compileExpsHOLExact,ca,cb,List.append_nil,List.mem_append] at member
    rcases member with h | h
    · apply iha ctxt tmp live p; simpa [ca] using h
    · apply ihb ctxt an al p; simpa [cb] using h
  | @cmp op a b ha hb iha ihb =>
    intro ctxt tmp live p member
    rcases ca : compileExpHOLExact ctxt tmp live a with ⟨ac,av,an,al⟩
    rcases cb : compileExpHOLExact ctxt an al b with ⟨bc,bv,bn,bl⟩
    simp only [compileExpHOLExact,ca,cb,progIfHOLExact,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with (h | h) | rfl | rfl | rfl
    · apply iha ctxt tmp live p; simpa [ca] using h
    · apply ihb ctxt an al p; simpa [cb] using h
    · rfl
    · rfl
    · rfl
private theorem nested_unmarked (xs : List (HolLoopProg width))
    (h : ∀ p ∈ xs, noMark p = true) : noMark (loopNestedSeqHOL xs) = true := by
  induction xs with
  | nil => rfl
  | cons p ps ih =>
    simp only [loopNestedSeqHOL,noMark,Bool.and_eq_true]
    exact ⟨h p (by simp),ih (by intro q hq; exact h q (by simp [hq]))⟩

theorem scalar_program_unmarked {p : CrepProgHOL width} (shape : ScalarProgram p) :
    ∀ ctxt live, noMark (compileHOLExact ctxt live p) = true := by
  induction shape with
  | skip | «break» | «continue» | tick => intros; simp only [compileHOLExact,noMark]
  | @ret e he =>
    intro ctxt live
    obtain ⟨code,value,next,outLive,compiled,_⟩ := compiledScalar_prefix he ctxt (ctxt.vmax+1) live
    have pref : ∀ p ∈ code, noMark p = true := by
      intro p hp
      apply scalar_prefix_unmarked he ctxt (ctxt.vmax+1) live p
      simpa [compiled] using hp
    simp only [compileHOLExact,compileExpsHOLExact,compiled,List.append_nil,genTemps,List.length_cons,List.length_nil,List.range_succ,
      List.range_zero,List.nil_append,List.map_cons,List.map_nil,List.zipWith_cons_cons,List.zipWith_nil_left,Nat.add_zero]
    apply nested_unmarked
    intro p hp
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with (h | rfl) | rfl
    · exact pref p h
    · rfl
    · rfl
  | @assign n e he =>
    intro ctxt live
    obtain ⟨code,value,next,outLive,compiled,_⟩ := compiledScalar_prefix he ctxt (ctxt.vmax+1) live
    have pref : ∀ p ∈ code, noMark p = true := by
      intro p hp
      apply scalar_prefix_unmarked he ctxt (ctxt.vmax+1) live p
      simpa [compiled] using hp
    simp only [compileHOLExact]
    cases h : ctxt.vars.lookup n with
    | none => rfl
    | some mapped =>
      simp only [compiled]
      apply nested_unmarked
      intro p hp
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with h | rfl
      · exact pref p h
      · rfl
  | @store a b ha hb =>
    intro ctxt live
    obtain ⟨ca,va,na,la,ea,_⟩ := compiledScalar_prefix ha ctxt (ctxt.vmax+1) live
    obtain ⟨cb,vb,nb,lb,eb,_⟩ := compiledScalar_prefix hb ctxt na la
    have pa : ∀ p ∈ ca, noMark p = true := by
      intro p hp; apply scalar_prefix_unmarked ha ctxt (ctxt.vmax+1) live p; simpa [ea] using hp
    have pb : ∀ p ∈ cb, noMark p = true := by
      intro p hp; apply scalar_prefix_unmarked hb ctxt na la p; simpa [eb] using hp
    simp only [compileHOLExact,ea,eb]
    apply nested_unmarked
    intro p hp
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with (h | h) | rfl | rfl
    · exact pa p h
    · exact pb p h
    · rfl
    · rfl
  | @dec n e body he hb ih =>
    intro ctxt live
    obtain ⟨code,value,next,outLive,compiled,_⟩ := compiledScalar_prefix he ctxt (ctxt.vmax+1) live
    have pref : ∀ p ∈ code, noMark p = true := by
      intro p hp; apply scalar_prefix_unmarked he ctxt (ctxt.vmax+1) live p; simpa [compiled] using hp
    simp only [compileHOLExact,compiled,noMark,Bool.and_eq_true]
    exact ⟨nested_unmarked code pref,True.intro,ih _ _⟩
  | @seq a b ha hb iha ihb =>
    intro ctxt live; simp only [compileHOLExact,noMark,Bool.and_eq_true]; exact ⟨iha _ _,ihb _ _⟩
  | @ite e a b he ha hb iha ihb =>
    intro ctxt live
    obtain ⟨code,value,next,outLive,compiled,_⟩ := compiledScalar_prefix he ctxt (ctxt.vmax+1) live
    have pref : ∀ p ∈ code, noMark p = true := by
      intro p hp; apply scalar_prefix_unmarked he ctxt (ctxt.vmax+1) live p; simpa [compiled] using hp
    simp only [compileHOLExact,compiled]
    apply nested_unmarked
    intro p hp
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with h | rfl | rfl
    · exact pref p h
    · rfl
    · simp only [noMark,Bool.and_eq_true]; exact ⟨iha _ _,ihb _ _⟩
  | @«while» e body he hb ih =>
    intro ctxt live
    obtain ⟨code,value,next,outLive,compiled,_⟩ := compiledScalar_prefix he ctxt (ctxt.vmax+1) live
    have pref : ∀ p ∈ code, noMark p = true := by
      intro p hp; apply scalar_prefix_unmarked he ctxt (ctxt.vmax+1) live p; simpa [compiled] using hp
    simp only [compileHOLExact,compiled,noMark]
    apply nested_unmarked
    intro p hp
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with h | rfl | rfl
    · exact pref p h
    · rfl
    · simp only [noMark,Bool.and_true]; exact ih _ _
private theorem branch_weight_equal {p : HolLoopProg width} (shape : LoopBranch p)
    (unmarked : noMark p = true) : LoopSteps.structuralWeight p = loopSkeletonWeight p := by
  induction shape <;> simp_all [noMark,LoopSteps.structuralWeight,loopSkeletonWeight]

/-- Loop-free compiled scalar code has structural weight bounded by the
size of the actual optimized output. -/
theorem scalarBranch_structural_le_output {p : CrepProgHOL width} (shape : ScalarProgram p)
    (free : scalarNoWhile p = true) (ctxt : CrepToLoopContextExact) (live : NumSet) :
    LoopSteps.structuralWeight (compileHOLExact ctxt live p) ≤
      sizeOf (optimiseHOL (compileHOLExact ctxt live p)) := by
  rw [branch_weight_equal (compile_scalar_branch shape free ctxt live) (scalar_program_unmarked shape ctxt live)]
  exact scalarLoop_weight_le_optimised_size (compile_scalar_program shape ctxt live)
end SteppedFlapjack.CrepToLoopSteps
