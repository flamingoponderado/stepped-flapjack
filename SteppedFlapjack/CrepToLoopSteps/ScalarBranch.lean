import SteppedFlapjack.CrepToLoopSteps.ScalarProgramDef

namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack SteppedFlapjack.LoopToWordSteps

def scalarNoWhile {width : Nat} [NeZero width] : CrepProgHOL width → Bool
  | .dec _ _ body => scalarNoWhile body
  | .seq a b => scalarNoWhile a && scalarNoWhile b
  | .ite _ a b => scalarNoWhile a && scalarNoWhile b
  | .while _ _ => false
  | _ => true

private theorem nested_branch {width : Nat} [NeZero width] (xs : List (HolLoopProg width))
    (shape : ∀ p ∈ xs, LoopBranch p) : LoopBranch (loopNestedSeqHOL xs) := by
  induction xs with
  | nil => exact .skip
  | cons p ps ih =>
    simp only [loopNestedSeqHOL]
    exact .seq (shape p (by simp)) (ih (by intro q hq; exact shape q (by simp [hq])))

/-- Loop-free recursive scalar Crep programs compile to Loop branches. -/
theorem compile_scalar_branch {width : Nat} [NeZero width] {p : CrepProgHOL width}
    (shape : ScalarProgram p) (loopFree : scalarNoWhile p = true) :
    ∀ ctxt live, LoopBranch (compileHOLExact ctxt live p) := by
  induction shape with
  | skip => intro ctxt live; simp only [compileHOLExact]; exact .skip
  | «break» n => intro ctxt live; simp only [compileHOLExact]; exact .break n
  | «continue» n => intro ctxt live; simp only [compileHOLExact]; exact .continue n
  | tick => intro ctxt live; simp only [compileHOLExact]; exact .tick
  | @ret e he =>
    intro ctxt live
    obtain ⟨code,value,next,outLive,compiled,_,_,pref⟩ := compiledScalar_prefix he ctxt (ctxt.vmax+1) live
    simp only [compileHOLExact,compileExpsHOLExact,compiled,List.append_nil,genTemps,List.length_cons,List.length_nil,List.range_succ,
      List.range_zero,List.nil_append,List.map_cons,List.map_nil,List.zipWith_cons_cons,List.zipWith_nil_left,Nat.add_zero]
    apply nested_branch
    intro p hp
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with (h | rfl) | rfl
    · exact pref p h
    · exact .assign _ _
    · exact .ret _
  | @assign n e he =>
    intro ctxt live
    obtain ⟨code,value,next,outLive,compiled,_,_,pref⟩ := compiledScalar_prefix he ctxt (ctxt.vmax+1) live
    simp only [compileHOLExact]
    cases h : ctxt.vars.lookup n with
    | none => exact .skip
    | some mapped =>
      simp only [compiled]
      apply nested_branch
      intro p hp
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with h | rfl
      · exact pref p h
      · exact .assign _ _
  | @store a b ha hb =>
    intro ctxt live
    obtain ⟨ca,va,na,la,ea,_,_,pa⟩ := compiledScalar_prefix ha ctxt (ctxt.vmax+1) live
    obtain ⟨cb,vb,nb,lb,eb,_,_,pb⟩ := compiledScalar_prefix hb ctxt na la
    simp only [compileHOLExact,ea,eb]
    apply nested_branch
    intro p hp
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with (h | h) | rfl | rfl
    · exact pa p h
    · exact pb p h
    · exact .assign _ _
    · exact .store _ _
  | @dec n e body he hb ih =>
    intro ctxt live
    obtain ⟨code,value,next,outLive,compiled,_,_,pref⟩ := compiledScalar_prefix he ctxt (ctxt.vmax+1) live
    have bodyFree : scalarNoWhile body = true := by simpa [scalarNoWhile] using loopFree
    simp only [compileHOLExact,compiled]
    exact .seq (nested_branch code pref) (.seq (.assign _ _) (ih bodyFree _ _))
  | @seq a b ha hb iha ihb =>
    intro ctxt live
    have h : scalarNoWhile a = true ∧ scalarNoWhile b = true := by simpa [scalarNoWhile] using loopFree
    simpa only [compileHOLExact] using LoopBranch.seq (iha h.1 ctxt live) (ihb h.2 ctxt live)
  | @ite e a b he ha hb iha ihb =>
    intro ctxt live
    have h : scalarNoWhile a = true ∧ scalarNoWhile b = true := by simpa [scalarNoWhile] using loopFree
    obtain ⟨code,value,next,outLive,compiled,_,_,pref⟩ := compiledScalar_prefix he ctxt (ctxt.vmax+1) live
    simp only [compileHOLExact,compiled]
    apply nested_branch
    intro p hp
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with hmem | rfl | rfl
    · exact pref p hmem
    · exact .assign _ _
    · exact .ite _ _ _ _ (iha h.1 _ _) (ihb h.2 _ _)
  | «while» => simp [scalarNoWhile] at loopFree
end SteppedFlapjack.CrepToLoopSteps
