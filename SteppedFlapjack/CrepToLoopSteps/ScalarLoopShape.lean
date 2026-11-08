import SteppedFlapjack.CrepToLoopSteps.ScalarProgram
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack SteppedFlapjack.LoopToWordSteps

/-- Loop programs with recursive branches and loops and loop-free basic blocks. -/
inductive ScalarLoop {width : Nat} [NeZero width] : HolLoopProg width → Prop
  | branch {p} : LoopBranch p → ScalarLoop p
  | seq {a b} : ScalarLoop a → ScalarLoop b → ScalarLoop (.seq a b)
  | ite (cmp r ri live) {a b} : ScalarLoop a → ScalarLoop b → ScalarLoop (.ite cmp r ri a b live)
  | loop (liveIn liveOut) {body} : ScalarLoop body → ScalarLoop (.loop liveIn body liveOut)

private theorem scalarLoop_nested {width : Nat} [NeZero width] (xs : List (HolLoopProg width))
    (shape : ∀ p ∈ xs, ScalarLoop p) : ScalarLoop (loopNestedSeqHOL xs) := by
  induction xs with
  | nil => exact .branch .skip
  | cons p ps ih =>
    simp only [loopNestedSeqHOL]
    exact .seq (shape p (by simp)) (ih (by intro q hq; exact shape q (by simp [hq])))

/-- The Loop compiler preserves recursive scalar shape, including nested loops. -/
theorem compile_scalar_program {width : Nat} [NeZero width] {p : CrepProgHOL width}
    (shape : ScalarProgram p) : ∀ ctxt live, ScalarLoop (compileHOLExact ctxt live p) := by
  induction shape with
  | skip => intro ctxt live; simp only [compileHOLExact]; exact .branch .skip
  | «break» n => intro ctxt live; simp only [compileHOLExact]; exact .branch (.break n)
  | «continue» n => intro ctxt live; simp only [compileHOLExact]; exact .branch (.continue n)
  | tick => intro ctxt live; simp only [compileHOLExact]; exact .branch .tick
  | @ret e he =>
    intro ctxt live
    obtain ⟨code,value,next,outLive,compiled,_,_,pref⟩ := compiledScalar_prefix he ctxt (ctxt.vmax+1) live
    simp only [compileHOLExact,compileExpsHOLExact,compiled,List.append_nil,genTemps,List.length_cons,List.length_nil,List.range_succ,
      List.range_zero,List.nil_append,List.map_cons,List.map_nil,List.zipWith_cons_cons,List.zipWith_nil_left,Nat.add_zero]
    apply scalarLoop_nested
    intro p hp
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with (h | rfl) | rfl
    · exact .branch (pref p h)
    · exact .branch (.assign _ _)
    · exact .branch (.ret _)
  | @assign n e he =>
    intro ctxt live
    obtain ⟨code,value,next,outLive,compiled,_,_,pref⟩ := compiledScalar_prefix he ctxt (ctxt.vmax+1) live
    simp only [compileHOLExact]
    cases h : ctxt.vars.lookup n with
    | none => exact .branch .skip
    | some mapped =>
      simp only [compiled]
      apply scalarLoop_nested
      intro p hp
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with h | rfl
      · exact .branch (pref p h)
      · exact .branch (.assign _ _)
  | @store a b ha hb =>
    intro ctxt live
    obtain ⟨ca,va,na,la,ea,_,_,pa⟩ := compiledScalar_prefix ha ctxt (ctxt.vmax+1) live
    obtain ⟨cb,vb,nb,lb,eb,_,_,pb⟩ := compiledScalar_prefix hb ctxt na la
    simp only [compileHOLExact,ea,eb]
    apply scalarLoop_nested
    intro p hp
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with (h | h) | rfl | rfl
    · exact .branch (pa p h)
    · exact .branch (pb p h)
    · exact .branch (.assign _ _)
    · exact .branch (.store _ _)
  | @dec n e body he hb ih =>
    intro ctxt live
    obtain ⟨code,value,next,outLive,compiled,_,_,pref⟩ := compiledScalar_prefix he ctxt (ctxt.vmax+1) live
    simp only [compileHOLExact,compiled]
    refine .seq (scalarLoop_nested code (by intro p hp; exact .branch (pref p hp)))
      (.seq (.branch (.assign _ _)) (ih _ _))
  | @seq a b ha hb iha ihb =>
    intro ctxt live; simpa only [compileHOLExact] using ScalarLoop.seq (iha ctxt live) (ihb ctxt live)
  | @ite e a b he ha hb iha ihb =>
    intro ctxt live
    obtain ⟨code,value,next,outLive,compiled,_,_,pref⟩ := compiledScalar_prefix he ctxt (ctxt.vmax+1) live
    simp only [compileHOLExact,compiled]
    apply scalarLoop_nested
    intro p hp
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with h | rfl | rfl
    · exact .branch (pref p h)
    · exact .branch (.assign _ _)
    · exact .ite _ _ _ _ (iha _ _) (ihb _ _)
  | @«while» e body he hb ih =>
    intro ctxt live
    obtain ⟨code,value,next,outLive,compiled,_,_,pref⟩ := compiledScalar_prefix he ctxt (ctxt.vmax+1) live
    simp only [compileHOLExact,compiled]
    apply ScalarLoop.loop
    apply scalarLoop_nested
    intro p hp
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with h | rfl | rfl
    · exact .branch (pref p h)
    · exact .branch (.assign _ _)
    · exact .ite _ _ _ _ (.seq (ih _ _) (.branch (.continue 0))) (.branch (.break 0))
end SteppedFlapjack.CrepToLoopSteps
