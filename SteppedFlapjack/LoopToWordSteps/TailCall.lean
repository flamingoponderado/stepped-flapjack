import SteppedFlapjack.LoopToWordSteps.LoopProgram
import SteppedFlapjack.LoopLiveSteps.TailEntryCode
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Call.TailCall

/-! Quantitative Loop-to-Word simulation for direct zero-argument tail calls. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.LoopToWord
open Flapjack.LoopToWord.CompileCorrect Flapjack.Compiler.Encoders.Asm

/-- A reached call to a supported Loop body obeys the same sixfold bound as
its callee. The compiler's code relation supplies the actual Word body. -/
theorem sixBoundedDirectTail_nonzero {width : Nat} [NeZero width] {C F : Type}
    (loc : Nat) (body : HolLoopProg width) (shape : LoopProgram body)
    (s : LoopSemStateFiniteExact width F)
    (found : findCode (some loc) [] s.code = some (.ln,body)) (clock : s.clock ≠ 0) :
    SixBoundPropertyAt C (.call none (some loc) [] none) s := by
  intro res final t ctxt retv labels premises
  obtain ⟨run,nonerror,state,locals,ret,dim,notWord,acc⟩ := premises
  have bodyProp : SixBoundPropertyAt C body {decClock s with locals := .ln} :=
    loopProgram_correct_with_steps shape _
  have bodyRun : evaluate body {decClock s with locals := .ln} = (res,final) := by
    rw [evaluate] at run
    simp only [show getVars [] s = some [] from rfl,found,Option.isSome_none,clock] at run
    cases h : evaluate body {decClock s with locals := .ln} with
    | mk r st =>
      rw [h] at run
      cases r with
      | none => simp at run; obtain ⟨rfl,_⟩ := run; exact False.elim (nonerror rfl)
      | some x =>
        cases x <;> simp_all
  have qualitative := compileCorrect_Call_TailCall (C := C) (some loc) [] none s
    (by
      intro vals pair env prog h
      have heq : (env,prog) = (.ln,body) := by
        have hv : vals = [] := Option.some.inj h.1.symm
        subst vals
        rw [h.2.2.1] at h
        exact Option.some.inj (h.2.1.symm.trans found)
      cases heq
      exact fun r st target c rv l pre => by
        obtain ⟨tf,rf,hr,hf,hrel,_⟩ := bodyProp r st target c rv l pre
        exact ⟨tf,rf,hr,hf,hrel⟩)
    res final t ctxt retv labels ⟨run,nonerror,state,locals,ret,dim,notWord,acc⟩
  obtain ⟨tf,rf,evalTarget,ffi,relation⟩ := qualitative
  refine ⟨tf,rf,evalTarget,ffi,relation,?_⟩
  obtain ⟨len,hm,hmd,hsmd,hclock,hbe,hffi,hcur,hlen,htop,hglob,hcode⟩ := state
  obtain ⟨args,ss,calleeCtxt,calleeLabels,wordFound,hret,hcalleelocals,hacc⟩ :=
    findCode_rel s.code t.code t.stackSize (some loc) [] .ln body retv hcode found
  have wordArgs : WordSemStateFiniteExact.getVars [0] t = some [retv] := by
    simp [WordSemStateFiniteExact.getVars,WordSemStateFiniteExact.getVar,ret]
  have targetClock : t.clock ≠ 0 := by rw [hclock]; exact clock
  obtain ⟨_,_,_,_,_,calleeBound⟩ := bodyProp res final
    (WordSemStateFiniteExact.callEnv args ss (WordSemStateFiniteExact.decClock t))
    calleeCtxt retv calleeLabels ⟨bodyRun,nonerror,
      ⟨len,hm,hmd,hsmd,by simp [WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.decClock,
        LoopSemStateFiniteExact.decClock,hclock],hbe,hffi,hcur,hlen,htop,hglob,hcode⟩,
      hcalleelocals,hret,dim,notWord,hacc⟩
  have wordSteps := WordSteps.steps_call_tail (some loc) [0] t [retv] args ss
    (LoopToWord.compHOL calleeCtxt body calleeLabels).1 wordArgs (by simp [wordSemBadDestArgs])
    wordFound targetClock
  have loopSteps := LoopSteps.steps_call_tail (some loc) [] s [] .ln body rfl found clock
  simp only [LoopToWord.compHOL,List.map_nil] at ⊢
  rw [wordSteps,loopSteps]
  omega

/-- The zero-clock call times out at the call node on both sides. -/
theorem sixBoundedDirectTail {width : Nat} [NeZero width] {C F : Type}
    (loc : Nat) (body : HolLoopProg width) (shape : LoopProgram body)
    (s : LoopSemStateFiniteExact width F)
    (found : findCode (some loc) [] s.code = some (.ln,body)) :
    SixBoundPropertyAt C (.call none (some loc) [] none) s := by
  by_cases clock : s.clock = 0
  · intro res final t ctxt retv labels premises
    obtain ⟨run,nonerror,state,locals,ret,dim,notWord,acc⟩ := premises
    have qualitative := compileCorrect_Call_TailCall (C := C) (some loc) [] none s
      (by intro vals pair env prog h; exact False.elim (h.2.2.2.2.2 clock))
      res final t ctxt retv labels ⟨run,nonerror,state,locals,ret,dim,notWord,acc⟩
    obtain ⟨tf,rf,evalTarget,ffi,relation⟩ := qualitative
    refine ⟨tf,rf,evalTarget,ffi,relation,?_⟩
    obtain ⟨len,hm,hmd,hsmd,hclock,hbe,hffi,hcur,hlen,htop,hglob,hcode⟩ := state
    obtain ⟨args,ss,calleeCtxt,calleeLabels,wordFound,hret,hcalleelocals,hacc⟩ :=
      findCode_rel s.code t.code t.stackSize (some loc) [] .ln body retv hcode found
    have wordArgs : WordSemStateFiniteExact.getVars [0] t = some [retv] := by
      simp [WordSemStateFiniteExact.getVars,WordSemStateFiniteExact.getVar,ret]
    have targetClock : t.clock = 0 := by rw [hclock]; exact clock
    have wordSteps : WordSteps.steps (.call none (some loc) [0] none) t = 1 := by
      rw [WordSteps.steps.eq_def]
      simp [wordArgs,wordSemBadDestArgs,wordSemAddRetLoc,wordFound,targetClock]
    have loopSteps : LoopSteps.steps (.call none (some loc) [] none) s = 1 := by
      rw [LoopSteps.steps.eq_def]
      simp [show getVars [] s = some [] from rfl,found,clock]
    simp only [LoopToWord.compHOL,List.map_nil]
    rw [wordSteps,loopSteps]
    omega
  · exact sixBoundedDirectTail_nonzero loc body shape s found clock

/-- Every supported branch is included in the quantitative Loop fragment. -/
theorem loopBranch_program {width : Nat} [NeZero width] {p : HolLoopProg width}
    (shape : LoopBranch p) : LoopProgram p := by
  induction shape with
  | skip => exact .leaf .skip
  | tick => exact .leaf .tick
  | assign v e => exact .leaf (.assign v e)
  | store e v => exact .leaf (.store e v)
  | setGlobal v e => exact .leaf (.setGlobal v e)
  | ret vs => exact .leaf (.ret vs)
  | «break» n => exact .leaf (.break n)
  | «continue» n => exact .leaf (.continue n)
  | seq _ _ a b => exact .seq a b
  | mark _ ih => exact .mark ih
  | ite cmp r ri live _ _ a b => exact .ite cmp r ri live a b

/-- The optimized callee fragment is contained in the quantitative one. -/
theorem loopSequence_program {width : Nat} [NeZero width] {p : HolLoopProg width}
    (shape : LoopSequenceSource p) : LoopProgram p := by
  induction shape with
  | branch h => exact loopBranch_program h
  | loop live exits h => exact .loop live exits (loopBranch_program h)
  | seq _ _ a b => exact .seq a b

/-- A single-destination entry has the sixfold bound when its reached callee
is supported; successful prefixes preserve the lookup needed by the call. -/
theorem singleTailEntry_correct_with_steps {width : Nat} [NeZero width] {C F : Type}
    {loc : Nat} {p : HolLoopProg width} (shape : LoopLiveSteps.SingleTailEntryShape loc p)
    (body : HolLoopProg width) (bodyShape : LoopProgram body) :
    ∀ s : LoopSemStateFiniteExact width F,
      findCode (some loc) [] s.code = some (.ln,body) → SixBoundPropertyAt C p s := by
  induction shape with
  | branch h => intro s _; exact loopProgram_correct_with_steps (loopBranch_program h) s
  | call => intro s found; exact sixBoundedDirectTail loc body bodyShape s found
  | @seq a b ha hb iha ihb =>
    intro s found
    apply sixBoundedSeq a b s
    refine ⟨?_,iha s found⟩
    intro res middle h
    obtain ⟨first,rfl⟩ := h
    have codeEq := LoopLiveSteps.tailEntry_none_code (LoopLiveSteps.singleTail_to_tail ha)
      s middle first.symm
    exact ihb middle (by simpa only [codeEq] using found)
  | @mark p hp ih =>
    intro s found
    exact sixBoundedMark p s (ih s found)

end SteppedFlapjack.LoopToWordSteps
