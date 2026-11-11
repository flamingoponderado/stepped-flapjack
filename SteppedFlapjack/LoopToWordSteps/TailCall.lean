import SteppedFlapjack.LoopToWordSteps.LoopProgram
import SteppedFlapjack.WordSteps.CallSteps
import SteppedFlapjack.LoopLiveSteps.TailEntryCode
import SteppedFlapjack.LoopLiveSteps.TailEntryBound
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Call.TailCall

/-! Quantitative Loop-to-Word simulation for direct zero-argument tail calls. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.LoopToWord
open Flapjack.LoopToWord.CompileCorrect Flapjack.Compiler.Encoders.Asm

/-- A reached call obeys the same sixfold bound as its callee. The code
relation supplies the actual Word body. -/
theorem sixBoundedDirectTail_nonzero {width : Nat} [NeZero width] {C F : Type}
    (loc : Nat) (vars : List Nat) (vals : List (WordLocW width)) (env : Spt (WordLocW width))
    (body : HolLoopProg width) (s : LoopSemStateFiniteExact width F)
    (bodyProp : SixBoundPropertyAt C body {decClock s with locals := env})
    (get : getVars vars s = some vals) (found : findCode (some loc) vals s.code = some (env,body)) (clock : s.clock ≠ 0) :
    SixBoundPropertyAt C (.call none (some loc) vars none) s := by
  intro res final t ctxt retv labels premises
  obtain ⟨run,nonerror,state,locals,ret,dim,notWord,acc⟩ := premises
  have bodyRun : evaluate body {decClock s with locals := env} = (res,final) := by
    rw [evaluate] at run
    simp only [get,found,Option.isSome_none,clock] at run
    cases h : evaluate body {decClock s with locals := env} with
    | mk r st =>
      rw [h] at run
      cases r with
      | none => simp at run; obtain ⟨rfl,_⟩ := run; exact False.elim (nonerror rfl)
      | some x =>
        cases x <;> simp_all
  have qualitative := compileCorrect_Call_TailCall (C := C) (some loc) vars none s
    (by
      intro argvals pair env2 prog h
      have heq : (env2,prog) = (env,body) := by
        have hv : argvals = vals := Option.some.inj (h.1.symm.trans get)
        subst argvals
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
    findCode_rel s.code t.code t.stackSize (some loc) vals env body retv hcode found
  obtain ⟨wordGet, _⟩ := LoopToWord.localsRelHOLGetVars ctxt s t vars vals ⟨locals,get⟩
  have wordArgs : WordSemStateFiniteExact.getVars (0 :: vars.map (LoopToWord.findVarHOL ctxt)) t = some (retv :: vals) := by
    simp [WordSemStateFiniteExact.getVars,WordSemStateFiniteExact.getVar,ret,wordGet]
  have targetClock : t.clock ≠ 0 := by rw [hclock]; exact clock
  obtain ⟨_,_,_,_,_,calleeBound⟩ := bodyProp res final
    (WordSemStateFiniteExact.callEnv args ss (WordSemStateFiniteExact.decClock t))
    calleeCtxt retv calleeLabels ⟨bodyRun,nonerror,
      ⟨len,hm,hmd,hsmd,by simp [WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.decClock,
        LoopSemStateFiniteExact.decClock,hclock],hbe,hffi,hcur,hlen,htop,hglob,hcode⟩,
      hcalleelocals,hret,dim,notWord,hacc⟩
  have wordSteps := WordSteps.steps_call_tail (some loc) (0 :: vars.map (LoopToWord.findVarHOL ctxt)) t (retv :: vals) args ss
    (LoopToWord.compHOL calleeCtxt body calleeLabels).1 wordArgs (by simp [wordSemBadDestArgs])
    wordFound targetClock
  have loopSteps := LoopSteps.steps_call_tail (some loc) vars s vals env body get found clock
  simp only [LoopToWord.compHOL] at ⊢
  rw [wordSteps,loopSteps]
  omega

/-- The zero-clock call times out at the call node on both sides. -/
theorem sixBoundedDirectTail {width : Nat} [NeZero width] {C F : Type}
    (loc : Nat) (vars : List Nat) (vals : List (WordLocW width)) (env : Spt (WordLocW width))
    (body : HolLoopProg width) (s : LoopSemStateFiniteExact width F)
    (bodyProp : s.clock ≠ 0 → SixBoundPropertyAt C body {decClock s with locals := env})
    (get : getVars vars s = some vals) (found : findCode (some loc) vals s.code = some (env,body)) :
    SixBoundPropertyAt C (.call none (some loc) vars none) s := by
  by_cases clock : s.clock = 0
  · intro res final t ctxt retv labels premises
    obtain ⟨run,nonerror,state,locals,ret,dim,notWord,acc⟩ := premises
    have qualitative := compileCorrect_Call_TailCall (C := C) (some loc) vars none s
      (by intro vals pair env prog h; exact False.elim (h.2.2.2.2.2 clock))
      res final t ctxt retv labels ⟨run,nonerror,state,locals,ret,dim,notWord,acc⟩
    obtain ⟨tf,rf,evalTarget,ffi,relation⟩ := qualitative
    refine ⟨tf,rf,evalTarget,ffi,relation,?_⟩
    obtain ⟨len,hm,hmd,hsmd,hclock,hbe,hffi,hcur,hlen,htop,hglob,hcode⟩ := state
    obtain ⟨args,ss,calleeCtxt,calleeLabels,wordFound,hret,hcalleelocals,hacc⟩ :=
      findCode_rel s.code t.code t.stackSize (some loc) vals env body retv hcode found
    obtain ⟨wordGet, _⟩ := LoopToWord.localsRelHOLGetVars ctxt s t vars vals ⟨locals,get⟩
    have wordArgs : WordSemStateFiniteExact.getVars (0 :: vars.map (LoopToWord.findVarHOL ctxt)) t = some (retv :: vals) := by
      simp [WordSemStateFiniteExact.getVars,WordSemStateFiniteExact.getVar,ret,wordGet]
    have targetClock : t.clock = 0 := by rw [hclock]; exact clock
    have wordSteps : WordSteps.steps (.call none (some loc) (0 :: vars.map (LoopToWord.findVarHOL ctxt)) none) t = 1 := by
      rw [WordSteps.steps.eq_def]
      simp [wordArgs,wordSemBadDestArgs,wordSemAddRetLoc,wordFound,targetClock]
    have loopSteps : LoopSteps.steps (.call none (some loc) vars none) s = 1 := by
      rw [LoopSteps.steps.eq_def]
      simp [get,found,clock]
    simp only [LoopToWord.compHOL]
    rw [wordSteps,loopSteps]
    omega
  · exact sixBoundedDirectTail_nonzero loc vars vals env body s (bodyProp clock) get found clock

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
  | nestedLoop live exits h ih => exact .loop live exits ih
  | conditional cmp r ri live ha hb iha ihb => exact .ite cmp r ri live iha ihb

/-- A single-destination entry has the sixfold bound when its reached callee
is supported; successful prefixes preserve the lookup needed by the call. -/
theorem singleTailEntry_correct_with_steps {width : Nat} [NeZero width] {C F : Type}
    {loc : Nat} {p : HolLoopProg width} (shape : LoopLiveSteps.SingleTailEntryShape loc p)
    (body : HolLoopProg width) (bodyShape : LoopProgram body) :
    ∀ s : LoopSemStateFiniteExact width F,
      findCode (some loc) [] s.code = some (.ln,body) → SixBoundPropertyAt C p s := by
  induction shape with
  | branch h => intro s _; exact loopProgram_correct_with_steps (loopBranch_program h) s
  | call => intro s found; exact sixBoundedDirectTail loc [] [] .ln body s (fun _ => loopProgram_correct_with_steps bodyShape _) rfl found
  | @seq a b ha hb iha ihb =>
    intro s found
    apply sixBoundedSeq a b s
    refine ⟨?_,iha s found⟩
    intro res middle h
    obtain ⟨first,rfl⟩ := h
    have codeEq := LoopLiveSteps.evaluate_code a s middle none first.symm
    exact ihb middle (by simpa only [codeEq] using found)
  | @mark p hp ih =>
    intro s found
    exact sixBoundedMark p s (ih s found)

/-- A reached Word call with compiler-generated raise/skip continuations costs
at most its callee plus two visits. -/
theorem wordReturning_generated_steps {width : Nat} [NeZero width] {C F : Type}
    (dest : Option Nat) (args names : List Nat) (cuts : WordLangCutsetsHOL)
    (l1 l2 h1 h2 exc : Nat) (s middle : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) (xs values : List (WordLocW width))
    (ss : Option Nat) (callee : WordLangProgHOL (BitVec width))
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (hargs : WordSemStateFiniteExact.getVars args s = some xs)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest (wordSemAddRetLoc (some (names,cuts,(WordLangProgHOL.skip : WordLangProgHOL (BitVec width)),l1,l2)) xs)
      s.code s.stackSize = some (values,callee,ss))
    (hvalid : ¬ (sptDomainEmpty cuts.1 ∨ ¬ names.Nodup))
    (hcut : wordSemCutEnvs cuts s.locals = some envs) (hclock : s.clock ≠ 0)
    (run : WordSemStateFiniteExact.evaluate callee
      (WordSemStateFiniteExact.callEnv values ss
        (WordSemStateFiniteExact.pushEnv envs (some (exc,.raise exc,h1,h2)) (WordSemStateFiniteExact.decClock s))) = (res,middle)) :
    WordSteps.steps (.call (some (names,cuts,.skip,l1,l2)) dest args (some (exc,.raise exc,h1,h2))) s ≤
      2 + WordSteps.steps callee (WordSemStateFiniteExact.callEnv values ss
        (WordSemStateFiniteExact.pushEnv envs (some (exc,.raise exc,h1,h2)) (WordSemStateFiniteExact.decClock s))) := by
  have count := WordSteps.steps_call_returning dest args names cuts .skip l1 l2
    (some (exc,.raise exc,h1,h2)) s middle res xs values ss callee envs hargs hbad hfind hvalid hcut hclock run
  rw [count]
  cases res with
  | none => simp
  | some r =>
    cases r <;> try simp
    case result addr ys =>
      split <;> try omega
      split <;> try omega
      split <;> try omega
      all_goals rw [WordSteps.steps_leaf WordLangProgHOL.skip _ (by rfl)]; omega
    case exception addr value =>
      split <;> try omega
      split <;> try omega
      all_goals rw [WordSteps.steps_leaf (WordLangProgHOL.raise exc) _ (by rfl)]; omega

/-- The post-call tick and sequence add at most two Word visits. -/
theorem wordReturning_generated_wrapper {width : Nat} [NeZero width] {C F : Type}
    (dest : Option Nat) (args names : List Nat) (cuts : WordLangCutsetsHOL)
    (l1 l2 h1 h2 exc : Nat) (s middle : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) (xs values : List (WordLocW width))
    (ss : Option Nat) (callee : WordLangProgHOL (BitVec width))
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (hargs : WordSemStateFiniteExact.getVars args s = some xs)
    (hbad : wordSemBadDestArgs dest args = false)
    (hfind : wordSemFindCode dest (wordSemAddRetLoc (some (names,cuts,(WordLangProgHOL.skip : WordLangProgHOL (BitVec width)),l1,l2)) xs)
      s.code s.stackSize = some (values,callee,ss))
    (hvalid : ¬ (sptDomainEmpty cuts.1 ∨ ¬ names.Nodup))
    (hcut : wordSemCutEnvs cuts s.locals = some envs) (hclock : s.clock ≠ 0)
    (run : WordSemStateFiniteExact.evaluate callee
      (WordSemStateFiniteExact.callEnv values ss
        (WordSemStateFiniteExact.pushEnv envs (some (exc,.raise exc,h1,h2)) (WordSemStateFiniteExact.decClock s))) = (res,middle)) :
    WordSteps.steps (.seq (.call (some (names,cuts,.skip,l1,l2)) dest args (some (exc,.raise exc,h1,h2))) .tick) s ≤
      4 + WordSteps.steps callee (WordSemStateFiniteExact.callEnv values ss
        (WordSemStateFiniteExact.pushEnv envs (some (exc,.raise exc,h1,h2)) (WordSemStateFiniteExact.decClock s))) := by
  have call := wordReturning_generated_steps dest args names cuts l1 l2 h1 h2 exc s middle res xs values ss callee envs
    hargs hbad hfind hvalid hcut hclock run
  rw [WordSteps.steps_seq]
  rcases WordSemStateFiniteExact.evaluate (.call (some (names,cuts,.skip,l1,l2)) dest args (some (exc,.raise exc,h1,h2))) s with ⟨r,t⟩
  cases r <;> simp only <;> try omega
  rw [WordSteps.steps_leaf WordLangProgHOL.tick _ (by rfl)]
  omega
/-- The actual compiled ordinary call has the sixfold bound when the reached
callee has it. The source and target execution facts are the local call
simulation facts used by the surrounding compiler induction. -/
theorem compiledReturning_steps_from_callee {width : Nat} [NeZero width] {C F : Type}
    (loc : Nat) (args names : List Nat) (live liveOut : NumSet) (exception : Nat)
    (markHandler markNormal : Bool)
    (source sourceCut sourcePost : LoopSemStateFiniteExact width F)
    (sourceVals : List (WordLocW width)) (sourceEnv : Spt (WordLocW width))
    (body : HolLoopProg width) (out : Option (LoopResultExact width))
    (target targetPost : WordSemStateFiniteExact width C F) (ctxt : Spt Nat) (labels : Nat × Nat)
    (targetResult : Option (WordSemResult width)) (wordVals wordEnv : List (WordLocW width))
    (ss : Option Nat) (wordBody : WordLangProgHOL (BitVec width))
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (sourceGet : getVars args source = some sourceVals)
    (sourceFound : findCode (some loc) sourceVals source.code = some (sourceEnv,body))
    (sourceDistinct : names.Nodup) (sourceCutRun : cutRes live (none,source) = (none,sourceCut))
    (sourceRun : evaluate body {sourceCut with locals := sourceEnv} = (out,sourcePost))
    (targetGet : WordSemStateFiniteExact.getVars (args.map (findVarHOL ctxt)) target = some wordVals)
    (targetFound : wordSemFindCode (some loc)
      (wordSemAddRetLoc (some (names.map (findVarHOL ctxt), (mkNewCutsetHOL ctxt live,(Spt.ln : NumSet)),
        (WordLangProgHOL.skip : WordLangProgHOL (BitVec width)),labels.1,labels.2)) wordVals)
      target.code target.stackSize = some (wordEnv,wordBody,ss))
    (targetValid : ¬ (sptDomainEmpty (mkNewCutsetHOL ctxt live) ∨ ¬ (names.map (findVarHOL ctxt)).Nodup))
    (targetCut : wordSemCutEnvs (mkNewCutsetHOL ctxt live,(Spt.ln : NumSet)) target.locals = some envs)
    (targetClock : target.clock ≠ 0)
    (targetRun : WordSemStateFiniteExact.evaluate wordBody
      (WordSemStateFiniteExact.callEnv wordEnv ss
        (WordSemStateFiniteExact.pushEnv envs (some (findVarHOL ctxt exception,
          .raise (findVarHOL ctxt exception),labels.1,labels.2+1)) (WordSemStateFiniteExact.decClock target))) =
      (targetResult,targetPost))
    (calleeBound : WordSteps.steps wordBody
      (WordSemStateFiniteExact.callEnv wordEnv ss
        (WordSemStateFiniteExact.pushEnv envs (some (findVarHOL ctxt exception,
          .raise (findVarHOL ctxt exception),labels.1,labels.2+1)) (WordSemStateFiniteExact.decClock target))) ≤
      6 * LoopSteps.steps body {sourceCut with locals := sourceEnv}) :
    WordSteps.steps (LoopToWord.compHOL ctxt
      (.call (some (names,live)) (some loc) args (some (exception,if markHandler then .mark (.raise exception) else .raise exception,
          if markNormal then .mark .skip else .skip,liveOut))) labels).1 target ≤
      6 * LoopSteps.steps (.call (some (names,live)) (some loc) args
        (some (exception,if markHandler then .mark (.raise exception) else .raise exception,
          if markNormal then .mark .skip else .skip,liveOut))) source := by
  cases labels with
  | mk lab1 lab2 =>
   have wordBound := wordReturning_generated_wrapper (some loc) (args.map (findVarHOL ctxt))
     (names.map (findVarHOL ctxt)) (mkNewCutsetHOL ctxt live,(Spt.ln : NumSet)) lab1 lab2 lab1 (lab2+1)
     (findVarHOL ctxt exception) target targetPost targetResult wordVals wordEnv ss wordBody envs
     targetGet (by simp [wordSemBadDestArgs]) targetFound targetValid targetCut targetClock targetRun
   have loopCount := LoopSteps.steps_call_returning (some loc) args names live
     (some (exception,if markHandler then .mark (.raise exception) else .raise exception,
          if markNormal then .mark .skip else .skip,liveOut)) source sourceCut sourcePost sourceVals sourceEnv body out
     sourceGet sourceFound sourceDistinct sourceCutRun sourceRun
   have loopLower : 1 + LoopSteps.steps body {sourceCut with locals := sourceEnv} ≤
       LoopSteps.steps (.call (some (names,live)) (some loc) args
         (some (exception,if markHandler then .mark (.raise exception) else .raise exception,
          if markNormal then .mark .skip else .skip,liveOut))) source := by
     rw [loopCount]
     omega
   cases markHandler <;> cases markNormal <;>
     simp only [Bool.false_eq_true,if_false,if_true,LoopToWord.compHOL] at loopLower ⊢ <;>
     simp only at calleeBound <;> omega


end SteppedFlapjack.LoopToWordSteps
