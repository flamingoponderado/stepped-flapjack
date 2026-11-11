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


/-- A successful Loop call cut and the compiler relations determine the Word
call's argument lookup, callee, cut environment, and callee-entry relations. -/
theorem returningCall_word_setup {width : Nat} [NeZero width] {C F : Type}
    (loc : Nat) (args names : List Nat) (live : NumSet)
    (s cut : LoopSemStateFiniteExact width F) (vals : List (WordLocW width))
    (env : Spt (WordLocW width)) (body : HolLoopProg width)
    (t : WordSemStateFiniteExact width C F) (ctxt : Spt Nat) (retv : WordLocW width)
    (labels : Nat × Nat) (exc : Nat) (sourceGet : getVars args s = some vals)
    (sourceFound : findCode (some loc) vals s.code = some (env,body))
    (distinct : names.Nodup) (sourceCut : cutRes live (none,s) = (none,cut))
    (state : loopToWordStateRelHOLExact s t) (locals : localsRelHOL ctxt s.locals t.locals)
    (ret : sptLookup 0 t.locals = some retv)
    (namesInCtxt : ∀ k, k ∈ names → sptMem k ctxt) :
    ∃ wordArgs ss calleeCtxt calleeLabels saved,
      WordSemStateFiniteExact.getVars (args.map (findVarHOL ctxt)) t = some vals ∧
      wordSemFindCode (some loc) (.loc labels.1 labels.2 :: vals) t.code t.stackSize =
        some (wordArgs,(compHOL calleeCtxt body calleeLabels).1,ss) ∧
      ¬ (sptDomainEmpty (mkNewCutsetHOL ctxt live) ∨ ¬ (names.map (findVarHOL ctxt)).Nodup) ∧
      wordSemCutEnvs (mkNewCutsetHOL ctxt live,(Spt.ln : NumSet)) t.locals = some (saved,.ln) ∧
      t.clock ≠ 0 ∧
      let calleeState := WordSemStateFiniteExact.callEnv wordArgs ss
        (WordSemStateFiniteExact.pushEnv (saved,.ln)
          (some (findVarHOL ctxt exc,.raise (findVarHOL ctxt exc),labels.1,labels.2+1))
          (WordSemStateFiniteExact.decClock t))
      loopToWordStateRelHOLExact {cut with locals := env} calleeState ∧
      localsRelHOL calleeCtxt env calleeState.locals ∧
      sptLookup 0 calleeState.locals = some (.loc labels.1 labels.2) ∧
      (∀ k, sptMem k (accVarsHOL body .ln) → sptMem k calleeCtxt) := by
  have cutFacts : ∃ cs, cutState live s = some cs ∧ s.clock ≠ 0 ∧ cut = decClock cs := by
    unfold cutRes at sourceCut
    simp only at sourceCut
    cases hc : cutState live s with
    | none => rw [hc] at sourceCut; simp at sourceCut
    | some cs =>
      simp only [hc] at sourceCut
      have hcClock : cs.clock = s.clock := cutState_clock hc
      by_cases hz : s.clock = 0
      · simp [hcClock,hz] at sourceCut
      · simp only [hcClock,hz,if_false,Prod.mk.injEq,true_and] at sourceCut
        exact ⟨cs,rfl,hz,sourceCut.symm⟩
  obtain ⟨cs,hcs,nonzero,rfl⟩ := cutFacts
  have subset : sptSubsetLive live s.locals ∧ cs = {s with locals := sptInter s.locals live} := by
    unfold cutState at hcs
    split at hcs
    · exact ⟨‹_›,(Option.some.inj hcs).symm⟩
    · cases hcs
  obtain ⟨subset,rfl⟩ := subset
  obtain ⟨len,hm,hmd,hsmd,hclock,hbe,hffi,hcur,hlen,htop,hglob,hcode⟩ := state
  obtain ⟨wordGet,_⟩ := localsRelHOLGetVars ctxt s t args vals ⟨locals,sourceGet⟩
  obtain ⟨wordArgs,ss,calleeCtxt,calleeLabels,wordFound,calleeRet,calleeLocals,calleeAcc⟩ :=
    findCode_rel s.code t.code t.stackSize (some loc) vals env body (.loc labels.1 labels.2) hcode sourceFound
  obtain ⟨saved,hce,savedRel⟩ := wordSemCutEnvMkNewCutsetHOL ctxt live s.locals t.locals retv ⟨locals,subset,ret⟩
  have cutEnvs := wordSemCutEnvLNIMPHOL _ _ _ hce
  have cutNonempty : ¬ sptDomainEmpty (mkNewCutsetHOL ctxt live) := fun h =>
    domainMkNewCutsetNotEmpty ctxt live (funext fun k => propext ⟨fun hk => h k hk,False.elim⟩)
  have mappedDistinct : (names.map (findVarHOL ctxt)).Nodup :=
    localsRelHOLAllDistinctMap ctxt s.locals t.locals names ⟨locals,namesInCtxt,distinct⟩
  have targetClock : t.clock ≠ 0 := by rw [hclock]; exact nonzero
  refine ⟨wordArgs,ss,calleeCtxt,calleeLabels,saved,wordGet,wordFound,?_,cutEnvs,targetClock,?_,?_,?_,calleeAcc⟩
  · simp [cutNonempty,mappedDistinct]
  · exact ⟨len,hm,hmd,hsmd,by simp [WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.pushEnv,
        WordSemStateFiniteExact.decClock,LoopSemStateFiniteExact.decClock,hclock],hbe,hffi,hcur,hlen,htop,hglob,hcode⟩
  · simpa [WordSemStateFiniteExact.callEnv] using calleeLocals
  · simpa [WordSemStateFiniteExact.callEnv] using calleeRet
/-- Every return variable is in the compiler context when the call's
accessed-variable condition holds. -/
theorem returningCall_names_in_context {width : Nat} [NeZero width]
    (loc : Nat) (args names : List Nat) (live liveOut : NumSet) (exc : Nat)
    (handler normal : HolLoopProg width) (ctxt : Spt Nat)
    (acc : ∀ k, sptMem k (accVarsHOL
      (.call (some (names,live)) (some loc) args (some (exc,handler,normal,liveOut))) .ln) → sptMem k ctxt) :
    ∀ k, k ∈ names → sptMem k ctxt := by
  intro k member
  apply acc
  have e1 := congrFun (accVarsAccHOL handler
    (accVarsHOL normal (sptInsert exc () (sptListInsert names .ln)))) k
  have e2 := congrFun (accVarsAccHOL normal (sptInsert exc () (sptListInsert names .ln))) k
  simp only [accVarsHOL]
  change sptDomain _ k
  rw [e1]
  change sptMem k (accVarsHOL handler .ln) ∨ sptDomain _ k
  rw [e2]
  change sptMem k (accVarsHOL handler .ln) ∨ sptMem k (accVarsHOL normal .ln) ∨ sptDomain _ k
  change sptMem k (accVarsHOL handler .ln) ∨ sptMem k (accVarsHOL normal .ln) ∨
    sptMem k (sptInsert exc () (sptListInsert names .ln))
  rw [sptMem_sptInsert,sptMem_sptListInsert_iff]
  simp [member]

/-- A non-error returning-call run cannot have an erroring callee. -/
theorem returningCall_callee_nonerror {width : Nat} [NeZero width] {F : Type}
    (loc : Nat) (args names : List Nat) (live liveOut : NumSet) (exc : Nat)
    (handler normal : HolLoopProg width) (s cut post final : LoopSemStateFiniteExact width F)
    (vals : List (WordLocW width)) (env : Spt (WordLocW width)) (body : HolLoopProg width)
    (out result : Option (LoopResultExact width))
    (get : getVars args s = some vals) (found : findCode (some loc) vals s.code = some (env,body))
    (distinct : names.Nodup) (cutRun : cutRes live (none,s) = (none,cut))
    (bodyRun : evaluate body {cut with locals := env} = (out,post))
    (run : evaluate (.call (some (names,live)) (some loc) args (some (exc,handler,normal,liveOut))) s = (result,final))
    (nonerror : result ≠ some .error) : out ≠ some .error := by
  intro bad
  rw [evaluate] at run
  simp only [get,found,distinct,not_true_eq_false,if_false] at run
  rw [cutRun] at run
  simp only at run
  rw [fix_clock_evaluate,bodyRun,bad] at run
  simp only [Prod.mk.injEq] at run
  exact nonerror run.1.symm

/-- A reached returning call has the sixfold Word visit bound whenever its
callee satisfies the compiler induction property. -/
theorem sixBoundedReturning_reached {width : Nat} [NeZero width] {C F : Type}
    (loc : Nat) (args names : List Nat) (live liveOut : NumSet) (exc : Nat)
    (markHandler markNormal : Bool)
    (s cut post : LoopSemStateFiniteExact width F) (vals : List (WordLocW width))
    (env : Spt (WordLocW width)) (body : HolLoopProg width) (out : Option (LoopResultExact width))
    (t : WordSemStateFiniteExact width C F) (ctxt : Spt Nat) (retv : WordLocW width) (labels : Nat × Nat)
    (sourceGet : getVars args s = some vals)
    (sourceFound : findCode (some loc) vals s.code = some (env,body))
    (distinct : names.Nodup) (sourceCut : cutRes live (none,s) = (none,cut))
    (bodyRun : evaluate body {cut with locals := env} = (out,post))
    (sourceResult : Option (LoopResultExact width)) (sourceFinal : LoopSemStateFiniteExact width F)
    (sourceRun : evaluate (.call (some (names,live)) (some loc) args
      (some (exc,if markHandler then .mark (.raise exc) else .raise exc,
        if markNormal then .mark .skip else .skip,liveOut))) s = (sourceResult,sourceFinal))
    (nonerror : sourceResult ≠ some .error)
    (bodyProp : SixBoundPropertyAt C body {cut with locals := env})
    (state : loopToWordStateRelHOLExact s t) (locals : localsRelHOL ctxt s.locals t.locals)
    (ret : sptLookup 0 t.locals = some retv) (dim : goodDimindex width)
    (acc : ∀ k, sptMem k (accVarsHOL
      (.call (some (names,live)) (some loc) args
        (some (exc,if markHandler then .mark (.raise exc) else .raise exc,
          if markNormal then .mark .skip else .skip,liveOut)) : HolLoopProg width) .ln) → sptMem k ctxt) :
    WordSteps.steps (compHOL ctxt
      (.call (some (names,live)) (some loc) args
        (some (exc,if markHandler then .mark (.raise exc) else .raise exc,
          if markNormal then .mark .skip else .skip,liveOut))) labels).1 t ≤
      6 * LoopSteps.steps (.call (some (names,live)) (some loc) args
        (some (exc,if markHandler then .mark (.raise exc) else .raise exc,
          if markNormal then .mark .skip else .skip,liveOut))) s := by
  have bodyNonerror := returningCall_callee_nonerror loc args names live liveOut exc _ _
    s cut post sourceFinal vals env body out sourceResult sourceGet sourceFound distinct sourceCut bodyRun sourceRun nonerror
  obtain ⟨wordArgs,ss,calleeCtxt,calleeLabels,saved,targetGet,targetFound,targetValid,targetCut,targetClock,
    calleeState,calleeLocals,calleeRet,calleeAcc⟩ :=
    returningCall_word_setup loc args names live s cut vals env body t ctxt retv labels exc
      sourceGet sourceFound distinct sourceCut state locals ret
      (returningCall_names_in_context loc args names live liveOut exc _ _ ctxt acc)
  obtain ⟨targetPost,targetResult,targetRun,_,_,calleeBound⟩ := bodyProp out post
    (WordSemStateFiniteExact.callEnv wordArgs ss
      (WordSemStateFiniteExact.pushEnv (saved,.ln)
        (some (findVarHOL ctxt exc,.raise (findVarHOL ctxt exc),labels.1,labels.2+1))
        (WordSemStateFiniteExact.decClock t))) calleeCtxt (.loc labels.1 labels.2) calleeLabels
    ⟨bodyRun,bodyNonerror,calleeState,calleeLocals,calleeRet,dim,by simp [wordSemIsWordLoc],calleeAcc⟩
  have targetFound' : wordSemFindCode (some loc)
      (wordSemAddRetLoc (some (names.map (findVarHOL ctxt), (mkNewCutsetHOL ctxt live,(Spt.ln : NumSet)),
        (WordLangProgHOL.skip : WordLangProgHOL (BitVec width)),labels.1,labels.2)) vals)
      t.code t.stackSize = some (wordArgs,(compHOL calleeCtxt body calleeLabels).1,ss) := by
    simpa [wordSemAddRetLoc] using targetFound
  exact compiledReturning_steps_from_callee loc args names live liveOut exc markHandler markNormal
    s cut post vals env body out t targetPost ctxt labels targetResult vals wordArgs ss
    (compHOL calleeCtxt body calleeLabels).1 (saved,.ln)
    sourceGet sourceFound distinct sourceCut bodyRun targetGet targetFound' targetValid targetCut targetClock targetRun calleeBound

/-- A returning call with a successful source cut inherits semantic
correctness and the sixfold visit bound from the reached callee. -/
theorem sixBoundedReturning_success {width : Nat} [NeZero width] {C F : Type}
    (loc : Nat) (args names : List Nat) (live liveOut : NumSet) (exc : Nat)
    (markHandler markNormal : Bool)
    (s cut post : LoopSemStateFiniteExact width F) (vals : List (WordLocW width))
    (env : Spt (WordLocW width)) (body : HolLoopProg width) (out : Option (LoopResultExact width))
    (sourceGet : getVars args s = some vals)
    (sourceFound : findCode (some loc) vals s.code = some (env,body))
    (distinct : names.Nodup) (sourceCut : cutRes live (none,s) = (none,cut))
    (bodyRun : evaluate body {cut with locals := env} = (out,post))
    (bodyProp : SixBoundPropertyAt C body {cut with locals := env}) :
    SixBoundPropertyAt C (.call (some (names,live)) (some loc) args
      (some (exc,if markHandler then .mark (.raise exc) else .raise exc,
        if markNormal then .mark .skip else .skip,liveOut))) s := by
  intro result final target ctxt retv labels premises
  obtain ⟨run,nonerror,state,locals,ret,dim,notWord,acc⟩ := premises
  obtain ⟨targetFinal,targetResult,targetRun,ffi,relation⟩ :=
    compileCorrect _ s result final target ctxt retv labels ⟨run,nonerror,state,locals,ret,dim,notWord,acc⟩
  refine ⟨targetFinal,targetResult,targetRun,ffi,relation,?_⟩
  exact sixBoundedReturning_reached loc args names live liveOut exc markHandler markNormal
    s cut post vals env body out target ctxt retv labels sourceGet sourceFound distinct sourceCut bodyRun
    result final run nonerror bodyProp state locals ret dim acc

/-- A Word returning call at zero clock cannot visit a callee. -/
theorem wordReturning_zero_steps {width : Nat} [NeZero width] {C F : Type}
    (dest : Option Nat) (args names : List Nat) (cuts : WordLangCutsetsHOL)
    (normal : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) (zero : s.clock = 0) :
    WordSteps.steps (.call (some (names,cuts,normal,l1,l2)) dest args handler) s = 1 := by
  rw [WordSteps.steps.eq_def]
  simp only [zero,if_true]
  repeat' split <;> simp_all

/-- At zero clock the generated ordinary-call wrapper has the sixfold bound. -/
theorem sixBoundedReturning_zero {width : Nat} [NeZero width] {C F : Type}
    (loc : Nat) (args names : List Nat) (live liveOut : NumSet) (exc : Nat)
    (markHandler markNormal : Bool) (s : LoopSemStateFiniteExact width F) (zero : s.clock = 0) :
    SixBoundPropertyAt C (.call (some (names,live)) (some loc) args
      (some (exc,if markHandler then .mark (.raise exc) else .raise exc,
        if markNormal then .mark .skip else .skip,liveOut))) s := by
  intro result final target ctxt retv labels premises
  obtain ⟨run,nonerror,state,locals,ret,dim,notWord,acc⟩ := premises
  obtain ⟨targetFinal,targetResult,targetRun,ffi,relation⟩ :=
    compileCorrect _ s result final target ctxt retv labels ⟨run,nonerror,state,locals,ret,dim,notWord,acc⟩
  refine ⟨targetFinal,targetResult,targetRun,ffi,relation,?_⟩
  obtain ⟨_,_,_,_,clock,_,_,_,_,_,_,_⟩ := state
  have targetZero : target.clock = 0 := by rw [clock]; exact zero
  have positive := LoopSteps.steps_pos (.call (some (names,live)) (some loc) args
    (some (exc,if markHandler then .mark (.raise exc) else .raise exc,
      if markNormal then .mark .skip else .skip,liveOut))) s
  cases labels with
  | mk l1 l2 =>
    cases markHandler <;> cases markNormal <;> simp only [Bool.false_eq_true,if_false,if_true,LoopToWord.compHOL] at ⊢
    all_goals rw [WordSteps.steps_seq]
    all_goals rw [wordReturning_zero_steps _ _ _ _ _ _ _ _ target targetZero]
    all_goals rcases WordSemStateFiniteExact.evaluate _ target with ⟨r,st⟩
    all_goals cases r <;> simp only
    all_goals simp only [Bool.false_eq_true,if_false,if_true] at positive
    all_goals try omega
    all_goals rw [WordSteps.steps_leaf WordLangProgHOL.tick _ (by rfl)]
    all_goals omega

/-- Direct returning calls, including timeout and failed cuts, inherit the
compiler's sixfold bound from their reached callee. -/
theorem sixBoundedDirectReturning {width : Nat} [NeZero width] {C F : Type}
    (loc : Nat) (args names : List Nat) (live liveOut : NumSet) (exc : Nat)
    (markHandler markNormal : Bool) (s : LoopSemStateFiniteExact width F)
    (vals : List (WordLocW width)) (env : Spt (WordLocW width)) (body : HolLoopProg width)
    (sourceGet : getVars args s = some vals)
    (sourceFound : findCode (some loc) vals s.code = some (env,body))
    (distinct : names.Nodup)
    (bodyProp : ∀ cut, cutRes live (none,s) = (none,cut) →
      SixBoundPropertyAt C body {cut with locals := env}) :
    SixBoundPropertyAt C (.call (some (names,live)) (some loc) args
      (some (exc,if markHandler then .mark (.raise exc) else .raise exc,
        if markNormal then .mark .skip else .skip,liveOut))) s := by
  by_cases zero : s.clock = 0
  · exact sixBoundedReturning_zero loc args names live liveOut exc markHandler markNormal s zero
  · rcases cutRun : cutRes live (none,s) with ⟨cutResult,cut⟩
    cases cutResult with
    | none =>
      rcases bodyRun : evaluate body {cut with locals := env} with ⟨out,post⟩
      exact sixBoundedReturning_success loc args names live liveOut exc markHandler markNormal
        s cut post vals env body out sourceGet sourceFound distinct cutRun bodyRun (bodyProp cut cutRun)
    | some r =>
      have cutError : r = .error := by
        unfold cutRes at cutRun
        cases hc : cutState live s with
        | none => simp [hc] at cutRun; exact cutRun.1.symm
        | some cs =>
          have clock := cutState_clock hc
          simp [hc,clock,zero] at cutRun
      subst r
      intro result final target ctxt retv labels premises
      obtain ⟨run,nonerror,_⟩ := premises
      rw [evaluate] at run
      simp only [sourceGet,sourceFound,distinct,not_true_eq_false,if_false] at run
      rw [cutRun] at run
      simp only [Prod.mk.injEq] at run
      exact False.elim (nonerror run.1.symm)


end SteppedFlapjack.LoopToWordSteps
