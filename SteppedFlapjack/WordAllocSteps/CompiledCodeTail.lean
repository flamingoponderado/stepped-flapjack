import SteppedFlapjack.WordToStackSteps.DirectTailLocal
import Flapjack.Compiler.Backend.WordToWord.Proofs.NoInstallCompileSingle

/-! Transfer tail-entry callee facts to the actually compiled code table. -/
namespace SteppedFlapjack.WordAllocSteps
open Flapjack Flapjack.Compiler.Backend.WordToWord Flapjack.WordSemStateFiniteExact Flapjack.WordProps
open Flapjack.Compiler.Encoders.Asm Flapjack.WordConvs Flapjack.Compiler.Backend.WordAlloc
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.LoopLiveSteps SteppedFlapjack.StackRemoveSteps.CompCorrect
variable {width : Nat} [NeZero width]

/-- A finite upper bound on the syntax size of code entries. -/
noncomputable def wordCodeSize (code : Spt (Nat × WordLangProgHOL (BitVec width))) : Nat :=
  maxListNat ((sptToAList code).map fun entry => sizeOf entry.2.2)

omit [NeZero width] in
/-- Every code body is bounded by the maximum computed from the actual table. -/
theorem wordCodeSize_bound (code : Spt (Nat × WordLangProgHOL (BitVec width)))
    (loc arity : Nat) (p : WordLangProgHOL (BitVec width))
    (lookup : sptLookup loc code = some (arity,p)) : sizeOf p ≤ wordCodeSize code := by
  have hlist : sptAListLookup loc (sptToAList code) = some (arity,p) := by
    have h := sptLookup_sptFromAList_sptToAList loc code
    rw [lookup] at h
    simpa only [sptLookup_sptFromAList] using h
  have member := Flapjack.sptAListLookup_mem loc (sptToAList code) (arity,p) hlist
  apply le_maxListNat_of_mem
  exact List.mem_map.mpr ⟨(loc,arity,p),member,rfl⟩

/-- The actual single-function Word compiler keeps call-free loop sequences
in that fragment, before the final must-terminate cleanup. -/
theorem compileSingle_loopSequence (flag : Bool) (k alg name arity : Nat)
    (ac : Flapjack.Compiler.Encoders.Asm.AsmConfigExact width) (col : Option (Spt Nat))
    {p : WordLangProgHOL (BitVec width)} (shape : LoopSequence p) :
    LoopSequence (compileSingle flag k alg ac ((name,arity,p),col)).2.2 := by
  change LoopSequence (Flapjack.WordAlloc.wordAlloc name ac alg k (preAlloc ac flag arity p) col)
  exact wordAlloc_loopSequence name ac alg k col (preAlloc_shape ac flag arity shape)

/-- Related compiled code tables preserve each required direct callee shape;
the new size bound is computed from the actual compiled table. -/
theorem compiled_tailEntry_codeBound {p : WordLangProgHOL (BitVec width)}
    (source target : Spt (Nat × WordLangProgHOL (BitVec width))) (K : Nat)
    (codeRel : Flapjack.Compiler.Backend.WordToWord.codeRel source target)
    (bound : TailEntryCodeBound p source K) : TailEntryCodeBound p target (wordCodeSize target) := by
  intro loc call
  obtain ⟨callee,lookup,shape,_⟩ := bound loc call
  obtain ⟨col,flag,k,alg,ac,compiled⟩ := codeRel loc (1,callee) lookup
  let out := (compileSingle flag k alg ac ((loc,1,callee),col)).2.2
  have targetLookup : sptLookup loc target = some (1,out) := by simpa [out,compileSingle] using compiled
  exact ⟨out,targetLookup,compileSingle_loopSequence flag k alg loc 1 ac col shape,
    wordCodeSize_bound target loc 1 out targetLookup⟩

open Classical in
/-- Without dynamic installation, the code-table replacement theorem does
not require a global no-allocation property. -/
theorem noInstall_codeRel_correct {C F : Type}
    (prog : WordLangProgHOL (BitVec width)) (st : WordSemStateFiniteExact width C F)
    (l : Spt (Nat × WordLangProgHOL (BitVec width)))
    (hrel : codeRel st.code l) (hni : noInstallSubprogsHOL prog = true)
    (hnic : noInstallCode st.code) (hdom : sptDomain st.code = sptDomain l)
    (hgc : Flapjack.Compiler.Backend.WordSimp.gcFunConstOk st.gcFun) :
    ∃ perm' : Nat → Nat → Nat,
      let (res,rst) := evaluate prog {st with permute := perm'}
      if res = some .error then True else
        let (res1,rst1) := evaluate prog {st with code := l}
        res1 = res ∧ codeRel rst.code rst1.code ∧ sptDomain rst.code = sptDomain rst1.code ∧
          rst1 = {rst with code := rst1.code} := by
  let co : AsmConfigExact width := ⟨.riscv, fun _ => [], false, 0, none, [], 0, 0, false,
    fun _ _ => false, (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)⟩
  let cs := fun p : Nat × Nat × WordLangProgHOL (BitVec width) => compileSingle false 0 0 co (p, none)
  let cc0 : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) →
      Option (List (BitVec 8) × List (BitVec width) × C) := fun _ _ => none
  let C' : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) →
      Option (List (BitVec 8) × List (BitVec width) × C) := fun conf progs => cc0 conf (progs.map cs)
  let O2 := Prod.map id (List.map cs) ∘ st.compileOracle
  let st' := cfState st.compileOracle C' st
  obtain ⟨perm', H⟩ := compile_single_correct false 0 0 co prog st' l O2 cc0 ⟨hrel, hdom, rfl, rfl, hgc⟩
  refine ⟨perm', ?_⟩
  have hnil : noInstallCode l := noInstallCode_of_codeRel st.code l hrel hdom hnic
  rcases hS : evaluate prog { st with permute := perm' } with ⟨res, rst⟩
  have hA := evaluate_compileFields_frame st.compileOracle C' prog { st with permute := perm' } hni hnic
  have hSc := evaluate_compileFields_const prog { st with permute := perm' } hni hnic
  rw [hS] at hA hSc
  change evaluate prog { st' with permute := perm' } = (res, cfState st.compileOracle C' rst) at hA
  rw [hA] at H
  dsimp only at H
  dsimp only
  by_cases herr : res = some .error
  · simp [herr]
  rw [if_neg herr] at H ⊢
  rcases hT : evaluate prog { st with code := l } with ⟨res1, rst1⟩
  have hB := evaluate_compileFields_frame O2 cc0 prog { st with code := l } hni hnil
  have hTc := evaluate_compileFields_const prog { st with code := l } hni hnil
  rw [hT] at hB hTc
  change evaluate prog { st' with code := l, compileOracle := O2, compile := cc0 } =
    (res1, cfState O2 cc0 rst1) at hB
  rw [hB] at H
  dsimp only at H
  dsimp only
  obtain ⟨hres, hcr, hd, heq⟩ := H
  refine ⟨hres, hcr, hd, ?_⟩
  obtain ⟨hTo, hTcc⟩ := hTc
  obtain ⟨hSo, hScc⟩ := hSc
  cases rst1
  cases rst
  simp only [cfState, WordSemStateFiniteExact.mk.injEq] at heq hTo hTcc hSo hScc ⊢
  simp_all
/-- A completed supported tail entry can run against the related compiled
code table with the same result, clock and FFI state. The only potentially
different state fields are the code table and permutation oracle. -/
theorem tailEntry_codeRel_run {C F : Type} {p : WordLangProgHOL (BitVec width)}
    (shape : WordTailEntryShape p) (s post : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) (target : Spt (Nat × WordLangProgHOL (BitVec width))) (K : Nat)
    (code : TailEntryCodeBound p s.code K) (noInstall : noInstallCode s.code)
    (rel : codeRel s.code target) (domain : sptDomain s.code = sptDomain target)
    (gc : Flapjack.Compiler.Backend.WordSimp.gcFunConstOk s.gcFun)
    (run : evaluate p s = (res,post)) (nonerror : res ≠ some .error) :
    ∃ perm, evaluate p {s with code := target} = (res,{post with code := target,permute := perm}) := by
  obtain ⟨perm,correct⟩ := noInstall_codeRel_correct p s target rel (tailEntry_noInstall shape) noInstall domain gc
  have permRun := SteppedFlapjack.WordSsaSteps.tailEntry_withPermute shape s perm K noInstall code
  rw [run] at permRun
  simp only at permRun
  rw [permRun] at correct
  simp only [if_neg nonerror] at correct
  rcases targetRun : evaluate p {s with code := target} with ⟨result,targetPost⟩
  rw [targetRun] at correct
  simp only at correct
  obtain ⟨resultEq,_,_,stateEq⟩ := correct
  have targetNoInstall := noInstallCode_of_codeRel s.code target rel domain noInstall
  have preserved := WordSemStateFiniteExact.code_evaluate p {s with code := target} (tailEntry_noInstall shape) targetNoInstall
  rw [targetRun] at preserved
  simp only at preserved
  subst result
  refine ⟨perm,?_⟩
  rw [stateEq,preserved]

/-- Normalize a completed source run, replace its code table by the actual
related compiled table, and bound the resulting entry visits. -/
theorem tailEntry_compiledCode_run_bound {C F : Type} {p : WordLangProgHOL (BitVec width)}
    (shape : WordTailEntryShape p) (s post : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) (target : Spt (Nat × WordLangProgHOL (BitVec width))) (K limit : Nat)
    (code : TailEntryCodeBound p s.code K) (noInstall : noInstallCode s.code)
    (rel : codeRel s.code target) (domain : sptDomain s.code = sptDomain target)
    (gc : Flapjack.Compiler.Backend.WordSimp.gcFunConstOk s.gcFun)
    (run : evaluate p s = (res,post)) (nonerror : res ≠ some .error) (notTimeout : res ≠ some .timeOut)
    (sourceBound : SteppedFlapjack.WordSteps.steps p s ≤ limit) :
    ∃ perm, evaluate p {s with code := target,clock := limit} =
        (res,{post with code := target,permute := perm,clock := limit-(s.clock-post.clock)}) ∧
      TailEntryCodeBound p target (wordCodeSize target) ∧
      SteppedFlapjack.WordSteps.steps p {s with code := target,clock := limit} ≤
        sizeOf p * (wordCodeSize target+1) * (limit+1) := by
  have normalized := tailEntry_normalized_run shape s post res K limit (tailEntry_noInstall shape)
    noInstall code run nonerror notTimeout sourceBound
  obtain ⟨perm,swapped⟩ := tailEntry_codeRel_run shape {s with clock := limit}
    {post with clock := limit-(s.clock-post.clock)} res target K code noInstall rel domain gc normalized nonerror
  have targetCode := compiled_tailEntry_codeBound s.code target K rel code
  have targetNoInstall := noInstallCode_of_codeRel s.code target rel domain noInstall
  have steps := tailEntry_clock_bound shape {s with code := target,clock := limit} (wordCodeSize target)
    (tailEntry_noInstall shape) targetNoInstall targetCode
  exact ⟨perm,swapped,targetCode,steps⟩

/-- The ordinary single-function compiler produces flat Word code for every
input, independent of the selected allocator branch. -/
theorem compileSingle_flat (flag : Bool) (k alg name arity : Nat) (ac : AsmConfigExact width)
    (col : Option (Spt Nat)) (p : WordLangProgHOL (BitVec width)) :
    flatExpConventions (compileSingle flag k alg ac ((name,arity,p),col)).2.2 = true := by
  change flatExpConventions (Flapjack.WordAlloc.wordAlloc name ac alg k (preAlloc ac flag arity p) col) = true
  apply wordAlloc_flatExpConventions
  unfold preAlloc
  apply (removeDeadProgConventions (fun _ => true) _ ac).1
  apply flatExpConventions_removeUnreach
  apply threeToTwoRegProg_flatExpConventions
  apply flat_exp_conventions_copy_prop
  apply flat_exp_conventions_word_common_subexp_elim
  apply (removeDeadProgConventions (fun _ => true) _ ac).1
  apply Flapjack.WordAlloc.fullSsaCcTrans_flatExpConventions
  exact instSelect_flatExpConventions _ _ _

/-- Every entry in the related compiled table is flat; this follows from code
relation and equal domains, independent of unrelated source body shapes. -/
theorem codeRel_target_flat (source target : Spt (Nat × WordLangProgHOL (BitVec width)))
    (rel : codeRel source target) (domain : sptDomain source = sptDomain target) :
    ∀ loc arity q, sptLookup loc target = some (arity,q) → flatExpConventions q = true := by
  intro loc arity q found
  have present : sptDomain source loc := by rw [domain]; simp [sptDomain,found]
  cases h : sptLookup loc source with
  | none => simp [sptDomain,h] at present
  | some entry =>
    obtain ⟨sourceArity,body⟩ := entry
    obtain ⟨col,flag,k,alg,ac,compiled⟩ := rel loc (sourceArity,body) h
    have eq := Option.some.inj (found.symm.trans compiled)
    have bodyEq : q = (compileSingle flag k alg ac ((loc,sourceArity,body),col)).2.2 := congrArg Prod.snd eq
    rw [bodyEq]
    exact compileSingle_flat flag k alg loc sourceArity ac col body

/-- The local Stack simulation condition follows from the allocated entry's
callee shape and the flatness of its compiled code table. -/
theorem regTail_localCode_of_flat {p : WordLangProgHOL (BitVec width)}
    (code : Spt (Nat × WordLangProgHOL (BitVec width))) (K : Nat)
    (bound : RegTailCodeBound p code K)
    (flat : ∀ loc arity q, sptLookup loc code = some (arity,q) → flatExpConventions q = true) :
    SteppedFlapjack.WordToStackSteps.RegTailLocalCode p code := by
  intro loc call
  obtain ⟨callee,lookup,shape,_⟩ := bound loc call
  exact ⟨1,callee,lookup,flat_loopSequence_block shape (flat loc 1 callee lookup)⟩

/-- Execute the actual fully compiled entry on its actual compiled code table.
The source visit limit determines the replay clock and the compiled-table
size determines the derived intermediate visit limit. -/
theorem fullCompileSingle_compiledCode_tailEntry_correct {C F : Type}
    (ac : AsmConfigExact width) (flag : Bool) (count fc alg k : Nat) (col : Option (Spt Nat))
    {p : WordLangProgHOL (BitVec width)} (shape : WordTailEntryShape p)
    (s post : WordSemStateFiniteExact width C F) (res : Option (WordSemResult width))
    (target : Spt (Nat × WordLangProgHOL (BitVec width))) (K limit : Nat) (locals : Spt (WordLocW width))
    (code : TailEntryCodeBound p s.code K) (noInstall : noInstallCode s.code)
    (rel : codeRel s.code target) (domainCode : sptDomain s.code = sptDomain target)
    (gc : Flapjack.Compiler.Backend.WordSimp.gcFunConstOk s.gcFun)
    (run : evaluate p s = (res,post)) (nonerror : res ≠ some .error) (notTimeout : res ≠ some .timeOut)
    (sourceBound : SteppedFlapjack.WordSteps.steps p s ≤ limit)
    (localsRel : wordLocalsRel (maxVarHOL (Flapjack.Compiler.Backend.WordSimp.compileExp p)+1) s.locals locals)
    (domainLocals : sptDomain locals = (fun key => key ∈ evenList count)) :
    let out := (fullCompileSingle flag k alg ac ((fc,count,p),col)).2.2
    let intermediate := sizeOf p * (wordCodeSize target+1) * (limit+1)
    RegTailShape out ∧ SteppedFlapjack.WordToStackSteps.RegTailLocalCode out target ∧
    noInstallSubprogsHOL out = true ∧ flatExpConventions out = true ∧ postAllocConventionsHOL k out = true ∧
    ∃ perm selectedLocals targetPost,
      evaluate out {s with code := target,locals := locals,clock := intermediate} = (res,targetPost) ∧
      Flapjack.WordAlloc.wordStateEqRel
        {post with code := target,permute := perm,locals := selectedLocals,clock := intermediate-(limit-(limit-(s.clock-post.clock)))} targetPost ∧
      SteppedFlapjack.WordSteps.steps out {s with code := target,locals := locals,clock := intermediate} ≤
        sizeOf out * (wordCodeSize target+1) * (intermediate+1) := by
  let intermediate := sizeOf p * (wordCodeSize target+1) * (limit+1)
  obtain ⟨perm,swapped,targetCode,swappedBound⟩ := tailEntry_compiledCode_run_bound shape s post res target K limit
    code noInstall rel domainCode gc run nonerror notTimeout sourceBound
  have targetNoInstall := noInstallCode_of_codeRel s.code target rel domainCode noInstall
  obtain ⟨outShape,_,outNoInstall,outFlat,outConvention,selectedLocals,targetPost,targetRun,targetRel,outCode,bound⟩ :=
    fullCompileSingle_tailEntry_correct ac flag count fc alg k col shape
      {s with code := target,clock := limit} {post with code := target,permute := perm,clock := limit-(s.clock-post.clock)}
      res (wordCodeSize target) intermediate locals targetNoInstall targetCode swapped nonerror notTimeout
      swappedBound gc localsRel domainLocals
  have targetFlat := codeRel_target_flat s.code target rel domainCode
  have localCode := regTail_localCode_of_flat target (wordCodeSize target) outCode targetFlat
  exact ⟨outShape,localCode,outNoInstall,outFlat,outConvention,perm,selectedLocals,targetPost,targetRun,targetRel,bound⟩

end SteppedFlapjack.WordAllocSteps
