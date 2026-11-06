import SteppedFlapjack.WordToStackSteps.WholeProgram
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompileSemantics
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Install

/-! Whole-program Word/Stack initialization relation. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordToStack.Native.Initialization
open Flapjack.Compiler.Backend.WordToWord SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordSimpSteps
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.InitializationStateRel

/-- The actual whole Word output and native Stack output satisfy the original
initial Word/Stack relation under the native initialization contract. -/
theorem wholeWordStack_initStateRel {width : Nat} [NeZero width] {C F : Type}
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (asmConf : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (t : StackSemStateFiniteExact width C F)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (noRaiseInput : raiseStubLocation ∉ programs.map Prod.fst)
    (noStoreInput : storeConstsStubLocation ∉ programs.map Prod.fst)
    (codeEq : t.code = sptFromAList (compileNative asmConf false (compile wc asmConf programs).2).2.2.2)
    (bitmapsPrefix : (compileNative asmConf false (compile wc asmConf programs).2).1.IsPrefix t.bitmaps)
    (ok : initStateOk asmConf (asmConf.regCount-(5+asmConf.avoidRegs.length)) t coracle) :
    stateRel asmConf (asmConf.regCount-(5+asmConf.avoidRegs.length)) 0 0
      (makeInit asmConf (asmConf.regCount-(5+asmConf.avoidRegs.length)) t
        (sptFromAList (compile wc asmConf programs).2) coracle : WordSemStateFiniteExact width (Nat × C) F)
      t [] 0 := by
  let code := (compile wc asmConf programs).2
  have names : code.map Prod.fst = programs.map Prod.fst := wholeCompile_names wc asmConf programs
  have noRaise : panPropsALookupEq raiseStubLocation code = none := by
    cases h : panPropsALookupEq raiseStubLocation code with
    | none => rfl
    | some value =>
      have member := Flapjack.WordToStackProofs.CompCorrect.Install.mem_of_panPropsALookupEq h
      have : raiseStubLocation ∈ code.map Prod.fst := List.mem_map.mpr ⟨_,member,rfl⟩
      rw [names] at this
      exact False.elim (noRaiseInput this)
  have noStore : panPropsALookupEq storeConstsStubLocation code = none := by
    cases h : panPropsALookupEq storeConstsStubLocation code with
    | none => rfl
    | some value =>
      have member := Flapjack.WordToStackProofs.CompCorrect.Install.mem_of_panPropsALookupEq h
      have : storeConstsStubLocation ∈ code.map Prod.fst := List.mem_map.mpr ⟨_,member,rfl⟩
      rw [names] at this
      exact False.elim (noStoreInput this)
  have conventions : ∀ entry ∈ code, flatExpConventions entry.2.2 = true ∧
      postAllocConventionsHOL (asmConf.regCount-(5+asmConf.avoidRegs.length)) entry.2.2 = true :=
    wholeCompile_conventions wc asmConf programs
  change t.code = sptFromAList (compileNative asmConf false code).2.2.2 at codeEq
  change (compileNative asmConf false code).1.IsPrefix t.bitmaps at bitmapsPrefix
  rcases compiled : compileWordToStackNative asmConf false
      (asmConf.regCount - (5 + asmConf.avoidRegs.length)) code (.list [4], 1) with
    ⟨bodies, frames, output, nextIndex⟩
  simp only [compileNative, Bool.false_eq_true, if_false, compiled] at codeEq bitmapsPrefix
  have keys := mapFstCompileWordToStack asmConf false _ code (.list [4], 1) bodies
    (frames, (output, nextIndex)) compiled
  have stubsDistinct : raiseStubLocation ≠ storeConstsStubLocation := by
    simp [raiseStubLocation, storeConstsStubLocation, wordNumStubs]
  have related : stateRel asmConf (asmConf.regCount - (5 + asmConf.avoidRegs.length)) 0 0
      (makeInit asmConf (asmConf.regCount - (5 + asmConf.avoidRegs.length)) t (sptFromAList code)
        coracle : WordSemStateFiniteExact width (Nat × C) F)
      t [] 0 := by
    apply initStateOkImpliesStateRel
    refine ⟨?_, ?_, ?_, ?_, ok⟩
    · rw [codeEq, sptLookup_sptFromAList, Flapjack.WordToStackProofs.CompCorrect.Install.sptAListLookup_eq_panPropsALookupEq]
      simp [panPropsALookupEq]
    · rw [codeEq, sptLookup_sptFromAList, Flapjack.WordToStackProofs.CompCorrect.Install.sptAListLookup_eq_panPropsALookupEq]
      simp [panPropsALookupEq, stubsDistinct]
    · intro n wordProg argumentCount lookup
      rw [sptLookup_sptFromAList, Flapjack.WordToStackProofs.CompCorrect.Install.sptAListLookup_eq_panPropsALookupEq] at lookup
      have member := Flapjack.WordToStackProofs.CompCorrect.Install.mem_of_panPropsALookupEq lookup
      obtain ⟨flat, allocated⟩ := conventions _ member
      obtain ⟨bs, i, bs2, i2, frame, body, compileRun, b1, b2, b3, bodyLookup⟩ :=
        compileWordToStackImpALookup asmConf false _ code (.list [4]) 1 bodies frames output
          nextIndex n argumentCount wordProg t.bitmaps compiled lookup
          (by simp [appListAppend, appendAux]) (by simp [appListAppend, appendAux])
          (by simpa [appListAppend, appendAux] using bitmapsPrefix)
      refine ⟨allocated, flat, bs, i, bs2, i2, frame, body, compileRun, b1, b2, b3, ?_⟩
      have notRaise : n ≠ raiseStubLocation := by
        rintro rfl
        rw [noRaise] at lookup
        cases lookup
      have notStore : n ≠ storeConstsStubLocation := by
        rintro rfl
        rw [noStore] at lookup
        cases lookup
      rw [codeEq, sptLookup_sptFromAList, Flapjack.WordToStackProofs.CompCorrect.Install.sptAListLookup_eq_panPropsALookupEq]
      simp [panPropsALookupEq, Ne.symm notRaise, Ne.symm notStore, bodyLookup]
    · rw [codeEq, sptDomainFromAList, sptDomainFromAList]
      funext x
      simp only [List.map_cons, List.mem_cons, keys]
  exact related

/-- Native initialization and the entry simulation use the same actual
whole-program output, including its oracle and bitmap witnesses. -/
theorem wholeWordStack_initialized_entry {width : Nat} [NeZero width] {C F : Type}
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (name count : Nat) (p : WordLangProgHOL (BitVec width)) (member : (name,count,p) ∈ programs)
    (nodup : (programs.map Prod.fst).Nodup) (shape : LoopSequence p)
    (t : StackSemStateFiniteExact width C F)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (noRaise : raiseStubLocation ∉ programs.map Prod.fst) (noStore : storeConstsStubLocation ∉ programs.map Prod.fst)
    (codeEq : t.code = sptFromAList (compileNative ac false (compile wc ac programs).2).2.2.2)
    (bitmapsPrefix : (compileNative ac false (compile wc ac programs).2).1.IsPrefix t.bitmaps)
    (ok : initStateOk ac (ac.regCount-(5+ac.avoidRegs.length)) t coracle) :
    stateRel ac (ac.regCount-(5+ac.avoidRegs.length)) 0 0
      (makeInit ac (ac.regCount-(5+ac.avoidRegs.length)) t (sptFromAList (compile wc ac programs).2) coracle :
        WordSemStateFiniteExact width (Nat × C) F) t [] 0 ∧
    ∃ col q bs n bsPost nPost body frame frameSize,
      q = (fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac ((name,count,p),col)).2.2 ∧
      LoopBlock q ∧ noInstallSubprogsHOL q = true ∧ flatExpConventions q = true ∧
      postAllocConventionsHOL (ac.regCount-(5+ac.avoidRegs.length)) q = true ∧
      frame = max (maxVarHOL q / 2 + 1 - (ac.regCount-(5+ac.avoidRegs.length))) (count-(ac.regCount-(5+ac.avoidRegs.length))) ∧
      frameSize = (if frame = 0 then 0 else frame+1) ∧
      compNative ac false q (bs,n) (ac.regCount-(5+ac.avoidRegs.length),frameSize,frame) = (body,(bsPost,nPost)) ∧
      sptLookup name t.code = some (compileProgNative ac false q count (ac.regCount-(5+ac.avoidRegs.length)) (bs,n)).1 ∧
      (appListAppend bs).length ≤ n ∧ n-(appListAppend bs).length ≤ t.bitmaps.length ∧
      (appListAppend bsPost).IsPrefix (t.bitmaps.drop (n-(appListAppend bs).length)) := by
  have nameMember : name ∈ programs.map Prod.fst := List.mem_map.mpr ⟨_,member,rfl⟩
  have notRaise : name ≠ raiseStubLocation := by intro h; subst name; exact noRaise nameMember
  have notStore : name ≠ storeConstsStubLocation := by intro h; subst name; exact noStore nameMember
  exact ⟨wholeWordStack_initStateRel wc ac programs t coracle noRaise noStore codeEq bitmapsPrefix ok,
    wholeWordStack_initialized_inputs wc ac programs name count p member nodup notRaise notStore shape t codeEq bitmapsPrefix⟩

end SteppedFlapjack.WordToStackSteps
