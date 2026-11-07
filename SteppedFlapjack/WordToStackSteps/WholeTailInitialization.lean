import SteppedFlapjack.WordToStackSteps.WholeInitialization
import SteppedFlapjack.WordToStackSteps.DeterministicEntry

/-! Native frame and bitmap witnesses for arbitrary compiler-selected entries. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Backend.WordToWord
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordAllocSteps
open Flapjack.WordSemStateFiniteExact Flapjack.WordAlloc Flapjack.WordToStackProofs
open Flapjack.Compiler.Backend.WordToStack.Native.Initialization
open Flapjack.WordToStackProofs.InitializationStateRel
variable {width : Nat} [NeZero width]

/-- The actual Stack compiler supplies frame and bitmap witnesses for the
selected Word output, including entries containing calls. -/
theorem wholeWordStack_entryColour_native_inputs (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : AsmConfigExact width) (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (name count : Nat) (p : WordLangProgHOL (BitVec width)) (member : (name,count,p) ∈ programs)
    (nodup : (programs.map Prod.fst).Nodup)
    (notRaise : name ≠ raiseStubLocation) (notStore : name ≠ storeConstsStubLocation)
    :
    let q := (fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac
      ((name,count,p),entryColour wc programs name)).2.2
    ∃ bs n bsPost nPost body frame frameSize,
      nativeEntryBitmap ac false (ac.regCount-(5+ac.avoidRegs.length)) name (compile wc ac programs).2 (.list [4],1) = some (bs,n) ∧
      frame = max (maxVarHOL q / 2 + 1 - (ac.regCount-(5+ac.avoidRegs.length))) (count-(ac.regCount-(5+ac.avoidRegs.length))) ∧
      frameSize = (if frame = 0 then 0 else frame+1) ∧
      compNative ac false q (bs,n) (ac.regCount-(5+ac.avoidRegs.length),frameSize,frame) = (body,(bsPost,nPost)) ∧
      sptLookup name (sptFromAList (compileNative ac false (compile wc ac programs).2).2.2.2) =
        some (.seq (.stackAlloc (frameSize-(count-(ac.regCount-(5+ac.avoidRegs.length))))) body) ∧
      sptLookup name (sptFromAList (compileNative ac false (compile wc ac programs).2).2.2.2) =
        some (compileProgNative ac false q count (ac.regCount-(5+ac.avoidRegs.length)) (bs,n)).1 ∧
      (appListAppend bs).length ≤ n ∧
      n-(appListAppend bs).length ≤ (compileNative ac false (compile wc ac programs).2).1.length ∧
      (appListAppend bsPost).IsPrefix ((compileNative ac false (compile wc ac programs).2).1.drop (n-(appListAppend bs).length)) := by
  let col := entryColour wc programs name
  let q := (fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac ((name,count,p),col)).2.2
  obtain ⟨bs,n,bsPost,nPost,entry,frameSize,selected,programCompiled,lookup,lengthBound,gapBound,bitmapPrefix⟩ :=
    wholeWordStack_entry_bitmap_deterministic wc ac programs name count p member nodup notRaise notStore
  let k := ac.regCount-(5+ac.avoidRegs.length)
  let frame := max (maxVarHOL q / 2 + 1 - k) (count-k)
  let size := if frame = 0 then 0 else frame+1
  rcases h : compNative ac false q (bs,n) (k,size,frame) with ⟨body,bm⟩
  rcases bm with ⟨after,afterN⟩
  have hp : compileProgNative ac false q count k (bs,n) =
      (.seq (.stackAlloc (size-(count-k))) body,size,after,afterN) := by
    change (Flapjack.Compiler.Backend.StackLang.Prog.seq (.stackAlloc (size-(count-k))) (compNative ac false q (bs,n) (k,size,frame)).1,
      size,(compNative ac false q (bs,n) (k,size,frame)).2) = _
    rw [h]
  rw [hp] at programCompiled
  simp only [Prod.mk.injEq] at programCompiled
  obtain ⟨rfl,rfl,rfl,rfl⟩ := programCompiled
  have found : sptLookup name (sptFromAList (compileNative ac false (compile wc ac programs).2).2.2.2) =
      some (compileProgNative ac false q count k (bs,n)).1 := by
    rw [hp]
    exact lookup
  exact ⟨bs,n,after,afterN,body,frame,size,
    selected,rfl,rfl,h,lookup,found,lengthBound,gapBound,bitmapPrefix⟩


/-- An initialized native Stack state supplies the code lookup, frame and
bitmap premises for the exact Word entry chosen by the whole compiler. -/
theorem wholeWordStack_tail_initialized_inputs {C F : Type}
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (name count : Nat) (p : WordLangProgHOL (BitVec width)) (member : (name,count,p) ∈ programs)
    (nodup : (programs.map Prod.fst).Nodup) (t : StackSemStateFiniteExact width C F)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (noRaise : raiseStubLocation ∉ programs.map Prod.fst) (noStore : storeConstsStubLocation ∉ programs.map Prod.fst)
    (codeEq : t.code = sptFromAList (compileNative ac false (compile wc ac programs).2).2.2.2)
    (bitmapsPrefix : (compileNative ac false (compile wc ac programs).2).1.IsPrefix t.bitmaps)
    (ok : initStateOk ac (ac.regCount-(5+ac.avoidRegs.length)) t coracle) :
    let k := ac.regCount-(5+ac.avoidRegs.length)
    let q := (fullCompileSingle ac.twoRegArith k wc.regAlg ac ((name,count,p),entryColour wc programs name)).2.2
    stateRel ac k 0 0 (makeInit ac k t (sptFromAList (compile wc ac programs).2) coracle :
      WordSemStateFiniteExact width (Nat × C) F) t [] 0 ∧
    ∃ bs n bsPost nPost body frame frameSize,
      nativeEntryBitmap ac false (ac.regCount-(5+ac.avoidRegs.length)) name (compile wc ac programs).2 (.list [4],1) = some (bs,n) ∧
      frame = max (maxVarHOL q / 2 + 1 - k) (count-k) ∧
      frameSize = (if frame = 0 then 0 else frame+1) ∧
      compNative ac false q (bs,n) (k,frameSize,frame) = (body,(bsPost,nPost)) ∧
      sptLookup name t.code = some (compileProgNative ac false q count k (bs,n)).1 ∧
      (appListAppend bs).length ≤ n ∧ n-(appListAppend bs).length ≤ t.bitmaps.length ∧
      (appListAppend bsPost).IsPrefix (t.bitmaps.drop (n-(appListAppend bs).length)) := by
  have nameMember : name ∈ programs.map Prod.fst := List.mem_map.mpr ⟨_,member,rfl⟩
  have notRaise : name ≠ raiseStubLocation := by intro h; subst name; exact noRaise nameMember
  have notStore : name ≠ storeConstsStubLocation := by intro h; subst name; exact noStore nameMember
  obtain ⟨bs,n,bsPost,nPost,body,frame,frameSize,selected,frameDef,sizeDef,compilation,_,found,lengthBound,gapBound,bitmapPrefix⟩ :=
    wholeWordStack_entryColour_native_inputs wc ac programs name count p member nodup notRaise notStore
  refine ⟨wholeWordStack_initStateRel wc ac programs t coracle noRaise noStore codeEq bitmapsPrefix ok,
    bs,n,bsPost,nPost,body,frame,frameSize,selected,frameDef,sizeDef,compilation,?_,lengthBound,
    gapBound.trans bitmapsPrefix.length_le,?_⟩
  · simpa only [codeEq] using found
  · exact bitmapPrefix.trans (bitmapsPrefix.drop _)

end SteppedFlapjack.WordToStackSteps
