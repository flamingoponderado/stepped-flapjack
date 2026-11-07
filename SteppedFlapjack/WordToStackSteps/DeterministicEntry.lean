import SteppedFlapjack.WordToStackSteps.WholeProgram

/-! Executable selection of a native entry's accumulated bitmap state. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Backend.WordToWord
open SteppedFlapjack.WordSimpSteps

/-- Bitmap state immediately before the first native compilation of a key. -/
def nativeEntryBitmap {width : Nat} [NeZero width] {β : Type} [DecidableEq β]
    (ac : AsmConfigExact width) (perf : Bool) (registers : Nat)
    (identifier : β) : List (β × Nat × WordLangProgHOL (BitVec width)) →
      (AppList (BitVec width) × Nat) → Option (AppList (BitVec width) × Nat)
  | [], _ => none
  | (name,count,program)::rest, state =>
      if name = identifier then some state
      else nativeEntryBitmap ac perf registers identifier rest
        (compileProgNative ac perf program count registers state).2.2

/-- The executable lookup returns the bitmap state that produces the actual
first-matching body and satisfies the compiler's bitmap accounting. -/
theorem nativeEntryBitmap_correct {width : Nat} [NeZero width] {β : Type} [DecidableEq β]
    (ac : AsmConfigExact width) (perf : Bool) (registers : Nat)
    (rows : List (β × Nat × WordLangProgHOL (BitVec width)))
    (bm : AppList (BitVec width)) (index : Nat)
    (bodies : List (β × HolProg width)) (frames : List Nat)
    (output : AppList (BitVec width)) (nextIndex : Nat)
    (identifier : β) (arguments : Nat) (program : WordLangProgHOL (BitVec width))
    (x : List (BitVec width))
    (compiled : compileWordToStackNative ac perf registers rows (bm,index) =
      (bodies,frames,output,nextIndex))
    (source : panPropsALookupEq identifier rows = some (arguments,program))
    (bound : (appListAppend bm).length ≤ index)
    (gapBound : index - (appListAppend bm).length ≤ x.length)
    (finalPrefix : (appListAppend output).IsPrefix (x.drop (index - (appListAppend bm).length))) :
    ∃ (start : AppList (BitVec width)) (startIndex : Nat)
      (finish : AppList (BitVec width)) (finishIndex frame : Nat) (body : HolProg width),
      nativeEntryBitmap ac perf registers identifier rows (bm,index) = some (start,startIndex) ∧
      compileProgNative ac perf program arguments registers (start,startIndex) = (body,frame,finish,finishIndex) ∧
      (appListAppend start).length ≤ startIndex ∧
      startIndex - (appListAppend start).length ≤ x.length ∧
      (appListAppend finish).IsPrefix (x.drop (startIndex - (appListAppend start).length)) ∧
      panPropsALookupEq identifier bodies = some body := by
  induction rows generalizing bm index bodies frames output nextIndex with
  | nil => simp [panPropsALookupEq] at source
  | cons row rows ih =>
    rcases row with ⟨name,argc,prog⟩
    rcases hp : compileProgNative ac perf prog argc registers (bm,index) with ⟨body,frame,nextBm,nextI⟩
    rcases ht : compileWordToStackNative ac perf registers rows (nextBm,nextI) with ⟨tailBodies,tailFrames,finalBm,finalI⟩
    have equation : ((name,body)::tailBodies,frame::tailFrames,finalBm,finalI) =
        (bodies,frames,output,nextIndex) := by
      simpa only [compileWordToStackNative,hp,ht] using compiled
    cases equation
    by_cases heq : name = identifier
    · have selected : argc = arguments ∧ prog = program := by
        simpa [panPropsALookupEq,heq] using source
      rcases selected with ⟨rfl,rfl⟩
      have tailPrefix := compileWordToStackIsPrefix ac perf registers rows
        (nextBm,nextI) tailBodies tailFrames (output,nextIndex) ht
      refine ⟨bm,index,nextBm,nextI,frame,body,?_,hp,bound,gapBound,tailPrefix.trans finalPrefix,?_⟩
      · simp [nativeEntryBitmap,heq]
      · simp [panPropsALookupEq,heq]
    · have tailSource : panPropsALookupEq identifier rows = some (arguments,program) := by
        simpa [panPropsALookupEq,heq] using source
      obtain ⟨nextBound,gap⟩ := compileProgLength ac perf prog argc registers
        bm index body frame nextBm nextI ⟨hp,bound⟩
      have nextGapBound : nextI - (appListAppend nextBm).length ≤ x.length := by
        simpa only [← gap] using gapBound
      have nextPrefix : (appListAppend output).IsPrefix
          (x.drop (nextI - (appListAppend nextBm).length)) := by
        simpa only [← gap] using finalPrefix
      obtain ⟨start,startI,finish,finishI,f,result,entry,hc,hb,hg,hpfx,hl⟩ :=
        ih nextBm nextI tailBodies tailFrames output nextIndex ht tailSource nextBound nextGapBound nextPrefix
      refine ⟨start,startI,finish,finishI,f,result,?_,hc,hb,hg,hpfx,?_⟩
      · simpa [nativeEntryBitmap,heq,hp] using entry
      · simpa [panPropsALookupEq,heq] using hl

/-- The native top-level entry's bitmap state is computed by the lookup above. -/
theorem compileNative_entry_bitmap_deterministic {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (name count : Nat) (p : WordLangProgHOL (BitVec width)) (member : (name,count,p) ∈ programs)
    (nodup : (programs.map Prod.fst).Nodup)
    (notRaise : name ≠ raiseStubLocation) (notStore : name ≠ storeConstsStubLocation) :
    ∃ bs n bsPost nPost body frame,
      nativeEntryBitmap ac false (ac.regCount-(5+ac.avoidRegs.length)) name programs (.list [4],1) = some (bs,n) ∧
      compileProgNative ac false p count (ac.regCount-(5+ac.avoidRegs.length)) (bs,n) = (body,frame,bsPost,nPost) ∧
      sptLookup name (sptFromAList (compileNative ac false programs).2.2.2) = some body ∧
      (appListAppend bs).length ≤ n ∧
      n-(appListAppend bs).length ≤ (compileNative ac false programs).1.length ∧
      (appListAppend bsPost).IsPrefix ((compileNative ac false programs).1.drop (n-(appListAppend bs).length)) := by
  let k := ac.regCount-(5+ac.avoidRegs.length)
  have sourceLookup : panPropsALookupEq name programs = some (count,p) := by
    rw [← Flapjack.WordToStackProofs.CompCorrect.Install.sptAListLookup_eq_panPropsALookupEq]
    exact sptAListLookup_of_mem_nodup programs name (count,p) nodup member
  rcases compiled : compileWordToStackNative ac false k programs (.list [4],1) with ⟨bodies,frames,output,next⟩
  obtain ⟨bs,n,bsPost,nPost,frame,body,selected,bodyCompiled,lengthBound,gapBound,bitmapPrefix,bodyLookup⟩ :=
    nativeEntryBitmap_correct ac false k programs (.list [4]) 1 bodies frames output next name count p
      (appListAppend output) compiled sourceLookup (by simp [appListAppend,appendAux])
      (by simp [appListAppend,appendAux]) (by simp [appListAppend,appendAux])
  dsimp only [k] at compiled
  simp only [compileNative, Bool.false_eq_true, if_false, compiled]
  refine ⟨bs,n,bsPost,nPost,body,frame,selected,bodyCompiled,?_,lengthBound,gapBound,bitmapPrefix⟩
  rw [sptLookup_sptFromAList]
  change sptAListLookup name ((raiseStubLocation,raiseStubNative false k) ::
    (storeConstsStubLocation,storeConstsStubNative k) :: bodies) = _
  simp only [sptAListLookup,if_neg notRaise,if_neg notStore]
  rw [Flapjack.WordToStackProofs.CompCorrect.Install.sptAListLookup_eq_panPropsALookupEq]
  exact bodyLookup

/-- Word compilation and native compilation jointly determine the entry bitmap state. -/
theorem wholeWordStack_entry_bitmap_deterministic {width : Nat} [NeZero width]
    (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (name count : Nat) (p : WordLangProgHOL (BitVec width)) (member : (name,count,p) ∈ programs)
    (nodup : (programs.map Prod.fst).Nodup)
    (notRaise : name ≠ raiseStubLocation) (notStore : name ≠ storeConstsStubLocation) :
    let code := (Flapjack.Compiler.Backend.WordToWord.compile wc ac programs).2
    let q := (Flapjack.Compiler.Backend.WordToWord.fullCompileSingle ac.twoRegArith
      (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac
      ((name,count,p),SteppedFlapjack.WordAllocSteps.entryColour wc programs name)).2.2
    ∃ bs n bsPost nPost body frame,
      nativeEntryBitmap ac false (ac.regCount-(5+ac.avoidRegs.length)) name code (.list [4],1) = some (bs,n) ∧
      compileProgNative ac false q count (ac.regCount-(5+ac.avoidRegs.length)) (bs,n) = (body,frame,bsPost,nPost) ∧
      sptLookup name (sptFromAList (compileNative ac false code).2.2.2) = some body ∧
      (appListAppend bs).length ≤ n ∧ n-(appListAppend bs).length ≤ (compileNative ac false code).1.length ∧
      (appListAppend bsPost).IsPrefix ((compileNative ac false code).1.drop (n-(appListAppend bs).length)) := by
  have outputMember := SteppedFlapjack.WordAllocSteps.wholeCompile_contains_entryColour wc ac programs name count p member nodup
  have eq : Flapjack.Compiler.Backend.WordToWord.fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac
      ((name,count,p),SteppedFlapjack.WordAllocSteps.entryColour wc programs name) =
      (name,count,(Flapjack.Compiler.Backend.WordToWord.fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac
        ((name,count,p),SteppedFlapjack.WordAllocSteps.entryColour wc programs name)).2.2) := by
    simp [Flapjack.Compiler.Backend.WordToWord.fullCompileSingle,Flapjack.Compiler.Backend.WordToWord.compileSingle]
  rw [eq] at outputMember
  have outputNodup : (((Flapjack.Compiler.Backend.WordToWord.compile wc ac programs).2).map Prod.fst).Nodup := by
    rw [SteppedFlapjack.WordAllocSteps.wholeCompile_names wc ac programs]
    exact nodup
  exact compileNative_entry_bitmap_deterministic ac _ name count _ outputMember outputNodup notRaise notStore

end SteppedFlapjack.WordToStackSteps
