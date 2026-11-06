import SteppedFlapjack.WordAllocSteps.WholeProgram
import Flapjack.Compiler.Backend.WordToStack.NativeTopCompile
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompileKeys
import Flapjack.Compiler.Backend.WordToWord.Proofs.Syntactic
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompileLookup
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Install

/-! Whole-program Word-to-Stack entry identification. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native Flapjack.Compiler.Backend.WordToWord
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.WordAllocSteps SteppedFlapjack.WordSteps
open Flapjack.WordSemStateFiniteExact Flapjack.WordAlloc
open Flapjack.Compiler.Backend.WordSimp Flapjack.Compiler.Backend.WordInst
open Flapjack.Compiler.Backend.WordAlloc
variable {width : Nat} [NeZero width]

/-- Each function is compiled at its actual accumulated bitmap state. -/
theorem compileWordToStack_member (ac : AsmConfigExact width) (perf : Bool) (k : Nat)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width))) (initial : AppList (BitVec width) × Nat)
    (name count : Nat) (p : WordLangProgHOL (BitVec width)) (member : (name,count,p) ∈ programs) :
    ∃ bitmaps, (name,(compileProgNative ac perf p count k bitmaps).1) ∈
      (compileWordToStackNative ac perf k programs initial).1 := by
  induction programs generalizing initial with
  | nil => simp at member
  | cons head tail ih =>
    rcases head with ⟨headName,headCount,headProg⟩
    simp only [List.mem_cons] at member
    rcases compiled : compileProgNative ac perf headProg headCount k initial with ⟨body,frame,next⟩
    rcases rest : compileWordToStackNative ac perf k tail next with ⟨bodies,frames,final⟩
    rcases member with same | later
    · cases same
      refine ⟨initial,?_⟩
      simp only [compileWordToStackNative,compiled,rest,List.mem_cons]
      exact Or.inl True.intro
    · obtain ⟨bitmaps,h⟩ := ih next later
      rw [rest] at h
      refine ⟨bitmaps,?_⟩
      simp only [compileWordToStackNative,compiled,rest,List.mem_cons]
      exact Or.inr h

/-- An input function with a non-stub name and distinct program keys is found
at its actual compiled body in the native top-level Stack code. -/
theorem compileNative_entry (ac : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (name count : Nat) (p : WordLangProgHOL (BitVec width)) (member : (name,count,p) ∈ programs)
    (nodup : (programs.map Prod.fst).Nodup)
    (notRaise : name ≠ raiseStubLocation) (notStore : name ≠ storeConstsStubLocation) :
    ∃ bitmaps, sptLookup name (sptFromAList (compileNative ac false programs).2.2.2) =
      some (compileProgNative ac false p count (ac.regCount-(5+ac.avoidRegs.length)) bitmaps).1 := by
  let k := ac.regCount-(5+ac.avoidRegs.length)
  let initial : AppList (BitVec width) × Nat := (.list [4],1)
  obtain ⟨bitmaps,hmember⟩ := compileWordToStack_member ac false k programs initial name count p member
  have keys : (compileWordToStackNative ac false k programs initial).1.map Prod.fst = programs.map Prod.fst := by
    exact Flapjack.WordToStackProofs.mapFstCompileWordToStack ac false k programs initial _ _ rfl
  have outputNodup : ((compileWordToStackNative ac false k programs initial).1.map Prod.fst).Nodup := by rw [keys]; exact nodup
  have lookup := sptAListLookup_of_mem_nodup _ name _ outputNodup hmember
  refine ⟨bitmaps,?_⟩
  change sptLookup name (sptFromAList
    ((raiseStubLocation,raiseStubNative false k) :: (storeConstsStubLocation,storeConstsStubNative k) ::
      (compileWordToStackNative ac false k programs initial).1)) = _
  rw [sptLookup_sptFromAList]
  simp only [sptAListLookup,if_neg notRaise,if_neg notStore]
  exact lookup

/-- The real Stack compiler supplies the bitmap accounting and prefix facts
for the selected entry, using its actual final bitmap table. -/
theorem compileNative_entry_bitmaps (ac : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (name count : Nat) (p : WordLangProgHOL (BitVec width)) (member : (name,count,p) ∈ programs)
    (nodup : (programs.map Prod.fst).Nodup)
    (notRaise : name ≠ raiseStubLocation) (notStore : name ≠ storeConstsStubLocation) :
    ∃ bs n bsPost nPost body frame,
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
  obtain ⟨bs,n,bsPost,nPost,frame,body,bodyCompiled,lengthBound,gapBound,bitmapPrefix,bodyLookup⟩ :=
    compileWordToStackImpALookup ac false k programs (.list [4]) 1 bodies frames output next name count p
      (appListAppend output) compiled sourceLookup (by simp [appListAppend,appendAux])
      (by simp [appListAppend,appendAux]) (by simp [appListAppend,appendAux])
  dsimp only [k] at compiled
  simp only [compileNative, Bool.false_eq_true, if_false, compiled]
  refine ⟨bs,n,bsPost,nPost,body,frame,bodyCompiled,?_,lengthBound,?_,?_⟩
  · rw [sptLookup_sptFromAList]
    change sptAListLookup name ((raiseStubLocation,raiseStubNative false k) ::
      (storeConstsStubLocation,storeConstsStubNative k) :: bodies) = _
    simp only [sptAListLookup,if_neg notRaise,if_neg notStore]
    rw [Flapjack.WordToStackProofs.CompCorrect.Install.sptAListLookup_eq_panPropsALookupEq]
    exact bodyLookup
  · exact gapBound
  · exact bitmapPrefix

/-- The native Stack output contains the fully allocated Word body selected by
the whole Word pass, at the bitmap state reached during list compilation. -/
theorem wholeWordStack_entry (wc : Flapjack.Compiler.Backend.WordToWord.Config) (ac : AsmConfigExact width)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (name count : Nat) (p : WordLangProgHOL (BitVec width)) (member : (name,count,p) ∈ programs)
    (nodup : (programs.map Prod.fst).Nodup)
    (notRaise : name ≠ raiseStubLocation) (notStore : name ≠ storeConstsStubLocation) :
    ∃ col q bitmaps,
      q = (fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac ((name,count,p),col)).2.2 ∧
      sptLookup name (sptFromAList (compileNative ac false (compile wc ac programs).2).2.2.2) =
        some (compileProgNative ac false q count (ac.regCount-(5+ac.avoidRegs.length)) bitmaps).1 := by
  obtain ⟨col,hmember⟩ := wholeCompile_contains_single wc ac programs name count p member
  have eq : fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac ((name,count,p),col) =
      (name,count,(fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac ((name,count,p),col)).2.2) := by
    simp [fullCompileSingle,compileSingle]
  rw [eq] at hmember
  have outputNodup : ((compile wc ac programs).2.map Prod.fst).Nodup := by
    rw [wholeCompile_names wc ac programs]
    exact nodup
  obtain ⟨bitmaps,lookup⟩ := compileNative_entry ac _ name count _ hmember outputNodup notRaise notStore
  exact ⟨col,_,bitmaps,rfl,lookup⟩

/-- The actual Word and Stack pipelines jointly choose the allocated function
and bitmap segment satisfying the stack simulation accounting. -/
theorem wholeWordStack_entry_bitmaps (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : AsmConfigExact width) (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (name count : Nat) (p : WordLangProgHOL (BitVec width)) (member : (name,count,p) ∈ programs)
    (nodup : (programs.map Prod.fst).Nodup)
    (notRaise : name ≠ raiseStubLocation) (notStore : name ≠ storeConstsStubLocation) :
    ∃ col q bs n bsPost nPost body frame,
      q = (fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac ((name,count,p),col)).2.2 ∧
      compileProgNative ac false q count (ac.regCount-(5+ac.avoidRegs.length)) (bs,n) = (body,frame,bsPost,nPost) ∧
      sptLookup name (sptFromAList (compileNative ac false (compile wc ac programs).2).2.2.2) = some body ∧
      (appListAppend bs).length ≤ n ∧
      n-(appListAppend bs).length ≤ (compileNative ac false (compile wc ac programs).2).1.length ∧
      (appListAppend bsPost).IsPrefix ((compileNative ac false (compile wc ac programs).2).1.drop (n-(appListAppend bs).length)) := by
  obtain ⟨col,hmember⟩ := wholeCompile_contains_single wc ac programs name count p member
  have eq : fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac ((name,count,p),col) =
      (name,count,(fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac ((name,count,p),col)).2.2) := by
    simp [fullCompileSingle,compileSingle]
  rw [eq] at hmember
  have outputNodup : ((compile wc ac programs).2.map Prod.fst).Nodup := by
    rw [wholeCompile_names wc ac programs]
    exact nodup
  obtain ⟨bs,n,bsPost,nPost,body,frame,bodyCompiled,lookup,lengthBound,gapBound,bitmapPrefix⟩ :=
    compileNative_entry_bitmaps ac _ name count _ hmember outputNodup notRaise notStore
  exact ⟨col,_,bs,n,bsPost,nPost,body,frame,rfl,bodyCompiled,lookup,lengthBound,gapBound,bitmapPrefix⟩

/-- The Word body at the native Stack entry has a source-related execution and
visit bound, with the actual oracle and accumulated bitmap state chosen by the
whole-program compilers. -/
theorem wholeWordStack_entry_bound {C F : Type} (wc : Flapjack.Compiler.Backend.WordToWord.Config)
    (ac : AsmConfigExact width) (programs : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (name count : Nat) (p : WordLangProgHOL (BitVec width)) (member : (name,count,p) ∈ programs)
    (nodup : (programs.map Prod.fst).Nodup)
    (notRaise : name ≠ raiseStubLocation) (notStore : name ≠ storeConstsStubLocation)
    (shape : LoopSequence p) (s post : WordSemStateFiniteExact width C F)
    (res : Option (WordSemResult width)) (locals : Spt (WordLocW width)) (limit : Nat)
    (run : evaluate p s = (res,post)) (nonerror : res ≠ some .error) (notTimeout : res ≠ some .timeOut)
    (sourceBound : steps p s ≤ limit) (gc : gcFunConstOk s.gcFun)
    (localRel : wordLocalsRel (maxVarHOL (compileExp p)+1) s.locals locals)
    (domain : sptDomain locals = (fun key => key ∈ evenList count)) :
    ∃ col q bitmaps selectedLocals targetPost,
      q = (fullCompileSingle ac.twoRegArith (ac.regCount-(5+ac.avoidRegs.length)) wc.regAlg ac ((name,count,p),col)).2.2 ∧
      sptLookup name (sptFromAList (compileNative ac false (compile wc ac programs).2).2.2.2) =
        some (compileProgNative ac false q count (ac.regCount-(5+ac.avoidRegs.length)) bitmaps).1 ∧
      evaluate q {s with locals := locals,clock := limit} = (res,targetPost) ∧
      wordStateEqRel {post with locals := selectedLocals,clock := limit-(s.clock-post.clock)} targetPost ∧
      steps q {s with locals := locals,clock := limit} ≤ sizeOf q * (limit+1) := by
  obtain ⟨col,q,bitmaps,qDef,lookup⟩ := wholeWordStack_entry wc ac programs name count p member nodup notRaise notStore
  obtain ⟨selectedLocals,targetPost,targetRun,rel,bound⟩ := compilerPrefix_alloc_correct
    ac ac.twoRegArith count name wc.regAlg (ac.regCount-(5+ac.avoidRegs.length)) col shape
    s post res locals limit run nonerror notTimeout sourceBound gc localRel domain
  refine ⟨col,q,bitmaps,selectedLocals,targetPost,qDef,lookup,?_,rel,?_⟩
  · rw [qDef,fullCompileSingle_eq_alloc ac ac.twoRegArith count name wc.regAlg
      (ac.regCount-(5+ac.avoidRegs.length)) col shape]
    exact targetRun
  · rw [qDef,fullCompileSingle_eq_alloc ac ac.twoRegArith count name wc.regAlg
      (ac.regCount-(5+ac.avoidRegs.length)) col shape]
    exact bound

end SteppedFlapjack.WordToStackSteps
