import SteppedFlapjack.WordToStackSteps.WholeInitialization
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallTail
import SteppedFlapjack.WordToStackSteps.EntryComposition
import SteppedFlapjack.WordToStackSteps.WholeTailInitialization
import Flapjack.Misc.Sptree.FromList2
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Call.Support

/-! The actual compiled initial entry either obtains its frame or hits the
native Stack resource limit. -/
namespace SteppedFlapjack.WordToStackSteps
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.WordToStackProofs
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordToStack.Native.Initialization
open Flapjack.Compiler.Backend.WordToWord
open Flapjack.WordToStackProofs.InitializationStateRel
open SteppedFlapjack.WordSimpSteps SteppedFlapjack.StackAllocSteps SteppedFlapjack.WordAllocSteps

/-- The native one-argument call environment meets SSA’s exact input-domain
and instruction-selection local-relation requirements. -/
theorem nativeEntry_locals {width : Nat} [NeZero width] {C F : Type}
    (source : WordSemStateFiniteExact width C F) (size temp : Nat) :
    let entry := callEnv [(.loc 1 0 : WordLocW width)] (some size) source
    sptDomain entry.locals = (fun key => key ∈ Flapjack.Compiler.Backend.WordAlloc.evenList 1) ∧
    wordLocalsRel temp entry.locals entry.locals ∧
    sptLookup 0 entry.locals = some (.loc 1 0) := by
  refine ⟨?_,(fun _ _ => rfl),?_⟩
  · simpa only [WordSemStateFiniteExact.callEnv, Flapjack.Compiler.Backend.WordAlloc.evenList, List.length_cons, List.length_nil] using
      (sptDomainFromList2 [(.loc 1 0 : WordLocW width)])
  · simp [WordSemStateFiniteExact.callEnv,sptFromList2,sptLookup]

/-- The compiler-selected frame for a function with the given arity. -/
def nativeFrame (k count : Nat) (q : WordLangProgHOL (BitVec 64)) : Nat :=
  max (maxVarHOL q / 2 + 1 - k) (count-k)
def nativeFrameSize (k count : Nat) (q : WordLangProgHOL (BitVec 64)) : Nat :=
  let frame := nativeFrame k count q
  if frame = 0 then 0 else frame+1

theorem nativeFrameSize_compile (ac : AsmConfigExact 64) (p : WordLangProgHOL (BitVec 64))
    (k count : Nat) (bitmaps : AppList (BitVec 64) × Nat) :
    (compileProgNative ac false p count k bitmaps).2.1 = nativeFrameSize k count p := by
  unfold compileProgNative nativeFrameSize nativeFrame
  generalize compNative ac false p bitmaps
    (k, (if max (maxVarHOL p / 2 + 1 - k) (count-k) = 0 then 0 else max (maxVarHOL p / 2 + 1 - k) (count-k) + 1),
      max (maxVarHOL p / 2 + 1 - k) (count-k)) = x
  cases x
  rfl

/-- Maximum compiler-selected frame size for a concrete program table. -/
def nativeMaxFrameSize {β : Type} (k : Nat)
    (programs : List (β × Nat × WordLangProgHOL (BitVec 64))) : Nat :=
  programs.foldr (fun row m => max (nativeFrameSize k row.2.1 row.2.2) m) 0

theorem nativeFrames_compile {β : Type} (ac : AsmConfigExact 64) (k : Nat)
    (programs : List (β × Nat × WordLangProgHOL (BitVec 64)))
    (bitmaps : AppList (BitVec 64) × Nat) :
    (compileWordToStackNative ac false k programs bitmaps).2.1 =
      programs.map (fun row => nativeFrameSize k row.2.1 row.2.2) := by
  induction programs generalizing bitmaps with
  | nil => rfl
  | cons row rows ih =>
    rcases row with ⟨name, count, p⟩
    generalize h : compileProgNative ac false p count k bitmaps = result
    rcases result with ⟨body, frame, next⟩
    have hf := nativeFrameSize_compile ac p k count bitmaps
    rw [h] at hf
    simp only at hf
    simp [compileWordToStackNative, h, hf, ih]

theorem nativeFrameSize_le_max {β : Type} (k : Nat)
    (programs : List (β × Nat × WordLangProgHOL (BitVec 64)))
    (name : β) (count : Nat) (p : WordLangProgHOL (BitVec 64))
    (member : (name,count,p) ∈ programs) :
    nativeFrameSize k count p ≤ nativeMaxFrameSize k programs := by
  induction programs with
  | nil => simp at member
  | cons row rows ih =>
    simp only [List.mem_cons] at member
    simp only [nativeMaxFrameSize, List.foldr_cons]
    rcases member with eq | mem
    · subst row
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih mem) (Nat.le_max_right _ _)
theorem compiledFrame_le_max {β : Type} (ac : AsmConfigExact 64) (k : Nat)
    (programs : List (β × Nat × WordLangProgHOL (BitVec 64)))
    (bitmaps : AppList (BitVec 64) × Nat) (size : Nat)
    (member : size ∈ (compileWordToStackNative ac false k programs bitmaps).2.1) :
    size ≤ nativeMaxFrameSize k programs := by
  rw [nativeFrames_compile] at member
  obtain ⟨⟨name,count,p⟩, hmem, eq⟩ := List.mem_map.mp member
  simp only at eq
  subst size
  exact nativeFrameSize_le_max k programs name count p hmem

/-- Every initialized call-site frame lookup is bounded by the concrete program maximum. -/
theorem initializedFrameLookup_le_max {C F : Type}
    (ac : AsmConfigExact 64) (k : Nat)
    (programs : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (t : StackSemStateFiniteExact 64 C F)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (name size : Nat)
    (found : sptLookup name (makeInit ac k t (sptFromAList programs) coracle).stackSize = some size) :
    size ≤ nativeMaxFrameSize k programs := by
  change sptLookup name (sptMapi _ (sptFromAList programs)) = _ at found
  rw [sptLookupMapi, sptLookup_sptFromAList] at found
  cases h : sptAListLookup name programs with
  | none => simp [h] at found
  | some entry =>
    obtain ⟨arity,p⟩ := entry
    simp only [h, Option.map_some, Option.some.injEq] at found
    have member := sptAListLookup_mem name programs (arity,p) h
    subst size
    rw [nativeFrameSize_compile]
    exact nativeFrameSize_le_max k programs name arity p member

/-- The compiler-selected one-argument entry frame. -/
def nativeEntryFrame (k : Nat) (q : WordLangProgHOL (BitVec 64)) : Nat :=
  nativeFrame k 1 q
/-- Stack allocation required by that frame. -/
def nativeEntryFrameSize (k : Nat) (q : WordLangProgHOL (BitVec 64)) : Nat :=
  nativeFrameSize k 1 q

/-- The compiler-selected entry frame is the one-argument instance of the
frame formula. -/
theorem nativeEntryFrameSize_compile (ac : AsmConfigExact 64) (p : WordLangProgHOL (BitVec 64))
    (k : Nat) (bitmaps : AppList (BitVec 64) × Nat) :
    (compileProgNative ac false p 1 k bitmaps).2.1 = nativeEntryFrameSize k p := by
  exact nativeFrameSize_compile ac p k 1 bitmaps

/-- The initialized frame gives the exact local-domain and state premises for
simulating an original Word entry against the compiled code table. Replacing
the code table does not alter entry locals or the frame relation once the
compiled table is restored for the Stack simulation. -/
theorem initializedTail_simulation_state {C F : Type}
    (ac : AsmConfigExact 64) (k frameSize frame : Nat)
    (stack : StackSemStateFiniteExact 64 C F)
    (compiledCode originalCode : Spt (Nat × WordLangProgHOL (BitVec 64)))
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (clock temp : Nat)
    (related : stateRel ac k frameSize frame
      (callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize)
        (makeInit ac k stack compiledCode coracle))
      {stack with stackSpace := stack.stackSpace-frameSize} [] 0) :
    let word := {callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize)
      (makeInit ac k stack compiledCode coracle) with code := originalCode}
    let entry := {stack with clock := clock}
    sptDomain word.locals = (fun key => key ∈ Flapjack.Compiler.Backend.WordAlloc.evenList 1) ∧
    wordLocalsRel temp word.locals word.locals ∧
    sptLookup 0 word.locals = some (.loc 1 0) ∧
    stateRel ac k frameSize frame {word with code := compiledCode,locals := word.locals,clock := clock}
      {entry with stackSpace := entry.stackSpace-frameSize} [] 0 := by
  have localFacts := nativeEntry_locals (makeInit ac k stack compiledCode coracle) frameSize temp
  have shifted := stateRel_setClocks ac k frameSize frame _ _ [] 0 clock related
  exact ⟨localFacts.1,localFacts.2.1,localFacts.2.2,by simpa [WordSemStateFiniteExact.callEnv,makeInit] using shifted⟩


/-- For the compiler-generated zero-argument context, the native Word entry
locals represent the empty Loop locals and every used Loop variable has a
context entry. -/
theorem nativeTailEntry_loopLocals {C F : Type} (p : HolLoopProg 64)
    (source : WordSemStateFiniteExact 64 C F) (frameSize : Nat) :
    let ctxt := makeCtxtHOL 2 (LoopToWord.fromNumSetHOL
      (sptDifference (accVarsHOL p .ln) (LoopToWord.toNumSetHOL []))) .ln
    let word := callEnv [(.loc 1 0 : WordLocW 64)] (some frameSize) source
    LoopToWord.localsRelHOL ctxt .ln word.locals ∧
      ∀ k, sptMem k (accVarsHOL p .ln) → sptMem k ctxt := by
  have h := LoopToWord.CompileCorrect.compFunc_ctxt [] p [] (.loc 1 0 : WordLocW 64) (by simp) (by simp)
  simpa [WordSemStateFiniteExact.callEnv,sptFromAList] using h


/-- The native entry frame formula bounds every source variable, and the
actual entry lookup validates every label occurring in its compiled body. -/
theorem nativeEntry_frame_and_labels {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k frame frameSize count start : Nat)
    (program : WordLangProgHOL (BitVec width)) (entry : StackSemStateFiniteExact width C F)
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat) (body : HolProg width)
    (frameDef : frame = max (maxVarHOL program / 2 + 1 - k) (count-k))
    (frameSizeDef : frameSize = if frame = 0 then 0 else frame+1)
    (compiles : compNative ac false program (bs,n) (k,frameSize,frame) = (body,(bsPost,nPost)))
    (found : sptLookup start entry.code = some (compileProgNative ac false program count k (bs,n)).1) :
    maxVarHOL program < 2*frame+2*k ∧
      ∀ loc, StackSem.getLabelsExact body loc → StackSem.locCheckExact entry.code loc := by
  constructor
  · rw [frameDef]
    have lower := Nat.le_max_left (maxVarHOL program / 2 + 1 - k) (count-k)
    omega
  · have foundBody : sptLookup start entry.code = some (.seq (.stackAlloc (frameSize-(count-k))) body) := by
      simpa only [compileProgNative, ← frameDef, ← frameSizeDef, compiles] using found
    intro loc label
    refine Or.inr ⟨start,_,foundBody,?_⟩
    simp only [StackSem.getLabelsExact]
    exact Or.inr label

end SteppedFlapjack.WordToStackSteps
