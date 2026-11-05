import SteppedFlapjack.LoopToWordSteps.Sequence
import SteppedFlapjack.WordToStackSteps.EntryComposition

/-! The common fragment of the quantitative Loop-to-Word and Word-to-Stack proofs. -/
namespace SteppedFlapjack.LoopToWordSteps
open Flapjack Flapjack.LoopSemStateFiniteExact SteppedFlapjack.WordToStackSteps
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

/-- Direct Loop leaves supported by the proved Word-to-Stack loop fragment. -/
inductive StackReadyLeaf {width : Nat} [NeZero width] : HolLoopProg width → Prop
  | skip : StackReadyLeaf .skip
  | fail : StackReadyLeaf .fail
  | tick : StackReadyLeaf .tick
  | arith (a) : StackReadyLeaf (.arith a)
  | setGlobal (v e) : StackReadyLeaf (.setGlobal v e)
  | load32 (a v) : StackReadyLeaf (.load32 a v)
  | loadByte (a v) : StackReadyLeaf (.loadByte a v)
  | store32 (a v) : StackReadyLeaf (.store32 a v)
  | storeByte (a v) : StackReadyLeaf (.storeByte a v)
  | break (n) : StackReadyLeaf (.break n)
  | continue (n) : StackReadyLeaf (.continue n)
  | ret (ns) : StackReadyLeaf (.return ns)
  | locValue (a b) : StackReadyLeaf (.locValue a b)

/-- These leaves are all included in the earlier Loop-to-Word bound. -/
theorem stackReadyLeaf_direct {width : Nat} [NeZero width] {p : HolLoopProg width}
    (shape : StackReadyLeaf p) : LoopSteps.DirectLeaf p := by
  cases shape <;> constructor

/-- Their actual compiled Word program belongs to the proved Stack fragment. -/
theorem stackReadyLeaf_wordBlock {width : Nat} [NeZero width] {p : HolLoopProg width}
    (shape : StackReadyLeaf p) (ctxt : Spt Nat) (labels : Nat × Nat) :
    LoopBlock (LoopToWord.compHOL ctxt p labels).1 := by
  cases labels
  cases shape <;> try { simp only [LoopToWord.compHOL]; constructor }
  case arith a => cases a <;> simp only [LoopToWord.compHOL] <;> constructor

/-- Programs in the common proved Loop-to-Stack fragment. -/
inductive StackReady {width : Nat} [NeZero width] : HolLoopProg width → Prop
  | leaf {p} : StackReadyLeaf p → StackReady p
  | seq {a b} : StackReady a → StackReady b → StackReady (.seq a b)
  | mark {p} : StackReady p → StackReady (.mark p)

theorem stackReady_directProgram {width : Nat} [NeZero width] {p : HolLoopProg width}
    (shape : StackReady p) : DirectProgram p := by
  induction shape with
  | leaf h => exact .leaf (stackReadyLeaf_direct h)
  | seq _ _ ha hb => exact .seq ha hb
  | mark _ h => exact .mark h

theorem stackReady_wordBlock {width : Nat} [NeZero width] {p : HolLoopProg width}
    (shape : StackReady p) (ctxt : Spt Nat) :
    ∀ labels : Nat × Nat, LoopBlock (LoopToWord.compHOL ctxt p labels).1 := by
  induction shape with
  | leaf h => exact stackReadyLeaf_wordBlock h ctxt
  | @seq a b ha hb iha ihb =>
    intro labels
    simp only [LoopToWord.compHOL]
    exact .seq (iha labels) (ihb (LoopToWord.compHOL ctxt a labels).2)
  | mark h ih =>
    intro labels
    simpa only [LoopToWord.compHOL] using ih labels


/-- Compilation of this common fragment introduces no dynamic installation. -/
theorem stackReady_noInstall {width : Nat} [NeZero width] {p : HolLoopProg width}
    (shape : StackReady p) (ctxt : Spt Nat) :
    ∀ labels : Nat × Nat, noInstallSubprogsHOL (LoopToWord.compHOL ctxt p labels).1 = true := by
  induction shape with
  | leaf h =>
    intro labels
    cases labels
    cases h <;> try { simp [LoopToWord.compHOL,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp] }
    case arith a => cases a <;> simp [LoopToWord.compHOL,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp]
  | @seq a b ha hb iha ihb =>
    intro labels
    simp only [LoopToWord.compHOL,noInstallSubprogsHOL,notCreatedSubprogsWithMemOp,Bool.and_eq_true]
    exact ⟨iha labels,ihb (LoopToWord.compHOL ctxt a labels).2⟩
  | mark h ih =>
    intro labels
    simpa only [LoopToWord.compHOL] using ih labels


/-- Completed Loop results whose Word return label is the program entry label. -/
inductive CompleteLoopResult : Option (LoopResultExact 64) → Prop
  | return (values) : CompleteLoopResult (some (.result values))
  | ffi (event) : CompleteLoopResult (some (.finalFfi event))

/-- The original result relation derives a complete Word outcome. -/
theorem completeLoop_resultCase {C F : Type} (ctxt : Spt Nat)
    (word wordPost : WordSemStateFiniteExact 64 C F) (sourcePost : LoopSemStateFiniteExact 64 F)
    (result : Option (LoopResultExact 64)) (wordResult : Option (WordSemResult 64))
    (complete : CompleteLoopResult result)
    (relation : LoopToWord.CompileCorrect.resultCase ctxt (.loc 1 0) word result sourcePost wordResult wordPost) :
    CompleteWordResult wordResult ∧ wordResult ≠ some .error ∧ wordResult ≠ some .timeOut := by
  cases complete with
  | «return» values =>
    simp only [LoopToWord.CompileCorrect.resultCase] at relation
    rw [relation.2.1]
    exact ⟨.return values,by simp,by simp⟩
  | ffi event =>
    simp only [LoopToWord.CompileCorrect.resultCase] at relation
    rw [relation]
    exact ⟨.ffi event,by simp,by simp⟩


/-- A LoopSem source-step limit directly yields an actual bounded StackSem
execution; the intermediate Word execution and its bound are derived. -/
theorem stackReady_loopToStack {C F : Type}
    (ac : AsmConfigExact 64) (p : HolLoopProg 64) (shape : StackReady p)
    (source sourcePost : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (word : WordSemStateFiniteExact 64 (Nat × C) F) (target : StackSemStateFiniteExact 64 C F)
    (ctxt : Spt Nat) (labels : Nat × Nat) (k f frame limit : Nat) (lens : List Nat)
    (bs bsPost : AppList (BitVec 64)) (n nPost : Nat) (compiled : HolProg 64)
    (complete : CompleteLoopResult result) (stepBound : LoopSteps.steps p source ≤ limit)
    (loopPremises : LoopSemStateFiniteExact.evaluate p source = (result,sourcePost) ∧ result ≠ some .error ∧
      loopToWordStateRelHOLExact source word ∧ LoopToWord.localsRelHOL ctxt source.locals word.locals ∧
      sptLookup 0 word.locals = some (.loc 1 0) ∧ goodDimindex 64 ∧ ¬ wordSemIsWordLoc (.loc 1 0 : WordLocW 64) = true ∧
      (∀ k, sptMem k (accVarsHOL p .ln) → sptMem k ctxt))
    (noInstallCode : WordProps.noInstallCode word.code)
    (code : ∀ loc arity q, sptLookup loc word.code = some (arity,q) → LoopBlock q)
    (stackPremises : stateRel ac k f frame word target lens 0 ∧
      postAllocConventionsHOL k (LoopToWord.compHOL ctxt p labels).1 = true ∧
      flatExpConventions (LoopToWord.compHOL ctxt p labels).1 = true ∧
      compNative ac false (LoopToWord.compHOL ctxt p labels).1 (bs,n) (k,f,frame) = (compiled,(bsPost,nPost)) ∧
      (appListAppend bs).length ≤ n ∧ n-(appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n-(appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL (LoopToWord.compHOL ctxt p labels).1 < 2*frame+2*k) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × C) F) (wordResult : Option (WordSemResult 64))
      (targetPost : StackSemStateFiniteExact 64 C F) (targetResult : Option (StackSemResult 64)),
      WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt p labels).1 word = (wordResult,wordPost) ∧
      wordPost.ffi = sourcePost.ffi ∧
      LoopToWord.CompileCorrect.resultCase ctxt (.loc 1 0) word result sourcePost wordResult wordPost ∧
      CompleteWordResult wordResult ∧
      StackSemEvaluate.evaluate (compiled,{target with clock := limit}) = (targetResult,targetPost) ∧
      compCorrectResult ac k f frame {word with clock := limit}
        {wordPost with clock := limit-(word.clock-wordPost.clock)} targetPost wordResult targetResult lens ∧
      StackSteps.steps (compiled,{target with clock := limit}) ≤
        callSequenceCost ac limit target.code (LoopToWord.compHOL ctxt p labels).1 (bs,n) (k,f,frame) := by
  have direct := directProgram_correct_with_steps (C := Nat × C) (stackReady_directProgram shape) source
  obtain ⟨wordPost,wordResult,wordRun,wordFfi,wordRelation,wordBound⟩ :=
    direct result sourcePost word ctxt (.loc 1 0) labels loopPremises
  obtain ⟨wordComplete,wordNotError,wordNotTimeout⟩ :=
    completeLoop_resultCase ctxt word wordPost sourcePost result wordResult complete wordRelation
  have loopBlock := stackReady_wordBlock shape ctxt labels
  have callShape : CallSequence (LoopToWord.compHOL ctxt p labels).1 := .block loopBlock
  have noInstall := stackReady_noInstall shape ctxt labels
  obtain ⟨targetPost,targetResult,targetRun,targetRelation,targetBound⟩ :=
    callSequence_bounded ac _ callShape word wordPost target wordResult k f frame bs bsPost n nPost limit
      compiled lens noInstall noInstallCode code wordNotTimeout (wordBound.trans stepBound)
      ⟨wordRun,wordNotError,stackPremises⟩
  exact ⟨wordPost,wordResult,targetPost,targetResult,wordRun,wordFfi,wordRelation,wordComplete,
    targetRun,targetRelation,targetBound⟩

end SteppedFlapjack.LoopToWordSteps
