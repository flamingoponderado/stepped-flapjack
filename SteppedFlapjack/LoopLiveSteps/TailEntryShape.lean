import SteppedFlapjack.LoopLiveSteps.OptimiseShape
import SteppedFlapjack.CrepToLoopSteps.TailCallSteps
import SteppedFlapjack.CrepToLoopSteps.WordSimpShape
import SteppedFlapjack.LoopLiveSteps.FrontendMember

/-! The actual optimizer preserves branch prefixes with direct tail calls. -/
namespace SteppedFlapjack.LoopLiveSteps
open Flapjack Flapjack.LoopSemStateFiniteExact SteppedFlapjack.LoopToWordSteps SteppedFlapjack.CrepToLoopSteps
variable {width : Nat} [NeZero width]

/-- A loop-free entry containing direct zero-argument tail calls. -/
inductive TailEntryShape : HolLoopProg width → Prop
  | branch {p} : LoopBranch p → TailEntryShape p
  | call (loc : Nat) : TailEntryShape (.call none (some loc) [] none)
  | seq {a b} : TailEntryShape a → TailEntryShape b → TailEntryShape (.seq a b)
  | mark {p} : TailEntryShape p → TailEntryShape (.mark p)

/-- The actual call-target propagation pass leaves such entries unchanged. -/
theorem loopCall_tailEntry {p : HolLoopProg width} (shape : TailEntryShape p) :
    ∀ env, (loopCallCompHOL env p).1 = p := by
  induction shape with
  | branch h => exact loopCall_branch h
  | call loc => intro env; simp [loopCallCompHOL]
  | @seq a b ha hb iha ihb =>
    intro env
    simp only [loopCallCompHOL]
    rw [iha env,ihb (loopCallCompHOL env a).2]
  | mark h ih => intro env; simp only [loopCallCompHOL,ih]

/-- Liveness shrinking retains the direct tail-call shape. -/
theorem shrink_tailEntry {p : HolLoopProg width} (shape : TailEntryShape p) :
    ∀ lt live, TailEntryShape (shrinkHOL lt p live).1 := by
  induction shape with
  | branch h => intro lt live; exact .branch (shrink_branch h lt live)
  | call loc => intro lt live; simp only [shrinkHOL]; exact .call loc
  | @seq a b ha hb iha ihb =>
    intro lt live
    simp only [shrinkHOL]
    exact .seq (iha lt (shrinkHOL lt b live).2) (ihb lt live)
  | mark h ih => intro lt live; simpa only [shrinkHOL] using ih lt live

/-- Every program in the entry fragment remains in it after marking. -/
theorem markAll_tailEntry {p : HolLoopProg width} (shape : TailEntryShape p) :
    TailEntryShape (markAllHOL p).1 ∧ (markAllHOL p).2 = true := by
  induction shape with
  | branch h => exact ⟨.branch (markAll_branch h).1,(markAll_branch h).2⟩
  | call loc => simp only [markAllHOL]; exact ⟨.mark (.call loc),True.intro⟩
  | @seq a b ha hb iha ihb =>
    simp only [markAllHOL,iha.2,ihb.2,Bool.true_and,if_true]
    exact ⟨.mark (.seq iha.1 ihb.1),True.intro⟩
  | mark h ih => simpa only [markAllHOL] using ih

/-- The exact Loop optimizer retains branch-plus-tail-call entries. -/
theorem optimise_tailEntry {p : HolLoopProg width} (shape : TailEntryShape p) :
    TailEntryShape (optimiseHOL p) := by
  simp only [optimiseHOL,loopCall_tailEntry shape .ln,compHOL]
  exact (markAll_tailEntry (shrink_tailEntry shape [] .ln)).1

/-- The real Crep-to-Loop output for a supported initializer and zero-argument
tail call belongs to the fragment both before and after Loop optimization. -/
theorem compiled_tailEntry_shape (ctxt : CrepToLoopContextExact) (live : NumSet)
    (init : CrepProgHOL width) (shape : BranchProgram init) (name : Basis.Pure.MlString.MlString) :
    TailEntryShape (compileHOLExact ctxt live (.seq init (.call none name []))) ∧
    TailEntryShape (optimiseHOL (compileHOLExact ctxt live (.seq init (.call none name [])))) := by
  have h : TailEntryShape (compileHOLExact ctxt live (.seq init (.call none name []))) := by
    simp only [compileHOLExact,compileExpsHOLExact,genTemps,List.nil_append]
    exact .seq (.branch (compile_branchProgram_loopBranch shape ctxt live)) (.seq (.call _) (.branch .skip))
  exact ⟨h,optimise_tailEntry h⟩

/-- Word programs generated from the branch-and-tail-call entry. -/
inductive WordTailEntryShape : WordLangProgHOL (BitVec width) → Prop
  | branch {p} : WordSimpSteps.Branch p → WordTailEntryShape p
  | call (loc : Nat) : WordTailEntryShape (.call none (some loc) [0] none)
  | seq {a b} : WordTailEntryShape a → WordTailEntryShape b → WordTailEntryShape (.seq a b)

/-- Actual Loop-to-Word compilation preserves the entry structure and maps the
zero-argument tail call to a Word tail call carrying the return location. -/
theorem tailEntry_word {p : HolLoopProg width} (shape : TailEntryShape p) (ctxt : Spt Nat) :
    ∀ labels, WordTailEntryShape (LoopToWord.compHOL ctxt p labels).1 := by
  induction shape with
  | branch h => intro labels; exact .branch (loopBranch_word h ctxt labels)
  | call loc => intro labels; cases labels; simp only [LoopToWord.compHOL,List.map_nil]; exact .call loc
  | @seq a b ha hb iha ihb =>
    intro labels
    simp only [LoopToWord.compHOL]
    exact .seq (iha labels) (ihb (LoopToWord.compHOL ctxt a labels).2)
  | mark h ih => intro labels; simpa only [LoopToWord.compHOL] using ih labels

/-- The optimized generated entry is accepted by the Word tail-entry shape. -/
theorem compiled_tailEntry_word (ctxt : CrepToLoopContextExact) (live : NumSet)
    (init : CrepProgHOL width) (shape : BranchProgram init) (name : Basis.Pure.MlString.MlString)
    (wordCtxt : Spt Nat) (labels : Nat × Nat) :
    WordTailEntryShape (LoopToWord.compHOL wordCtxt
      (optimiseHOL (compileHOLExact ctxt live (.seq init (.call none name [])))) labels).1 :=
  tailEntry_word (compiled_tailEntry_shape ctxt live init shape name).2 wordCtxt labels

/-- A completed generated entry remains a completed execution after the
actual Loop optimizer, with the proved Word tail-entry shape. -/
theorem compiled_tailEntry_optimise_correct {F : Type}
    (ctxt : CrepToLoopContextExact) (live : NumSet) (init : CrepProgHOL 64)
    (shape : BranchProgram init) (name : Basis.Pure.MlString.MlString)
    (source final : LoopSemStateFiniteExact 64 F) (result : Option (LoopResultExact 64))
    (wordCtxt : Spt Nat) (labels : Nat × Nat)
    (run : LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt live (.seq init (.call none name []))) source = (result,final))
    (complete : CompleteLoopResult result) :
    LoopSemStateFiniteExact.evaluate (optimiseHOL (compileHOLExact ctxt live (.seq init (.call none name [])))) source =
      (result,final) ∧
    WordTailEntryShape (LoopToWord.compHOL wordCtxt
      (optimiseHOL (compileHOLExact ctxt live (.seq init (.call none name [])))) labels).1 := by
  refine ⟨optimise_correct _ _ _ _ ⟨run,?_,?_,?_,?_⟩,compiled_tailEntry_word ctxt live init shape name wordCtxt labels⟩
  all_goals cases complete <;> simp_all

end SteppedFlapjack.LoopLiveSteps
