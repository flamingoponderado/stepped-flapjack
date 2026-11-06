import SteppedFlapjack.WordAllocSteps.WholeTailCode
import SteppedFlapjack.CrepToLoopSteps.WholeCodeRel
import SteppedFlapjack.LoopLiveSteps.TailEntryShape

/-! Supported Crep syntax implies the actual whole Word input shapes. -/
namespace SteppedFlapjack.WordAllocSteps
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm
open SteppedFlapjack.CrepToLoopSteps SteppedFlapjack.LoopToWordSteps SteppedFlapjack.LoopLiveSteps

/-- The actual optimized Crep-to-Loop compiler preserves the supported body
classification for any function parameters and function-label map. -/
theorem supportedBody_optimised_loop {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (funcs : HolFiniteMapExact MlString (Nat × Nat))
    (params : List Nat) {body : CrepProgHOL width} (shape : SupportedCodeBody body) :
    LoopSequenceSource (optimiseHOL (compFuncHOLExact arch funcs params (crepSimpProgHOL body))) ∨
      TailEntryShape (optimiseHOL (compFuncHOLExact arch funcs params (crepSimpProgHOL body))) := by
  rw [supportedCodeBody_simp_fixed shape]
  unfold compFuncHOLExact
  cases shape with
  | branch h =>
    left
    exact optimise_sequence (.branch (compile_branchProgram_loopBranch h _ _))
  | tail h name =>
    right
    exact (compiled_tailEntry_shape _ _ _ h name).2
  | loop hi hc hb ht =>
    left
    exact optimise_sequence (branchConditionWhileBranch_wordSimpShape _ hi _ hc _ _ hb ht _ _)

/-- Any list of supported Loop bodies becomes a whole Word program satisfying
the code-shape premise used by the allocation and machine simulations. -/
theorem wholeLoop_word_shapes {width : Nat} [NeZero width]
    (programs : List (Nat × List Nat × HolLoopProg width))
    (shapes : ∀ name params body, (name,params,body) ∈ programs → LoopSequenceSource body ∨ TailEntryShape body) :
    TailProgramShapes (loopToWordCompileHOL programs) := by
  intro name arity body member
  obtain ⟨⟨sourceName,params,sourceBody⟩,sourceMember,entryEq⟩ := List.mem_map.mp member
  cases entryEq
  rcases shapes sourceName params sourceBody sourceMember with h | h
  · left
    exact loopSequenceSource_word h _ _
  · right
    exact tailEntry_word h _ _

/-- Every function produced by the actual Crep-to-Loop compiler has a supported
Loop shape when its source body belongs to the supported Crep fragment. -/
theorem wholeCrep_optimised_loop_shapes {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (programs : List (MlString × List Nat × CrepProgHOL width))
    (shapes : ∀ name params body, (name,params,body) ∈ programs → SupportedCodeBody body) :
    ∀ name params body, (name,params,body) ∈ compileProgHOLExact arch programs →
      LoopSequenceSource body ∨ TailEntryShape body := by
  let comp := compFuncHOLExact (width := width) arch (crepToLoopMakeFuncsExactExecutable programs)
  have zipShape : ∀ (ns : List Nat) (entries : List (MlString × List Nat × CrepProgHOL width)),
      (∀ entry ∈ entries, SupportedCodeBody entry.2.2) →
      ∀ output ∈ List.zipWith (fun n entry => (n,List.range entry.2.1.length,
        optimiseHOL (comp entry.2.1 (crepSimpProgHOL entry.2.2)))) ns entries,
        LoopSequenceSource output.2.2 ∨ TailEntryShape output.2.2 := by
    intro ns
    induction ns with
    | nil => intro entries _ output member; simp at member
    | cons n ns ih =>
      intro entries hs output member
      cases entries with
      | nil => simp at member
      | cons entry entries =>
        simp only [List.zipWith,List.mem_cons] at member
        rcases member with rfl | member
        · exact supportedBody_optimised_loop arch _ entry.2.1 (hs entry (by simp))
        · apply ih entries (fun e he => hs e (by simp [he])) output member
  intro name params body member
  have h := zipShape _ programs (by
    intro entry member
    rcases entry with ⟨name,params,body⟩
    exact shapes name params body member) (name,params,body) member
  exact h

/-- Supported Crep functions discharge the whole Word compiler's structural
premise for the actual Crep/Loop/Word frontend output. -/
theorem wholeCrep_word_shapes {width : Nat} [NeZero width]
    (arch : AsmArchitecture) (programs : List (MlString × List Nat × CrepProgHOL width))
    (shapes : ∀ name params body, (name,params,body) ∈ programs → SupportedCodeBody body) :
    TailProgramShapes (loopToWordCompileHOL (compileProgHOLExact arch programs)) :=
  wholeLoop_word_shapes _ (wholeCrep_optimised_loop_shapes arch programs shapes)

end SteppedFlapjack.WordAllocSteps
