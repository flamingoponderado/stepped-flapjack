import SteppedFlapjack.LoopLiveSteps.ClockBound
import Flapjack.Pancake.LoopToWord.CompFuncExact
import Flapjack.Pancake.CrepToLoop.ContextExact

/-! Membership of optimized Loop functions in the actual Word frontend output. -/
namespace SteppedFlapjack.LoopLiveSteps
open Flapjack Flapjack.Basis.Pure.MlString Flapjack.LoopToWord SteppedFlapjack.LoopToWordSteps
variable {width : Nat} [NeZero width]

/-- The actual Loop-to-Word compiler maps each zero-argument function to an
entry with one return-location argument and the compiler-generated context. -/
theorem loopToWord_zeroArg_member (code : List (Nat × List Nat × HolLoopProg width))
    (name : Nat) (p : HolLoopProg width) (member : (name,[],p) ∈ code) :
    (name,1,(LoopToWord.compHOL
      (makeCtxtHOL 2 (fromNumSetHOL (sptDifference (accVarsHOL p .ln) (toNumSetHOL []))) .ln)
      p (name,2)).1) ∈ loopToWordCompileHOL code := by
  apply List.mem_map.mpr
  refine ⟨(name,[],p),member,?_⟩
  rfl

/-- The real Crep-to-Loop list compiler places each zero-argument function
at its actual numbered location, after Crep simplification and Loop optimization. -/
theorem crepToLoop_zeroArg_member (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (code : List (MlString × List Nat × CrepProgHOL width))
    (name : MlString) (p : CrepProgHOL width) (member : (name,[],p) ∈ code) :
    ∃ index, (index+firstLoopName,[],
      optimiseHOL (compFuncHOLExact arch (crepToLoopMakeFuncsExactExecutable code) [] (crepSimpProgHOL p))) ∈
      compileProgHOLExact arch code := by
  obtain ⟨index,hi,hget⟩ := List.mem_iff_getElem.mp member
  refine ⟨index,List.mem_iff_getElem.mpr ⟨index,?_,?_⟩⟩
  · simp only [compileProgHOLExact,List.length_zipWith,List.length_map,List.length_range, Nat.min_self]
    exact hi
  · simp only [compileProgHOLExact,List.getElem_zipWith,List.getElem_map,List.getElem_range,hget]
    rfl

/-- The actual optimized Loop body yields a supported Word compiler input when
it appears as a zero-argument function in the real Loop program list. -/
theorem optimised_loopToWord_member (code : List (Nat × List Nat × HolLoopProg width))
    (name : Nat) (p : HolLoopProg width) (shape : LoopSequenceSource p)
    (member : (name,[],optimiseHOL p) ∈ code) :
    let body := optimiseHOL p
    let ctxt := makeCtxtHOL 2 (fromNumSetHOL (sptDifference (accVarsHOL body .ln) (toNumSetHOL []))) .ln
    (name,1,(LoopToWord.compHOL ctxt body (name,2)).1) ∈ loopToWordCompileHOL code ∧
      LoopSequenceSource body :=
  ⟨loopToWord_zeroArg_member code name (optimiseHOL p) member,optimise_sequence shape⟩

/-- Both actual frontend list passes place a zero-argument Crep function’s
optimized body into the Word input, at the compiler-generated numeric name. -/
theorem crepToWord_zeroArg_member (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (code : List (MlString × List Nat × CrepProgHOL width))
    (name : MlString) (p : CrepProgHOL width) (member : (name,[],p) ∈ code) :
    let body := optimiseHOL (compFuncHOLExact arch (crepToLoopMakeFuncsExactExecutable code) [] (crepSimpProgHOL p))
    ∃ index, let location := index+firstLoopName
      let ctxt := makeCtxtHOL 2 (fromNumSetHOL (sptDifference (accVarsHOL body .ln) (toNumSetHOL []))) .ln
      (location,1,(LoopToWord.compHOL ctxt body (location,2)).1) ∈
        loopToWordCompileHOL (compileProgHOLExact arch code) := by
  obtain ⟨index,entry⟩ := crepToLoop_zeroArg_member arch code name p member
  exact ⟨index,loopToWord_zeroArg_member _ _ _ entry⟩

end SteppedFlapjack.LoopLiveSteps
