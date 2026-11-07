import SteppedFlapjack.CrepToLoopSteps.WholeCodeRel
import SteppedFlapjack.CrepToLoopSteps.DeclTerminal
import SteppedFlapjack.LoopLiveSteps.OptimiseShape
import SteppedFlapjack.LoopToWordSteps.BitmapSourceShape

/-! Static Loop shapes from supported Crep bodies. -/
namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open SteppedFlapjack.LoopToWordSteps SteppedFlapjack.LoopLiveSteps

/-- Every supported Crep body compiles to a bitmap-free Loop shape, with no
execution, clock or state hypotheses. -/
theorem supportedCodeBody_loopShape {width : Nat} [NeZero width]
    (ctxt : CrepToLoopContextExact) (live : NumSet) {p : CrepProgHOL width}
    (shape : SupportedCodeBody p) :
    TailEntryShape (optimiseHOL (compileHOLExact ctxt live p)) ∨
      LoopSequenceSource (optimiseHOL (compileHOLExact ctxt live p)) := by
  cases shape with
  | branch h =>
    right
    exact optimise_sequence (.branch (compile_branchProgram_loopBranch h ctxt live))
  | tail h name =>
    left
    exact (compiled_tailEntry_shape ctxt live _ h name).2
  | loop hi hc hb ht =>
    right
    exact optimise_sequence (branchConditionWhileBranch_wordSimpShape _ hi _ hc _ _ hb ht ctxt live)
  | @declWhile name value condition body tail hv hc hb ht =>
    right
    apply optimise_sequence
    have suffix (bc : CrepToLoopContextExact) (bl : NumSet) :
        LoopSequenceSource (compileHOLExact bc bl (.seq (.while condition body) tail)) := by
      obtain ⟨code,conditionValue,next,outLive,condCompiled,loopCompiled,loopBody⟩ :=
        branchConditionWhile_loopBranch condition hc body hb bc bl
      simp only [compileHOLExact,loopCompiled]
      exact .seq (.loop bl bl loopBody) (.branch (compile_branchProgram_loopBranch ht bc bl))
    obtain ⟨value2,compiled⟩ := directExpression_noCode hv ctxt (ctxt.vmax+1) live
    rw [compileHOLExact,compiled]
    exact .seq (.branch .skip) (.seq (.branch (.assign _ _)) (suffix _ _))
  | @declLoop name value init condition body tail hv hi hc hb ht =>
    right
    apply optimise_sequence
    obtain ⟨value2,compiled⟩ := directExpression_noCode hv ctxt (ctxt.vmax+1) live
    rw [compileHOLExact,compiled]
    exact .seq (.branch .skip) (.seq (.branch (.assign _ _))
      (branchConditionWhileBranch_wordSimpShape init hi condition hc body tail hb ht _ _))

/-- The actual Crep-to-Loop program list contains only bitmap-free shapes
when every input body belongs to the supported fragment. -/
theorem supportedProgram_loopShapes {width : Nat} [NeZero width]
    (arch : Flapjack.Compiler.Encoders.Asm.AsmArchitecture)
    (programs : List (MlString × List Nat × CrepProgHOL width))
    (shapes : ∀ row ∈ programs, SupportedCodeBody row.2.2) :
    ∀ row ∈ compileProgHOLExact arch programs,
      TailEntryShape row.2.2 ∨ LoopSequenceSource row.2.2 := by
  intro row member
  obtain ⟨i,hi,hget⟩ := List.mem_iff_getElem.mp member
  have hlen : (compileProgHOLExact arch programs).length = programs.length := by
    simp only [compileProgHOLExact,List.length_zipWith,List.length_map,List.length_range,Nat.min_self]
  have hindex : i < programs.length := by rwa [← hlen]
  have hm : programs[i] ∈ programs := List.getElem_mem hindex
  have shape := shapes programs[i] hm
  have fixed := supportedCodeBody_simp_fixed shape
  have outputShape := supportedCodeBody_loopShape
    (mkCtxtExact arch (makeVmapExact programs[i].2.1) (crepToLoopMakeFuncsExactExecutable programs)
      (programs[i].2.1.length - 1))
    (listToNumSetHOLExact (List.range programs[i].2.1.length)) shape
  have eq : (compileProgHOLExact arch programs)[i].2.2 =
      optimiseHOL (compileHOLExact
        (mkCtxtExact arch (makeVmapExact programs[i].2.1) (crepToLoopMakeFuncsExactExecutable programs)
          (programs[i].2.1.length - 1))
        (listToNumSetHOLExact (List.range programs[i].2.1.length)) programs[i].2.2) := by
    simp only [compileProgHOLExact,List.getElem_zipWith,List.getElem_map,List.getElem_range,
      compFuncHOLExact,fixed]
  rw [← eq] at outputShape
  simpa only [hget] using outputShape

end SteppedFlapjack.CrepToLoopSteps
