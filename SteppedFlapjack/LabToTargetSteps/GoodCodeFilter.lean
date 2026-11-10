import Flapjack.Compiler.Backend.LabToTarget.GoodCode
import Flapjack.Compiler.Backend.LabToTarget.FilterSkipSafety
import Flapjack.Compiler.Backend.LabToTarget.SkipFilterPreconditions
import Flapjack.Compiler.Backend.LabFilter.Proofs.SectionEnd

/-! Skip filtering preserves Lab code safety. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabProps.LabelSets
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabToTarget.FilterSkip
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Encoders.Asm Flapjack.Misc

/-- Skip filtering preserves each of the actual Lab code-safety conditions. -/
theorem goodCode_filterSkip {width : Nat} [NeZero width] {G : Type}
    (config : AsmConfigExact width) (labels : Spt (Spt G)) (code : LabProgHOL width)
    (good : goodCode config labels code) : goodCode config labels (filterSkip code) := by
  obtain ⟨hend,hsec,hdistinct,hlabels,hdisjoint,htargets,hpre⟩ := good
  refine ⟨LabFilter.Proofs.secEndsWithLabelFilterSkip code hend,?_,?_,?_,?_,?_,allEncOkPreFilterSkip code config hpre⟩
  · intro sec hmem line hline
    rw [filterSkipMap] at hmem
    obtain ⟨original,horiginal,rfl⟩ := List.mem_map.mp hmem
    exact hsec original horiginal line (List.mem_filter.mp hline).1
  · simpa only [mapSectionNumFilterSkip] using hdistinct
  · intro sec hmem
    have hm : LabelSets.extractLabels sec.lines ∈ (filterSkip code).map (fun sectionData => LabelSets.extractLabels sectionData.lines) :=
      List.mem_map.mpr ⟨sec,hmem,rfl⟩
    rw [filterSkipExtractLabels] at hm
    obtain ⟨original,horiginal,heq⟩ := List.mem_map.mp hm
    rw [← heq]
    exact hlabels original horiginal
  · simpa only [mapSectionNumFilterSkip] using hdisjoint
  · simpa only [getLabelsFilterSkip,getCodeLabelsFilterSkip] using htargets

end SteppedFlapjack.PanToCrepSteps
