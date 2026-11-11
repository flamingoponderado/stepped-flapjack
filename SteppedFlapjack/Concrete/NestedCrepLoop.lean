import SteppedFlapjack.Concrete.NestedCrep
import SteppedFlapjack.Concrete.NestedSourceHOL
import SteppedFlapjack.CrepToLoopSteps.WholeCodeRel
import SteppedFlapjack.CrepToLoopSteps.ExecutableFrontend
/-! The multi-function witness instantiates the whole-program Crep/Loop code relation. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString Flapjack.PanSemStateFiniteExact
open SteppedFlapjack.PanToCrepSteps
open Flapjack.Compiler.Encoders.RiscV.Target SteppedFlapjack.CrepToLoopSteps
open SteppedFlapjack.LoopLiveSteps SteppedFlapjack.LoopToWordSteps

def nestedCallCrepPrograms : List (MlString × List Nat × CrepProgHOL 64) := compileProgDeclsHOLW (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main"))

/-- The source configuration immediately before the generated entry call. -/
def nestedLoweredSource : PanSemStateFiniteExact 64 Unit :=
  noGlobalsLoweredPreCall {sourceTemplate with clock := 6}
    (HolFiniteMapExact.empty.updateList
      (functionsHOL (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main"))).reverse)

/-- The lowered wrapper follows the same two nested calls and returns seven. -/
theorem nestedLoweredSource_run : ∃ final,
    nestedLoweredSource.evaluateHOLFiniteState (.seq .skip (.call none (ofString "main'") [])) =
      (some (.returned (.val (.word 7))),final) ∧ final.ffi = sourceFfi := by
  have a : (ofString "main" == ofString "main'") = false := by decide
  have b : (ofString "main" == ofString "middle") = false := by decide
  have c : (ofString "main'" == ofString "middle") = false := by decide
  have d : (ofString "main" == ofString "leaf") = false := by decide
  have e : (ofString "main'" == ofString "leaf") = false := by decide
  have f : (ofString "middle" == ofString "leaf") = false := by decide
  simp [a,b,c,d,e,f,nestedLoweredSource,noGlobalsLoweredPreCall,nestedCall_lowered_declarations,
    functionsHOL,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_skip,evaluateHOLFiniteState_call,
    evaluateHOLFiniteState_decCall_fixClockRewrite,evaluateHOLFiniteState_return,evalListHOLFinite,evalListHOLExact,
    PanSemStateFiniteExact.lookupCodeHOLFinite,lookupCodeHOLExact,HolFiniteMapExact.lookup_updateList,FUPDATE_LIST,
    HolFiniteMapExact.lookup_update,FUPDATE,callEntryStateHOLFinite,evalHOLExact,
    shapeOfHOLExact,shapeEqHOL,setVarHOLFinite,emptyLocalsHOLFinite,sourceTemplate]

/-- The wrapper visit limit is computed from the counted source run and source declarations. -/
def nestedSourceEntryLimit : Nat :=
  1 + SimpVisits.simpTableFactor (functionsHOL (nestedCallDeclarations.map declToHOL)) * 6 +
    SimpVisits.hw (progToHOL (panSimpProg nestedCallEntry)) + 2

/-- The shared structural optimizer computes the original Loop compiler output
for every function of the nested-call witness. -/
theorem nestedCall_structuralLive_eq :
    compileProgWithStructuralLive riscvConfig.isa nestedCallCrepPrograms =
      compileProgHOLExact riscvConfig.isa nestedCallCrepPrograms := by
  rw [nestedCallCrepPrograms,compileProgDeclsHOLW,nestedCall_inline_selection_empty,
    CrepInlineRoute.compileInlTopHOLExact_nil]
  exact callFrontend_compileProgWithStructuralLive_eq _ _
    (callFrontend_declaration_sources _ nestedCall_declaration_shapes)

def nestedLoopLive1 : NumSet := sptInsert 1 () .ln

def nestedLoopCode64 : HolLoopProg 64 :=
 .mark (.seq (.mark .skip) (.mark (.seq (.mark (.call none (some 65) [] none)) (.mark .skip))))

def nestedLoopCode65 : HolLoopProg 64 :=
 .mark <| .seq (.mark .skip) <| .mark <| .seq (.mark .skip) <| .mark <| .seq
   (.mark <| .seq (.mark <| .call (some ([1],.ln)) (some 66) [] (some (2,.mark (.raise 2),.mark .skip,nestedLoopLive1))) (.mark .skip))
   (.mark <| .seq (.mark (.assign 2 (.var 1))) (.mark <| .seq (.mark (.return [2])) (.mark .skip)))

def nestedLoopCode66 : HolLoopProg 64 :=
 .mark (.seq (.mark (.call none (some 67) [] none)) (.mark .skip))

def nestedLoopCode67 : HolLoopProg 64 :=
 .mark (.seq (.mark (.assign 1 (.const 7))) (.mark (.seq (.mark (.return [1])) (.mark .skip))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- The real Loop compiler produces the four concrete optimized functions. -/
theorem nestedCall_loop_code : compileProgHOLExact riscvConfig.isa nestedCallCrepPrograms =
 [(64,[],nestedLoopCode64),(65,[],nestedLoopCode65),(66,[],nestedLoopCode66),(67,[],nestedLoopCode67)] := by
  rw [← nestedCall_structuralLive_eq]
  rw [nestedCallCrepPrograms,nestedCall_crep_code]
  with_unfolding_all rfl

end SteppedFlapjack.Concrete
