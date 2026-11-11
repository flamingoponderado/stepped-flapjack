import SteppedFlapjack.Concrete.NestedCrep
import SteppedFlapjack.Concrete.NestedSourceHOL
import SteppedFlapjack.CrepToLoopSteps.WholeCodeRel
import SteppedFlapjack.CrepToLoopSteps.ExecutableFrontend
/-! The multi-function witness instantiates the whole-program Crep/Loop code relation. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.RiscV.Target SteppedFlapjack.CrepToLoopSteps
open SteppedFlapjack.LoopLiveSteps SteppedFlapjack.LoopToWordSteps

def nestedCallCrepPrograms : List (MlString × List Nat × CrepProgHOL 64) := compileProgDeclsHOLW (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main"))

/-- The generated four-function Crep table has maximum statement weight four. -/
theorem nestedCall_crep_codeWeight : SteppedFlapjack.CrepSteps.codeWeight nestedCallCrepPrograms = 4 := by
  rw [nestedCallCrepPrograms,nestedCall_crep_code]
  rfl

/-- The generated Loop table has the compiler code relation for every Crep function. -/
theorem nestedCall_loop_code_relation : crepToLoopCodeRelExact
      (mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable nestedCallCrepPrograms) 0)
      (alistToFmapCodeExact nestedCallCrepPrograms) (sptFromAList (compileProgHOLExact riscvConfig.isa nestedCallCrepPrograms)) := by
  apply callFrontend_declaration_crepLoop_codeRel _ _ nestedCall_inline_selection_empty nestedCall_declaration_shapes
    (ofString "main") (.seq .skip (.call none (ofString "main'") []))
  · rw [nestedCall_lowered_declarations]; decide
  · rw [nestedCall_crep_code]; rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- The lowered source and generated Crep tables satisfy the compiler code relation. -/
theorem nestedCall_panCrep_code_relation : codeRelExactHOLW
      (mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL
        (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main")))) 0
        (getEidsFromDeclsHOL (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main"))))
      (HolFiniteMapExact.empty.updateList (functionsHOL (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main"))).reverse)
      (alistToFmapCodeExact nestedCallCrepPrograms) := by
  apply callFrontend_declaration_codeRel
  · rw [nestedCall_lowered_declarations]
    decide
  · exact nestedCall_inline_selection_empty
  · exact nestedCall_declaration_shapes

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
