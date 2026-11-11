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

private theorem nestedCall_crep_fixed (name : MlString) (params : List Nat) (body : CrepProgHOL 64)
    (h : (name,params,body) ∈ nestedCallCrepPrograms) : crepSimpProgHOL body = body := by
  rw [nestedCallCrepPrograms,compileProgDeclsHOLW,nestedCall_inline_selection_empty,
    CrepInlineRoute.compileInlTopHOLExact_nil] at h
  obtain ⟨ctxt,p,eq,shape⟩ := callFrontend_declaration_sources _ nestedCall_declaration_shapes (name,params,body) h
  simp only at eq
  rw [eq]
  exact callFrontend_simp_fixed shape

/-- The generated Loop table has the compiler code relation for every Crep function. -/
theorem nestedCall_loop_code_relation : crepToLoopCodeRelExact
      (mkCtxtExact riscvConfig.isa (makeVmapExact []) (crepToLoopMakeFuncsExactExecutable nestedCallCrepPrograms) 0)
      (alistToFmapCodeExact nestedCallCrepPrograms) (sptFromAList (compileProgHOLExact riscvConfig.isa nestedCallCrepPrograms)) := by
  apply wholeCrep_fixed_executable_codeRel _ nestedCallCrepPrograms (ofString "main") (.seq .skip (.call none (ofString "main'") []))
  · rw [nestedCallCrepPrograms,nestedCall_crep_code]; decide
  · rw [nestedCallCrepPrograms,nestedCall_crep_code]; rfl
  · exact nestedCall_crep_fixed

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
/-- The lowered source and generated Crep tables satisfy the compiler code relation. -/
theorem nestedCall_panCrep_code_relation : codeRelExactHOLW
      (mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL
        (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main")))) 0
        (getEidsFromDeclsHOL (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main"))))
      (HolFiniteMapExact.empty.updateList (functionsHOL (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main"))).reverse)
      (alistToFmapCodeExact nestedCallCrepPrograms) := by
  let decls := compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main")
  have unique : ((functionsHOL decls).map Prod.fst).Nodup := by
    dsimp only [decls]; rw [nestedCall_lowered_declarations]; decide
  have localised : ∀ entry ∈ functionsHOL decls, localisedProgHOL entry.2.2.1 = true := by
    dsimp only [decls]; rw [nestedCall_lowered_declarations]
    simp [functionsHOL,localisedProgHOL,localisedExpHOL,everyExpListHOL,everyExpHOL]
  have inlineNil : (functionsHOL (decls.filter inlinableHOL)).map Prod.fst = [] := by
    dsimp only [decls]; rw [nestedCall_lowered_declarations]; rfl
  have relation := mkCtxtCodeImpCodeRelExactHOLW decls unique localised
  change codeRelExactHOLW _ _ (HolFiniteMapExact.empty.updateList
    (compileProgDeclsHOLW decls).reverse)
  rw [compileProgDeclsHOLW,inlineNil,CrepInlineRoute.compileInlTopHOLExact_nil]
  exact relation

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
