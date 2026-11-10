import SteppedFlapjack.Concrete.NestedCrep
import SteppedFlapjack.CrepToLoopSteps.WholeCodeRel
/-! The multi-function witness instantiates the whole-program Crep/Loop code relation. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.RiscV.Target SteppedFlapjack.CrepToLoopSteps

def nestedCallCrepPrograms : List (MlString × List Nat × CrepProgHOL 64) := compileProgDeclsHOLW (compileTopExactHOL (nestedCallDeclarations.map declToHOL) (ofString "main"))

private theorem nestedCall_crep_fixed (name : MlString) (params : List Nat) (body : CrepProgHOL 64)
    (h : (name,params,body) ∈ nestedCallCrepPrograms) : crepSimpProgHOL body = body := by
  rw [nestedCallCrepPrograms,nestedCall_crep_code] at h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h | h | h | h <;> cases h <;> simp [crepSimpProgHOL,crepSimpExpHOL]

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

end SteppedFlapjack.Concrete
