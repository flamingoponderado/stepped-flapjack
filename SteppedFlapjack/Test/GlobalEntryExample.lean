import SteppedFlapjack.PanToCrepSteps.TailEntryRelations

/-! Concrete frontend satisfiability checks, including a nonempty one-loop
function table. These do not instantiate the global call or backend premises. -/
namespace SteppedFlapjack.Test.GlobalEntryExample
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString SteppedFlapjack.PanToCrepSteps

private def ffi : HolFfiState Unit :=
  { oracle := fun _ state _ _ => .ret state [], ffiState := (), ioEvents := [] }

private def pan : PanSemStateFiniteExact 64 Unit where
  locals := HolFiniteMapExact.empty
  globals := HolFiniteMapExact.empty
  structs := []
  code := HolFiniteMapExact.empty
  eshapes := HolFiniteMapExact.empty
  memory := fun _ => .word 0
  memaddrs := fun _ => False
  shMemaddrs := fun _ => False
  clock := 10
  be := false
  ffi := ffi
  baseAddr := 0
  topAddr := 0

private def crep : CrepSemHOLState 64 Unit where
  locals := HolFiniteMapExact.empty
  globals := HolFiniteMapExact.empty
  code := HolFiniteMapExact.empty
  memory := fun _ => .word 0
  memaddrs := fun _ => False
  shMemaddrs := fun _ => False
  clock := 10
  be := false
  ffi := ffi
  baseAddr := 0
  topAddr := 0

private def context : PanToCrepContextExact 64 where
  vars := HolFiniteMapExact.empty
  funcs := HolFiniteMapExact.empty
  eids := HolFiniteMapExact.empty
  vmax := 0

/-- Concrete, simultaneous source/target frontend relations. -/
example : panToCrepStateRelFiniteExact pan crep ∧
    codeRelExactHOLW context pan.code crep.code ∧
    panToCrepExcpRelFiniteExact context.eids pan.eshapes ∧
    panToCrepLocalsRelFiniteExact context pan.locals crep.locals := by
  refine ⟨⟨rfl,rfl,rfl,rfl,by funext key; rfl,rfl,rfl,rfl,rfl,rfl⟩,?_,?_,?_⟩
  · intro function variableShapes program returnShape lookup
    simp [pan, HolFiniteMapExact.empty] at lookup
  · simp [panToCrepExcpRelFiniteExact, context, pan, HolFiniteMapExact.empty]
  · simp [panToCrepLocalsRelFiniteExact, noOverlapFiniteExact,
      ctxtMaxFiniteExact, pan, context, HolFiniteMapExact.empty]

/-- The concrete zero-condition loop terminates without a source error. -/
example : (PanSemStateFiniteExact.evaluateHOLFiniteState pan
    (.while (.const 0) .skip)).1 = none := by
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_while_total]
  rfl

/-- A concrete one-loop body meets the frontend syntactic requirements, and
its condition is compiled to a single Crep expression. -/
example : ∃ condition : CrepExpHOL 64,
    compileExpExactHOLW (ctxtFcExactHOL context.funcs context.eids [] [] []) (.const 0) =
      ([condition],.one) ∧
    CrepToLoopSteps.BranchProgram (compileProgExactHOLW context .skip) ∧
    compileProgExactHOLW (ctxtFcExactHOL context.funcs context.eids [] [] [])
        (.seq .skip (.seq (.while (.const 0) .skip) (.return (.const 7)))) =
      .seq (compileProgExactHOLW (ctxtFcExactHOL context.funcs context.eids [] [] []) .skip)
        (.seq (.while condition (compileProgExactHOLW (ctxtFcExactHOL context.funcs context.eids [] [] []) .skip))
          (compileProgExactHOLW (ctxtFcExactHOL context.funcs context.eids [] [] []) (.return (.const 7)))) := by
  obtain ⟨condition,compiled,_,init,_,_,_,body⟩ :=
    tailEntry_compiled_shapes context .skip .skip (.const 0) .skip (.return (.const 7))
      .skip .skip (.const 0) .skip (.return (.const 7))
  exact ⟨condition,compiled,init,body⟩

private def oneLoopFunction : FunDeclHOL 64 where
  name := ofString "main"
  inline := false
  exported := false
  params := []
  body := .seq .skip (.seq (.while (.const 0) .skip) (.return (.const 7)))
  returnShape := .one

private def oneLoopDeclarations : List (DeclHOL 64) := [.function oneLoopFunction]

/-- A nonempty, concrete source function table and its compiler-generated
Crep table satisfy the complete Pancake-to-Crep code relation. -/
private theorem oneLoopCodeRel : codeRelExactHOLW
    (mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL oneLoopDeclarations)) 0
      (getEidsFromDeclsHOL oneLoopDeclarations))
    (HolFiniteMapExact.empty.updateList (functionsHOL oneLoopDeclarations).reverse)
    (HolFiniteMapExact.empty.updateList (compileToCrepExactHOLW oneLoopDeclarations).reverse) := by
  apply mkCtxtCodeImpCodeRelExactHOLW
  · simp [oneLoopDeclarations, functionsHOL]
  · intro entry member
    simp [oneLoopDeclarations, functionsHOL] at member
    subst entry
    rfl

/-- The concrete one-loop source and compiled Crep code tables coexist
with the initial state, exception and local relations. -/
example :
    let ctx := mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL oneLoopDeclarations)) 0
      (getEidsFromDeclsHOL oneLoopDeclarations)
    let p := {pan with code := HolFiniteMapExact.empty.updateList (functionsHOL oneLoopDeclarations).reverse}
    let q := {crep with code := HolFiniteMapExact.empty.updateList (compileToCrepExactHOLW oneLoopDeclarations).reverse}
    panToCrepStateRelFiniteExact p q ∧ codeRelExactHOLW ctx p.code q.code ∧
      panToCrepExcpRelFiniteExact ctx.eids p.eshapes ∧
      panToCrepLocalsRelFiniteExact ctx p.locals q.locals := by
  refine ⟨⟨rfl,rfl,rfl,rfl,by funext key; rfl,rfl,rfl,rfl,rfl,rfl⟩,oneLoopCodeRel,?_,?_⟩
  · simp [panToCrepExcpRelFiniteExact, mkCtxtExactHOL, pan, HolFiniteMapExact.empty,
      getEidsFromDeclsHOL, getEidsEntriesHOL, exceptionsHOL, isExnDeclHOL, alistToFmap, FEMPTY,
      oneLoopDeclarations, oneLoopFunction]
  · simp [panToCrepLocalsRelFiniteExact, noOverlapFiniteExact, ctxtMaxFiniteExact,
      mkCtxtExactHOL, pan, crep, HolFiniteMapExact.empty]

end SteppedFlapjack.Test.GlobalEntryExample
