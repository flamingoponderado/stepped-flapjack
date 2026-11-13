import SteppedFlapjack.Concrete.CountedSource
import SteppedFlapjack.Concrete.FrontendShape
import SteppedFlapjack.PanToCrepSteps.GlobalFrontendControl
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString SteppedFlapjack.PanToCrepSteps

def GlobalLayout (shapes : VarName → Option ShapeHOL) (globals : PanGlobalsContextExact 64) : Prop :=
  ∀ name shape, shapes name = some shape → ∃ offset, globals.globals.lookup (ofString name) = some (shape,offset)

theorem globalRead_path {shapes : VarName → Option ShapeHOL} {e : Exp (RiscV.Word 64)} {shape : ShapeHOL}
    (read : GlobalRead shapes e shape) :
    ∃ name rootShape, shapes name = some rootShape ∧
      FieldPath (.var .global (ofString name)) rootShape (expToHOL e) shape := by
  induction read with
  | global name shape ranged found => exact ⟨name,shape,found,by simpa [expToHOL] using (FieldPath.root (root := .var .global (ofString name)) (rootShape := shape))⟩
  | field path index shape found ih =>
    obtain ⟨name,rootShape,lookup,rootPath⟩ := ih
    exact ⟨name,rootShape,lookup,by simpa [expToHOL] using FieldPath.field rootPath index shape found⟩

theorem fieldPath_atomic {root e : ExpHOL 64} {rootShape shape : ShapeHOL}
    (path : FieldPath root rootShape e shape) (atom : ∀ fields, rootShape ≠ .comb fields) :
    e = root ∧ shape = rootShape := by
  induction path with
  | root => exact ⟨rfl,rfl⟩
  | field path index shape found ih =>
    obtain ⟨_,eq⟩ := ih
    exact False.elim (atom _ eq.symm)

theorem globalRead_frontend {shapes : VarName → Option ShapeHOL} {globals : PanGlobalsContextExact 64}
    {ctxt : PanToCrepContextExact 64} (layout : GlobalLayout shapes globals)
    {e : Exp (RiscV.Word 64)} (read : GlobalRead shapes e .one) :
    PanToCrepSteps.GlobalScalar globals ctxt (expToHOL e) := by
  obtain ⟨name,rootShape,found,path⟩ := globalRead_path read
  obtain ⟨offset,lookup⟩ := layout name rootShape found
  cases rootShape with
  | one =>
    obtain ⟨eq,_⟩ := fieldPath_atomic path (by intro fields h; cases h)
    rw [eq]
    exact .globalWord (ofString name) offset lookup
  | named tag =>
    obtain ⟨_,impossible⟩ := fieldPath_atomic path (by intro fields h; cases h)
    cases impossible
  | comb fields => exact .globalPath (ofString name) offset fields lookup path
theorem globalScalar_frontend {shapes : VarName → Option ShapeHOL} {globals : PanGlobalsContextExact 64}
    {scope : List VarName} {ctxt : PanToCrepContextExact 64} (layout : GlobalLayout shapes globals)
    (relation : ScopeRelation scope ctxt) {e : Exp (RiscV.Word 64)} (scalar : GlobalScalarExpression shapes scope e) :
    PanToCrepSteps.GlobalScalar globals ctxt (expToHOL e) := by
  induction scalar with
  | «local» h => exact .local (scalar_frontend_shape relation h)
  | global h => exact globalRead_frontend layout h
  | load h ih => simpa [expToHOL,shapeToHOL] using PanToCrepSteps.GlobalScalar.load ih
  | heapField fields index selected address ih =>
    simp only [expToHOL, shapeToHOL]
    apply PanToCrepSteps.GlobalScalar.heapField (fields.map shapeToHOL) index
    · simp [List.getElem?_map, selected, shapeToHOL]
    · simpa [expToHOL, shapeToHOL] using ih
  | op op a b iha ihb => simpa [expToHOL] using PanToCrepSteps.GlobalScalar.op op iha ihb
  | cmp op a b iha ihb => simpa [expToHOL] using PanToCrepSteps.GlobalScalar.cmp op iha ihb
  | shift op a b iha ihb => simpa [expToHOL] using PanToCrepSteps.GlobalScalar.shift op iha ihb

theorem globalValue_frontend {shapes : VarName → Option ShapeHOL} {globals : PanGlobalsContextExact 64}
    {scope : List VarName} {ctxt : PanToCrepContextExact 64} (layout : GlobalLayout shapes globals)
    (relation : ScopeRelation scope ctxt) {e : Exp (RiscV.Word 64)} (h : GlobalValueExpression shapes scope e) :
    GlobalValue globals ctxt (expToHOL e) := by
  induction h with
  | scalar h => exact .scalar (globalScalar_frontend layout relation h)
  | tuple fields ih =>
    simp only [expToHOL]
    apply GlobalValue.tuple
    intro e member
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
    exact ih original originalMember

theorem globalCallSupported_frontend {shapes : VarName → Option ShapeHOL} {globals : PanGlobalsContextExact 64}
    {scope : List VarName} {program : Prog (RiscV.Word 64)} (layout : GlobalLayout shapes globals)
    (supported : GlobalCallSupportedIn shapes scope program) : ∀ ctxt, ScopeRelation scope ctxt →
      GlobalCallFrontend globals ctxt (progToHOL program) := by
  induction supported with
  | base h =>
    intro ctxt rel
    exact .base (GlobalFrontend.of_frontend globals (supportedIn_frontend_shape h ctxt rel))
  | assignGlobalWord name found scalar =>
    intro ctxt rel
    obtain ⟨offset,lookup⟩ := layout name .one found
    simpa [progToHOL] using (GlobalCallFrontend.base (GlobalFrontend.assignGlobal lookup (globalScalar_frontend layout rel scalar)))
  | assignGlobalStruct name fieldShapes found fields =>
    intro ctxt rel
    obtain ⟨offset,lookup⟩ := layout name (.comb fieldShapes) found
    apply GlobalCallFrontend.base
    simp only [progToHOL,expToHOL]
    apply GlobalFrontend.assignGlobalStruct lookup
    intro e member
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
    exact globalValue_frontend layout rel (fields original originalMember)
  | ret scalar =>
    intro ctxt rel
    simpa [progToHOL] using (GlobalCallFrontend.base (GlobalFrontend.ret (globalScalar_frontend layout rel scalar)))
  | assignLocal name member scalar =>
    intro ctxt rel
    obtain ⟨reg,found⟩ := rel name member
    simpa [progToHOL] using (GlobalCallFrontend.base (GlobalFrontend.assignLocal reg found (globalScalar_frontend layout rel scalar)))
  | store address value =>
    intro ctxt rel
    cases value with
    | scalar h =>
      simpa [progToHOL] using (GlobalCallFrontend.base (GlobalFrontend.store (globalScalar_frontend layout rel address) (globalScalar_frontend layout rel h)))
    | tuple fields =>
      apply GlobalCallFrontend.base
      simp only [progToHOL,expToHOL]
      apply GlobalFrontend.storeStruct (globalScalar_frontend layout rel address)
      intro e member
      obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
      exact globalValue_frontend layout rel (fields original originalMember)
  | tail name args hs =>
    intro ctxt rel
    simp only [progToHOL]
    apply GlobalCallFrontend.tail
    intro e member
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
    exact globalScalar_frontend layout rel (hs original originalMember)
  | call dest name args hs body ih =>
    intro ctxt rel
    simp only [progToHOL,shapeToHOL]
    apply GlobalCallFrontend.decCall
    · intro e member
      obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
      exact globalScalar_frontend layout rel (hs original originalMember)
    · have eq : decCallCtxt ctxt (ofString dest) .one = scalarDeclContext ctxt (ofString dest) := by
        simp [decCallCtxt,decCallSlots,scalarDeclContext,sizeOfShapeHOL]
      rw [eq]
      exact ih _ (rel.declare dest)
  | decl name scalar body ih =>
    intro ctxt rel
    simpa [progToHOL,shapeToHOL] using GlobalCallFrontend.decl (globalScalar_frontend layout rel scalar) (ih _ (rel.declare name))
  | seq a b iha ihb =>
    intro ctxt rel
    simpa [progToHOL] using GlobalCallFrontend.seq (iha ctxt rel) (ihb ctxt rel)
  | ite scalar a b iha ihb =>
    intro ctxt rel
    simpa [progToHOL] using GlobalCallFrontend.ite (globalScalar_frontend layout rel scalar) (iha ctxt rel) (ihb ctxt rel)
  | «while» scalar body ih =>
    intro ctxt rel
    simpa [progToHOL] using GlobalCallFrontend.while (globalScalar_frontend layout rel scalar) (ih ctxt rel)

/-- Related production code automatically supplies the global-aware source table. -/
theorem globalSupported_sourceTable {σ : Type} (shapes : VarName → Option ShapeHOL)
    (globals : PanGlobalsContextExact 64) (layout : GlobalLayout shapes globals)
    (production : PanSemState (RiscV.Word 64) (FfiState σ)) (source : PanSemStateFiniteExact 64 σ)
    (rel : PanSemStateRelExec production source.toExact)
    (codeShape : ∀ name params body, (name,params,body) ∈ countedFunctionsOfCode production.code →
      ∃ scope, GlobalCallSupportedIn shapes scope body) :
    GlobalCallTable globals source.code := by
  intro name values body locals rsh found
  have raw := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some source.code.lookup name values body locals rsh found
  have hn : NameRanged (toStringOfBytes name) := nameRanged_toStringOfBytes_bridge name
  have codeRel := rel.2.2.2.1 (toStringOfBytes name) hn
  rw [ofString_toStringOfBytes] at codeRel
  cases prodCode : panSemCodeLookup production.code (toStringOfBytes name) with
  | none =>
    simp only [prodCode,Option.map_none] at codeRel
    simp [lookupCodeHOLExact, ← codeRel] at raw
  | some entry =>
    obtain ⟨params, sourceBody, returnShape⟩ := entry
    simp only [prodCode,Option.map_some] at codeRel
    have lookup : source.code.lookup name = some (panLangEntryToHOL (params,sourceBody,returnShape)) := codeRel.symm
    simp only [lookupCodeHOLExact,lookup] at raw
    split at raw
    · simp only [Option.some.injEq,Prod.mk.injEq] at raw
      obtain ⟨bodyEq,_,_⟩ := raw
      have tableLookup := countedFunctionLookup production.code (toStringOfBytes name)
      rw [prodCode] at tableLookup
      have member := lookupPanFunction_mem tableLookup
      obtain ⟨scope,supported⟩ := codeShape _ _ _ member
      let ctxt : PanToCrepContextExact 64 := mkCtxtExactHOL (panToCrepMakeVmapHOLExact (scope.map (fun n => (ofString n,ShapeHOL.one))))
        HolFiniteMapExact.empty (sizeOfShapeHOL (.comb (scope.map (fun _ => ShapeHOL.one))) - 1) HolFiniteMapExact.empty
      refine ⟨ctxt,?_⟩
      have h := globalCallSupported_frontend layout supported ctxt (scalar_parameter_scope scope HolFiniteMapExact.empty HolFiniteMapExact.empty)
      simpa [panLangEntryToHOL] using bodyEq ▸ h
    · simp at raw

end SteppedFlapjack.Concrete
