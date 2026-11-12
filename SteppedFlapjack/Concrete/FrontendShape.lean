import SteppedFlapjack.PanToCrepSteps.WhileSteps
import SteppedFlapjack.Concrete.SourceRuns
import SteppedFlapjack.PanToCrepSteps.FrontendProgram

/-! Connect source scalar syntax to the frontend's singleton-result expressions. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open SteppedFlapjack.PanToCrepSteps

/-- Each in-scope source variable has a scalar register in the frontend context. -/
def ScopeRelation (scope : List VarName) (ctxt : PanToCrepContextExact 64) : Prop :=
  ∀ name ∈ scope, ∃ reg, ctxt.vars.lookup (ofString name) = some (.one,[reg])

/-- Source scalar syntax has the generalized frontend shape when its locals
are represented in the compiler context. -/
theorem scalar_frontend_shape {scope : List VarName} {ctxt : PanToCrepContextExact 64}
    (relation : ScopeRelation scope ctxt) {e : Exp (RiscV.Word 64)} (scalar : Scalar scope e) :
    FrontendScalar ctxt (expToHOL e) := by
  induction scalar with
  | const v => simpa [expToHOL] using (FrontendScalar.const (ctxt := ctxt) v)
  | «local» name member =>
    obtain ⟨reg,found⟩ := relation name member
    simpa [expToHOL] using (FrontendScalar.local (ofString name) reg found)
  | load address ih => simpa [expToHOL,shapeToHOL] using (FrontendScalar.load ih)
  | op op a b iha ihb => simpa [expToHOL] using (FrontendScalar.op op iha ihb)
  | cmp op a b iha ihb => simpa [expToHOL] using (FrontendScalar.cmp op iha ihb)
  | shift op a b iha ihb => simpa [expToHOL] using (FrontendScalar.shift op iha ihb)

/-- A new declaration extends the register context, including shadowing. -/
theorem ScopeRelation.declare {scope : List VarName} {ctxt : PanToCrepContextExact 64}
    (relation : ScopeRelation scope ctxt) (name : VarName) :
    ScopeRelation (name :: scope) (scalarDeclContext ctxt (ofString name)) := by
  intro item member
  simp only [List.mem_cons] at member
  rcases member with eq | member
  · subst item
    exact ⟨_,scalarDeclContext_local ctxt (ofString name)⟩
  · by_cases same : ofString item = ofString name
    · exact ⟨_,by rw [same]; exact scalarDeclContext_local ctxt (ofString name)⟩
    · obtain ⟨reg,found⟩ := relation item member
      refine ⟨reg,?_⟩
      simpa [scalarDeclContext,HolFiniteMapExact.lookup_update,FUPDATE,same,Ne.symm same] using found

/-- All supported source programs have the generalized frontend shape. -/
theorem supportedIn_frontend_shape {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) : ∀ ctxt, ScopeRelation scope ctxt →
      FrontendProgram ctxt (progToHOL program) := by
  induction supported with
  | skip => intro ctxt relation; simpa [progToHOL] using (FrontendProgram.skip (ctxt := ctxt))
  | assign name member e =>
    intro ctxt relation
    obtain ⟨reg,found⟩ := relation name member
    simpa [progToHOL] using (FrontendProgram.assign reg found (scalar_frontend_shape relation e))
  | decl name e body ih =>
    intro ctxt relation
    simpa [progToHOL,shapeToHOL] using
      (FrontendProgram.decl (scalar_frontend_shape relation e) (ih _ (relation.declare name)))
  | seq a b iha ihb =>
    intro ctxt relation
    simpa [progToHOL] using (FrontendProgram.seq (iha ctxt relation) (ihb ctxt relation))
  | ite e a b iha ihb =>
    intro ctxt relation
    simpa [progToHOL] using (FrontendProgram.ite (scalar_frontend_shape relation e) (iha ctxt relation) (ihb ctxt relation))
  | «while» e body ih =>
    intro ctxt relation
    simpa [progToHOL] using (FrontendProgram.while (scalar_frontend_shape relation e) (ih ctxt relation))
  | ret e =>
    intro ctxt relation
    simpa [progToHOL] using (FrontendProgram.ret (scalar_frontend_shape relation e))

theorem supported_frontend_shape {program : Prog (RiscV.Word 64)} (supported : CallFreeSupported program)
    (ctxt : PanToCrepContextExact 64) : FrontendProgram ctxt (progToHOL program) :=
  supportedIn_frontend_shape supported.1 ctxt (by intro name member; simp at member)

private theorem callContext_scalar (ctxt : PanToCrepContextExact 64) (name : MlS) :
    decCallCtxt ctxt name .one = scalarDeclContext ctxt name := by
  simp [decCallCtxt,decCallSlots,scalarDeclContext,sizeOfShapeHOL]
/-- Every call-supported source body has the call-aware frontend shape. -/
theorem callSupported_frontend_shape {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope program) : ∀ ctxt, ScopeRelation scope ctxt →
      CallFrontend ctxt (progToHOL program) := by
  induction supported with
  | base h => intro ctxt relation; exact .base (supportedIn_frontend_shape h ctxt relation)
  | tail name args shape =>
    intro ctxt relation
    simp only [progToHOL]
    apply CallFrontend.tail
    intro e member
    obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
    exact scalar_frontend_shape relation (shape original originalMember)
  | call dest name args shape cont ih =>
    intro ctxt relation
    simp only [progToHOL,shapeToHOL]
    apply CallFrontend.decCall
    · intro e member
      obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp member
      exact scalar_frontend_shape relation (shape original originalMember)
    · rw [callContext_scalar]
      exact ih _ (relation.declare dest)
  | decl name e body ih =>
    intro ctxt relation
    simpa only [progToHOL,shapeToHOL] using CallFrontend.decl (scalar_frontend_shape relation e) (ih _ (relation.declare name))
  | seq a b iha ihb => intro ctxt relation; simpa only [progToHOL] using CallFrontend.seq (iha ctxt relation) (ihb ctxt relation)
  | ite e a b iha ihb => intro ctxt relation; simpa only [progToHOL] using CallFrontend.ite (scalar_frontend_shape relation e) (iha ctxt relation) (ihb ctxt relation)
  | «while» e body ih => intro ctxt relation; simpa only [progToHOL] using CallFrontend.while (scalar_frontend_shape relation e) (ih ctxt relation)

private def scalarParamEntries : List VarName → Nat → List (MlS × (ShapeHOL × List Nat))
  | [], _ => []
  | n :: ns, off => (ofString n,(.one,[off])) :: scalarParamEntries ns (off+1)
private def scalarShapeSlots : List ShapeHOL → Nat → List (List Nat)
  | [], _ => []
  | shape :: shapes, offset =>
      (List.range (sizeOfShapeHOL shape)).map (offset + ·) ::
        scalarShapeSlots shapes (offset + sizeOfShapeHOL shape)

private theorem scalarShapeSlots_correct (shapes : List ShapeHOL) (offset : Nat) :
    withShapeHOL shapes ((List.range (sizeOfShapeHOL (.comb shapes))).map (offset + ·)) =
      scalarShapeSlots shapes offset := by
  induction shapes generalizing offset with
  | nil => simp [withShapeHOL,scalarShapeSlots]
  | cons shape shapes ih =>
    simp only [withShapeHOL,scalarShapeSlots,sizeOfShapeHOL,sizeOfShapesHOL]
    rw [List.range_add]
    have htail := ih (offset + sizeOfShapeHOL shape)
    simpa [sizeOfShapeHOL,sizeOfShapesHOL,Nat.add_assoc,Function.comp_def] using htail

private theorem scalarEntries_exact (names : List VarName) (offset : Nat) :
    scalarParamEntries names offset =
      (names.map (fun n => ofString n)).zip
        ((names.map (fun _ => ShapeHOL.one)).zip
          (withShapeHOL (names.map (fun _ => ShapeHOL.one))
            ((List.range (sizeOfShapeHOL (.comb (names.map (fun _ => ShapeHOL.one))))).map (offset + ·)))) := by
  induction names generalizing offset with
  | nil => simp [scalarParamEntries]
  | cons name names ih =>
    simp only [scalarParamEntries,List.map_cons]
    rw [scalarShapeSlots_correct]
    simp only [scalarShapeSlots,sizeOfShapeHOL,List.range_one,List.map_cons,List.map_nil,List.zip_cons_cons,Nat.add_zero]
    have tail := ih (offset+1)
    rw [scalarShapeSlots_correct] at tail
    exact congrArg (List.cons _) tail

private theorem scalarEntries_lookup (names : List VarName) (offset : Nat) (m : FiniteMap MlS (ShapeHOL × List Nat))
    (key : MlS) (prior : (∃ reg, FLOOKUP m key = some (.one,[reg])) ∨ ∃ n ∈ names, ofString n = key) :
    ∃ reg, FLOOKUP (FUPDATE_LIST m (scalarParamEntries names offset)) key = some (.one,[reg]) := by
  induction names generalizing offset m with
  | nil =>
    simp only [scalarParamEntries,FUPDATE_LIST_nil] at *
    rcases prior with h | ⟨_,h,_⟩
    · exact h
    · cases h
  | cons n ns ih =>
    simp only [scalarParamEntries,FUPDATE_LIST_cons]
    apply ih
    rcases prior with h | ⟨x,hx,eq⟩
    · by_cases hk : ofString n = key
      · left; refine ⟨offset,?_⟩; simp [FLOOKUP,FUPDATE,hk]
      · left; obtain ⟨reg,hr⟩ := h; refine ⟨reg,?_⟩; simpa [FLOOKUP,FUPDATE,hk] using hr
    · simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · left; refine ⟨offset,?_⟩; simp [FLOOKUP,FUPDATE,eq]
      · exact Or.inr ⟨x,hx,eq⟩
/-- Scalar function parameters provide a register for each in-scope name. -/
theorem scalar_parameter_scope (names : List VarName) (funcs : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ShapeHOL))
    (eids : HolFiniteMapExact MlS (BitVec 64)) :
    ScopeRelation names (mkCtxtExactHOL
      (panToCrepMakeVmapHOLExact (names.map (fun n => (ofString n,ShapeHOL.one)))) funcs
      (sizeOfShapeHOL (.comb (names.map (fun _ => ShapeHOL.one))) - 1) eids) := by
  intro name member
  have vals : (names.map (fun n => ofString n)).zip
      ((names.map (fun _ => ShapeHOL.one)).zip
        (withShapeHOL (names.map (fun _ => ShapeHOL.one))
          (List.range (sizeOfShapeHOL (.comb (names.map (fun _ => ShapeHOL.one))))))) = scalarParamEntries names 0 := by
    simpa using (scalarEntries_exact names 0).symm
  have got := scalarEntries_lookup names 0 FEMPTY (ofString name) (Or.inr ⟨name,member,rfl⟩)
  simp only [mkCtxtExactHOL,panToCrepMakeVmapHOLExact,List.map_map,Function.comp_def,vals,
    HolFiniteMapExact.lookup_updateList]
  exact got
/-- A scalar-parameter function body has the frontend shape in its compiler-generated context. -/
theorem callSupported_scalarFunction_frontend (names : List VarName) {program : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn names program) (funcs : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ShapeHOL))
    (eids : HolFiniteMapExact MlS (BitVec 64)) :
    CallFrontend (mkCtxtExactHOL (panToCrepMakeVmapHOLExact (names.map (fun n => (ofString n,ShapeHOL.one))))
      funcs (sizeOfShapeHOL (.comb (names.map (fun _ => ShapeHOL.one))) - 1) eids) (progToHOL program) :=
  callSupported_frontend_shape supported _ (scalar_parameter_scope names funcs eids)

/-- A function may pass its scalar argument through an ordinary call and return the result. -/
theorem scalar_argument_call_frontend (funcs : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ShapeHOL))
    (eids : HolFiniteMapExact MlS (BitVec 64)) :
    CallFrontend (mkCtxtExactHOL (panToCrepMakeVmapHOLExact [(ofString "x",ShapeHOL.one)])
      funcs (sizeOfShapeHOL (.comb [ShapeHOL.one]) - 1) eids)
      (progToHOL (.decCall "y" .one "callee" [.var .local "x"] (.return (.var .local "y")) : Prog (RiscV.Word 64))) := by
  apply callSupported_scalarFunction_frontend ["x"]
  exact .call "y" "callee" [.var .local "x"] (by
    intro e h; simp only [List.mem_singleton] at h; subst e; exact .local "x" (by simp))
    (.base (.ret (.local "y" (by simp))))


/-- A comparison is accepted in an actual conditional and compiles to a
single Crep comparison expression. -/
theorem comparison_frontend_example (ctxt : PanToCrepContextExact 64) :
    FrontendScalar ctxt (.cmp .less (.const 0) (.const 1)) ∧
    compileExpExactHOLW ctxt (.cmp .less (.const 0) (.const 1) : ExpHOL 64) =
      ([.cmp .less (.const 0) (.const 1)],.one) := by
  constructor
  · exact .cmp .less (.const 0) (.const 1)
  · simp [compileExpExactHOLW]

/-- Global lowering leaves the supported scalar expressions unchanged. -/
theorem scalar_globals_fixed {scope : List VarName} {e : Exp (RiscV.Word 64)}
    (scalar : Scalar scope e) (globals : PanGlobalsContextExact 64) :
    compileExpExactHOL globals (expToHOL e) = expToHOL e := by
  induction scalar <;> simp_all [expToHOL,compileExpExactHOL,compileExpExactHOLList]

/-- Global lowering leaves every supported source body unchanged. -/
theorem supportedIn_globals_fixed {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) (globals : PanGlobalsContextExact 64) :
    compileProgExactHOL globals (progToHOL program) = progToHOL program := by
  induction supported <;> simp_all [progToHOL,compileProgExactHOL,shapeToHOL] <;>
    aesop (add safe scalar_globals_fixed)

theorem supported_globals_fixed {program : Prog (RiscV.Word 64)}
    (supported : CallFreeSupported program) (globals : PanGlobalsContextExact 64) :
    compileProgExactHOL globals (progToHOL program) = progToHOL program :=
  supportedIn_globals_fixed supported.1 globals

private theorem scalarList_globals_fixed {scope : List VarName} (args : List (Exp (RiscV.Word 64)))
    (supported : ∀ e ∈ args, Scalar scope e) (globals : PanGlobalsContextExact 64) :
    compileExpExactHOLList globals (args.map expToHOL) = args.map expToHOL := by
  induction args with
  | nil => simp [compileExpExactHOLList]
  | cons e rest ih =>
    have h : Scalar scope e := supported e (by simp)
    have restShape : ∀ e ∈ rest, Scalar scope e := by
      intro x hx; exact supported x (by simp [hx])
    simp [compileExpExactHOLList,scalar_globals_fixed h globals,ih restShape]

/-- Global lowering leaves every supported body, including calls, unchanged. -/
theorem callSupportedIn_globals_fixed {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : CallSupportedIn scope program) (globals : PanGlobalsContextExact 64) :
    compileProgExactHOL globals (progToHOL program) = progToHOL program := by
  induction supported with
  | base h => exact supportedIn_globals_fixed h globals
  | tail name args scalar => simp [progToHOL,compileProgExactHOL,scalarList_globals_fixed args scalar globals]
  | call dest name args scalar cont ih => simp [progToHOL,shapeToHOL,compileProgExactHOL,scalarList_globals_fixed args scalar globals,ih]
  | decl name scalar body ih => simp [progToHOL,shapeToHOL,compileProgExactHOL,scalar_globals_fixed scalar globals,ih]
  | seq a b iha ihb => simp [progToHOL,compileProgExactHOL,iha,ihb]
  | ite scalar a b iha ihb => simp [progToHOL,compileProgExactHOL,scalar_globals_fixed scalar globals,iha,ihb]
  | «while» scalar body ih => simp [progToHOL,compileProgExactHOL,scalar_globals_fixed scalar globals,ih]

/-- The phase-zero witnesses instantiate the generalized frontend shape. -/
theorem countdown_frontend_shape (n : Nat) (ctxt : PanToCrepContextExact 64) :
    FrontendProgram ctxt (countdownHOL n) := by
  rw [countdown_hol_eq]
  exact supported_frontend_shape (countdown_supported n) ctxt

theorem branching_frontend_shape (ctxt : PanToCrepContextExact 64) :
    FrontendProgram ctxt branchingHOL := by
  rw [branching_hol_eq]
  exact supported_frontend_shape branching_supported ctxt

end SteppedFlapjack.Concrete
