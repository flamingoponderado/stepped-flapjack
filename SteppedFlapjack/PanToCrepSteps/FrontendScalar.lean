import SteppedFlapjack.PanToCrepSteps.DeclShape

/-! General singleton-result frontend scalar expressions. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString

theorem dropShapeLoads {width : Nat} [NeZero width] (n count : Nat)
    (address : BitVec width) (value : CrepExpHOL width) :
    ∃ next, (loadShapeBytesHOLW address (n+count) value).drop n = loadShapeBytesHOLW next count value := by
  induction n generalizing address with
  | zero => exact ⟨address, by simp⟩
  | succ n ih =>
    obtain ⟨next, eq⟩ := ih (address + BitVec.ofNat width (width / 8))
    exact ⟨next, by simpa [loadShapeBytesHOLW, Nat.succ_add] using eq⟩

theorem takeShapeLoads {width : Nat} [NeZero width] (n count : Nat)
    (address : BitVec width) (value : CrepExpHOL width) :
    (loadShapeBytesHOLW address (n+count) value).take n = loadShapeBytesHOLW address n value := by
  induction n generalizing address with
  | zero => simp [loadShapeBytesHOLW]
  | succ n ih =>
    simpa [loadShapeBytesHOLW, Nat.succ_add] using congrArg (List.cons (if address == 0 then .load value else .load (.op .add [value,.const address]))) (ih (address + BitVec.ofNat width (width / 8)))

theorem selectShapeLoad {width : Nat} [NeZero width] (index : Nat) (shapes : List ShapeHOL) (shape : ShapeHOL)
    (address : BitVec width) (value : CrepExpHOL width) (h : shapes[index]? = some shape) :
    ∃ offset, compFieldHOL index shapes (loadShapeBytesHOLW address (sizeOfShapesHOL shapes) value) =
      (loadShapeBytesHOLW offset (sizeOfShapeHOL shape) value, shape) := by
  induction shapes generalizing index address with
  | nil => simp at h
  | cons head shapes ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst head
      exact ⟨address, by simp [compFieldHOL,sizeOfShapesHOL,takeShapeLoads]⟩
    | succ index =>
      simp only [List.getElem?_cons_succ] at h
      obtain ⟨next, drop⟩ := dropShapeLoads (sizeOfShapeHOL head) (sizeOfShapesHOL shapes) address value
      obtain ⟨offset, eq⟩ := ih index next h
      exact ⟨offset, by simpa [compFieldHOL,sizeOfShapesHOL,drop] using eq⟩
inductive FieldPath {width : Nat} [NeZero width] (root : ExpHOL width) (rootShape : ShapeHOL) : ExpHOL width → ShapeHOL → Prop
  | root : FieldPath root rootShape root rootShape
  | field {e shapes} (path : FieldPath root rootShape e (.comb shapes)) (index : Nat) (shape : ShapeHOL)
      (found : shapes[index]? = some shape) : FieldPath root rootShape (.rfield index e) shape

theorem fieldPath_compiles {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width)
    {root e : ExpHOL width} {rootShape shape : ShapeHOL} (path : FieldPath root rootShape e shape)
    (value : CrepExpHOL width) (address : BitVec width)
    (compiled : compileExpExactHOLW ctxt root = (loadShapeBytesHOLW address (sizeOfShapeHOL rootShape) value,rootShape)) :
    ∃ offset, compileExpExactHOLW ctxt e = (loadShapeBytesHOLW offset (sizeOfShapeHOL shape) value,shape) := by
  induction path with
  | root => exact ⟨address,compiled⟩
  | field path index shape found ih =>
    obtain ⟨offset, compiled⟩ := ih
    obtain ⟨next, selected⟩ := selectShapeLoad index _ shape offset value found
    refine ⟨next, ?_⟩
    simpa [compileExpExactHOLW,compiled,sizeOfShapeHOL] using selected


theorem scalarPathField_compiles {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width)
    (shapes : List ShapeHOL) (address e : ExpHOL width) (compiled : CrepExpHOL width)
    (ha : compileExpExactHOLW ctxt address = ([compiled],.one))
    (path : FieldPath (.load (.comb shapes) address) (.comb shapes) e .one) :
    ∃ offset, compileExpExactHOLW ctxt e =
      ([if offset == 0 then .load compiled else .load (.op .add [compiled,.const offset])], .one) := by
  have root : compileExpExactHOLW ctxt (.load (.comb shapes) address) =
      (loadShapeBytesHOLW 0 (sizeOfShapeHOL (.comb shapes)) compiled,.comb shapes) := by
    simp [compileExpExactHOLW,ha,sizeOfShapeHOL]
  obtain ⟨offset, h⟩ := fieldPath_compiles ctxt path compiled 0 root
  exact ⟨offset, by simpa [sizeOfShapeHOL,loadShapeBytesHOLW] using h⟩

theorem FieldPath.localised {width : Nat} [NeZero width] {root e : ExpHOL width}
    {rootShape shape : ShapeHOL} (path : FieldPath root rootShape e shape)
    (h : localisedExpHOL root = true) : localisedExpHOL e = true := by
  induction path with
  | root => exact h
  | field path index shape found ih => simpa [localisedExpHOL,everyExpHOL] using ih

theorem FieldPath.everyLocal {width : Nat} [NeZero width] {root e : ExpHOL width}
    {rootShape shape : ShapeHOL} (path : FieldPath root rootShape e shape)
    (h : everyExpHOL localisedExpHOL root = true) (hlocal : localisedExpHOL root = true) :
    everyExpHOL localisedExpHOL e = true := by
  induction path with
  | root => exact h
  | field path index shape found ih =>
    have loc := path.localised hlocal
    simpa [everyExpHOL,localisedExpHOL] using And.intro loc ih

/-- A scalar expression the Pancake frontend compiles to one Crep expression.
The direct subset also supports the existing no-auxiliary-code Loop proofs;
comparisons may generate additional Loop code in a later pass. -/
inductive FrontendScalar {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width) : ExpHOL width → Prop
  | const (value) : FrontendScalar ctxt (.const value)
  | local (name reg) : ctxt.vars.lookup name = some (.one,[reg]) → FrontendScalar ctxt (.var .local name)
  | baseAddr : FrontendScalar ctxt .baseAddr
  | topAddr : FrontendScalar ctxt .topAddr
  | bytesInWord : FrontendScalar ctxt .bytesInWord
  | fieldPath (shapes : List ShapeHOL) {address e} :
      FrontendScalar ctxt address →
      FieldPath (.load (.comb shapes) address) (.comb shapes) e .one → FrontendScalar ctxt e
  | load {address} : FrontendScalar ctxt address → FrontendScalar ctxt (.load .one address)
  | op (operator) {a b} : FrontendScalar ctxt a → FrontendScalar ctxt b → FrontendScalar ctxt (.op operator [a,b])
  | cmp (operator) {a b} : FrontendScalar ctxt a → FrontendScalar ctxt b → FrontendScalar ctxt (.cmp operator a b)
  | shift (operator) {a b} : FrontendScalar ctxt a → FrontendScalar ctxt b → FrontendScalar ctxt (.shift operator a b)

theorem FrontendScalar.fieldLoad {width : Nat} [NeZero width] {ctxt : PanToCrepContextExact width}
    (index : Nat) (shapes : List ShapeHOL) (found : shapes[index]? = some .one) {address}
    (h : FrontendScalar ctxt address) :
    FrontendScalar ctxt (.rfield index (.load (.comb shapes) address)) :=
  .fieldPath shapes h (.field .root index .one found)

/-- The existing direct-expression fragment embeds into the full scalar grammar. -/
theorem frontendScalar_of_direct {width : Nat} [NeZero width] {ctxt : PanToCrepContextExact width} {e : ExpHOL width}
    (shape : ScalarExpression ctxt e) : FrontendScalar ctxt e := by
  induction shape with
  | const v => exact .const v
  | «local» name reg found => exact .local name reg found
  | baseAddr => exact .baseAddr
  | topAddr => exact .topAddr
  | bytesInWord => exact .bytesInWord
  | op op a b iha ihb => exact .op op iha ihb
  | shift op a b iha ihb => exact .shift op iha ihb

/-- General frontend scalars do not refer to global variables. -/
theorem frontendScalar_localised {width : Nat} [NeZero width] {ctxt : PanToCrepContextExact width}
    {e : ExpHOL width} (shape : FrontendScalar ctxt e) : localisedExpHOL e = true := by
  induction shape <;> simp_all [localisedExpHOL,everyExpHOL,everyExpListHOL]
  case fieldPath shapes address path ih =>
    apply path.localised
    simpa [localisedExpHOL,everyExpHOL] using ih

/-- Supported scalar arguments satisfy the compiler localization check. -/
theorem frontendScalar_everyLocal {width : Nat} [NeZero width] {ctxt : PanToCrepContextExact width}
    {e : ExpHOL width} (shape : FrontendScalar ctxt e) : everyExpHOL localisedExpHOL e = true := by
  induction shape <;> simp_all [localisedExpHOL,everyExpHOL,everyExpListHOL]
  case fieldPath shapes address path ih =>
    apply path.everyLocal
    · simpa [everyExpHOL,localisedExpHOL] using And.intro (frontendScalar_localised address) ih
    · simpa [everyExpHOL,localisedExpHOL] using frontendScalar_localised address
  all_goals first
    | exact frontendScalar_localised (by assumption)
    | constructor <;> (simpa [localisedExpHOL] using frontendScalar_localised (by assumption))

theorem frontendArguments_localised {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width)
    (args : List (ExpHOL width)) (shape : ∀ e ∈ args, FrontendScalar ctxt e) :
    everyExpListHOL localisedExpHOL args = true := by
  induction args with
  | nil => rfl
  | cons e es ih =>
    simp only [everyExpListHOL,Bool.and_eq_true]
    exact ⟨frontendScalar_everyLocal (shape e (by simp)),ih (fun x hx => shape x (by simp [hx]))⟩

/-- Every frontend scalar produces exactly one Crep expression. -/
theorem frontendScalar_compile {width : Nat} [NeZero width] {ctxt : PanToCrepContextExact width} {e : ExpHOL width}
    (shape : FrontendScalar ctxt e) : ∃ value, compileExpExactHOLW ctxt e = ([value],.one) := by
  induction shape with
  | const v => exact ⟨.const v,by simp [compileExpExactHOLW]⟩
  | «local» name reg found => exact ⟨.var reg,by simp [compileExpExactHOLW,found]⟩
  | baseAddr => exact ⟨.baseAddr,by simp [compileExpExactHOLW]⟩
  | topAddr => exact ⟨.topAddr,by simp [compileExpExactHOLW]⟩
  | bytesInWord => exact ⟨.const (BitVec.ofNat width (width / 8)),by simp [compileExpExactHOLW]⟩
  | fieldPath shapes address path ih =>
    obtain ⟨compiled, hc⟩ := ih
    obtain ⟨offset, eq⟩ := scalarPathField_compiles ctxt shapes _ _ compiled hc path
    exact ⟨_, eq⟩
  | load address ih =>
    obtain ⟨compiled, hc⟩ := ih
    exact ⟨.load compiled, by simp [compileExpExactHOLW, hc, sizeOfShapeHOL, loadShapeBytesHOLW]⟩
  | op op ha hb iha ihb =>
    obtain ⟨a,ca⟩ := iha
    obtain ⟨b,cb⟩ := ihb
    exact ⟨.op op [a,b],by simp [compileExpExactHOLW,compileExpExactHOLWList,ca,cb,cexpHeads]⟩
  | cmp op ha hb iha ihb =>
    obtain ⟨a,ca⟩ := iha
    obtain ⟨b,cb⟩ := ihb
    exact ⟨.cmp op a b,by simp [compileExpExactHOLW,ca,cb]⟩
  | shift op ha hb iha ihb =>
    obtain ⟨a,ca⟩ := iha
    obtain ⟨b,cb⟩ := ihb
    exact ⟨.shift op a b,by simp [compileExpExactHOLW,ca,cb]⟩

/-- Generalized scalar declarations compile with the actual extended context,
including when the initializer contains comparisons. -/
theorem frontendDecl_compile {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width) (name : MlString)
    (initializer : ExpHOL width) (body : ProgHOL width) (shape : FrontendScalar ctxt initializer) :
    ∃ value, compileProgExactHOLW ctxt (.dec name .one initializer body) =
      .dec (ctxt.vmax+1) value (compileProgExactHOLW (scalarDeclContext ctxt name) body) := by
  obtain ⟨value,compiled⟩ := frontendScalar_compile shape
  refine ⟨value,?_⟩
  simp [compileProgExactHOLW,compileDecExactHOLW,compiled,nestedDecsHOL,scalarDeclContext]

/-- Generalized scalar conditions are passed to the generated Crep conditional. -/
theorem frontendIf_compile {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width)
    (condition : ExpHOL width) (yes no : ProgHOL width) (shape : FrontendScalar ctxt condition) :
    ∃ value, compileProgExactHOLW ctxt (.ite condition yes no) =
      .ite value (compileProgExactHOLW ctxt yes) (compileProgExactHOLW ctxt no) := by
  obtain ⟨value,compiled⟩ := frontendScalar_compile shape
  exact ⟨value,by simp [compileProgExactHOLW,compileIfExactHOLW,compiled]⟩

/-- Generalized scalar conditions are passed to the generated Crep loop. -/
theorem frontendWhile_compile {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width)
    (condition : ExpHOL width) (body : ProgHOL width) (shape : FrontendScalar ctxt condition) :
    ∃ value, compileProgExactHOLW ctxt (.while condition body) =
      .while value (compileProgExactHOLW ctxt body) := by
  obtain ⟨value,compiled⟩ := frontendScalar_compile shape
  exact ⟨value,by simp [compileProgExactHOLW,compileWhileExactHOLW,compiled]⟩

/-- The scalar after a two-word nested field is supported and loads at byte offset 16. -/
example (ctxt : PanToCrepContextExact 64) :
    FrontendScalar ctxt (.rfield 1 (.load (.comb [.comb [.one,.one],.one]) .topAddr)) := by
  exact .fieldLoad 1 [.comb [.one,.one],.one] rfl .topAddr
example (ctxt : PanToCrepContextExact 64) :
    compileExpExactHOLW ctxt (.rfield 1 (.load (.comb [.comb [.one,.one],.one]) (.topAddr : ExpHOL 64))) =
      ([.load (.op .add [.topAddr,.const 16])],.one) := by
  simp [compileExpExactHOLW,compFieldHOL,sizeOfShapeHOL,sizeOfShapesHOL,loadShapeBytesHOLW]

/-- A two-level field path selects the second word of a nested value. -/
example (ctxt : PanToCrepContextExact 64) :
    FrontendScalar ctxt (.rfield 1 (.rfield 0 (.load (.comb [.comb [.one,.one],.one]) .topAddr))) := by
  exact .fieldPath [.comb [.one,.one],.one] .topAddr (.field (.field .root 0 (.comb [.one,.one]) rfl) 1 .one rfl)
example (ctxt : PanToCrepContextExact 64) :
    compileExpExactHOLW ctxt (.rfield 1 (.rfield 0 (.load (.comb [.comb [.one,.one],.one]) (.topAddr : ExpHOL 64)))) =
      ([.load (.op .add [.topAddr,.const 8])],.one) := by
  simp [compileExpExactHOLW,compFieldHOL,sizeOfShapeHOL,sizeOfShapesHOL,loadShapeBytesHOLW]

end SteppedFlapjack.PanToCrepSteps
