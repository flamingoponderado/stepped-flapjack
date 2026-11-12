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

theorem selectScalarShapeLoad {width : Nat} [NeZero width] (index : Nat) (shapes : List ShapeHOL)
    (address : BitVec width) (value : CrepExpHOL width) (h : shapes[index]? = some .one) :
    ∃ offset, compFieldHOL index shapes (loadShapeBytesHOLW address (sizeOfShapesHOL shapes) value) =
      ([if offset == 0 then .load value else .load (.op .add [value,.const offset])], .one) := by
  induction shapes generalizing index address with
  | nil => simp at h
  | cons shape shapes ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst shape
      refine ⟨address, ?_⟩
      simp [compFieldHOL,sizeOfShapesHOL,sizeOfShapeHOL,Nat.one_add,loadShapeBytesHOLW]
    | succ index =>
      simp only [List.getElem?_cons_succ] at h
      obtain ⟨next, drop⟩ := dropShapeLoads (sizeOfShapeHOL shape) (sizeOfShapesHOL shapes) address value
      obtain ⟨offset, eq⟩ := ih index next h
      refine ⟨offset, ?_⟩
      simpa [compFieldHOL,sizeOfShapesHOL,drop] using eq

theorem scalarShapeField_compiles {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width)
    (index : Nat) (shapes : List ShapeHOL) (address : ExpHOL width) (compiled : CrepExpHOL width)
    (ha : compileExpExactHOLW ctxt address = ([compiled],.one)) (hi : shapes[index]? = some .one) :
    ∃ offset, compileExpExactHOLW ctxt (.rfield index (.load (.comb shapes) address)) =
      ([if offset == 0 then .load compiled else .load (.op .add [compiled,.const offset])], .one) := by
  obtain ⟨offset, h⟩ := selectScalarShapeLoad index shapes 0 compiled hi
  exact ⟨offset, by simpa [compileExpExactHOLW, ha, sizeOfShapeHOL] using h⟩

/-- A scalar expression the Pancake frontend compiles to one Crep expression.
The direct subset also supports the existing no-auxiliary-code Loop proofs;
comparisons may generate additional Loop code in a later pass. -/
inductive FrontendScalar {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width) : ExpHOL width → Prop
  | const (value) : FrontendScalar ctxt (.const value)
  | local (name reg) : ctxt.vars.lookup name = some (.one,[reg]) → FrontendScalar ctxt (.var .local name)
  | baseAddr : FrontendScalar ctxt .baseAddr
  | topAddr : FrontendScalar ctxt .topAddr
  | bytesInWord : FrontendScalar ctxt .bytesInWord
  | fieldLoad (index : Nat) (shapes : List ShapeHOL) (inBounds : shapes[index]? = some .one) {address} :
      FrontendScalar ctxt address →
      FrontendScalar ctxt (.rfield index (.load (.comb shapes) address))
  | load {address} : FrontendScalar ctxt address → FrontendScalar ctxt (.load .one address)
  | op (operator) {a b} : FrontendScalar ctxt a → FrontendScalar ctxt b → FrontendScalar ctxt (.op operator [a,b])
  | cmp (operator) {a b} : FrontendScalar ctxt a → FrontendScalar ctxt b → FrontendScalar ctxt (.cmp operator a b)
  | shift (operator) {a b} : FrontendScalar ctxt a → FrontendScalar ctxt b → FrontendScalar ctxt (.shift operator a b)

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

/-- Supported scalar arguments satisfy the compiler localization check. -/
theorem frontendScalar_everyLocal {width : Nat} [NeZero width] {ctxt : PanToCrepContextExact width}
    {e : ExpHOL width} (shape : FrontendScalar ctxt e) : everyExpHOL localisedExpHOL e = true := by
  induction shape <;> simp_all [localisedExpHOL,everyExpHOL,everyExpListHOL]
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
  | fieldLoad index shapes inBounds address ih =>
    obtain ⟨compiled, hc⟩ := ih
    obtain ⟨offset, eq⟩ := scalarShapeField_compiles ctxt index shapes _ compiled hc inBounds
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

end SteppedFlapjack.PanToCrepSteps
