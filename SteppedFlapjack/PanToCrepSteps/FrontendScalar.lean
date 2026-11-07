import SteppedFlapjack.PanToCrepSteps.DeclShape

/-! General singleton-result frontend scalar expressions. -/
namespace SteppedFlapjack.PanToCrepSteps
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString

/-- A scalar expression the Pancake frontend compiles to one Crep expression.
The direct subset also supports the existing no-auxiliary-code Loop proofs;
comparisons may generate additional Loop code in a later pass. -/
inductive FrontendScalar {width : Nat} [NeZero width] (ctxt : PanToCrepContextExact width) : ExpHOL width → Prop
  | const (value) : FrontendScalar ctxt (.const value)
  | local (name reg) : ctxt.vars.lookup name = some (.one,[reg]) → FrontendScalar ctxt (.var .local name)
  | baseAddr : FrontendScalar ctxt .baseAddr
  | topAddr : FrontendScalar ctxt .topAddr
  | bytesInWord : FrontendScalar ctxt .bytesInWord
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

/-- Every frontend scalar produces exactly one Crep expression. -/
theorem frontendScalar_compile {width : Nat} [NeZero width] {ctxt : PanToCrepContextExact width} {e : ExpHOL width}
    (shape : FrontendScalar ctxt e) : ∃ value, compileExpExactHOLW ctxt e = ([value],.one) := by
  induction shape with
  | const v => exact ⟨.const v,by simp [compileExpExactHOLW]⟩
  | «local» name reg found => exact ⟨.var reg,by simp [compileExpExactHOLW,found]⟩
  | baseAddr => exact ⟨.baseAddr,by simp [compileExpExactHOLW]⟩
  | topAddr => exact ⟨.topAddr,by simp [compileExpExactHOLW]⟩
  | bytesInWord => exact ⟨.const (BitVec.ofNat width (width / 8)),by simp [compileExpExactHOLW]⟩
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

end SteppedFlapjack.PanToCrepSteps
