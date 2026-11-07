import SteppedFlapjack.PanToCrepSteps.CountedCountdown

/-! A syntactic, locally scoped scalar fragment for the first compiler pass. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString

/-- Expressions in the supported scalar fragment; local reads must be in scope. -/
inductive Scalar (scope : List VarName) : Exp (RiscV.Word 64) → Prop
  | const (value) : Scalar scope (.const value)
  | local (name) : name ∈ scope → Scalar scope (.var .local name)
  | op (operator) {a b} : Scalar scope a → Scalar scope b → Scalar scope (.op operator [a,b])
  | cmp (operator) {a b} : Scalar scope a → Scalar scope b → Scalar scope (.cmp operator a b)
  | shift (operator) {a b} : Scalar scope a → Scalar scope b → Scalar scope (.shift operator a b)

/-- Supported function bodies have scalar locals and expressions, including
nested conditionals and loops. Declarations bind only their own body. -/
inductive SupportedIn : List VarName → Prog (RiscV.Word 64) → Prop
  | skip {scope} : SupportedIn scope .skip
  | assign {scope} (name) {e} : name ∈ scope → Scalar scope e → SupportedIn scope (.assign .local name e)
  | decl {scope} (name) {e body} : Scalar scope e → SupportedIn (name :: scope) body →
      SupportedIn scope (.dec name .one e body)
  | seq {scope a b} : SupportedIn scope a → SupportedIn scope b → SupportedIn scope (.seq a b)
  | ite {scope e a b} : Scalar scope e → SupportedIn scope a → SupportedIn scope b → SupportedIn scope (.ite e a b)
  | while {scope e body} : Scalar scope e → SupportedIn scope body → SupportedIn scope (.while e body)
  | ret {scope e} : Scalar scope e → SupportedIn scope (.return e)

/-- A parameter-free body begins with no locals and its identifiers are
representable by HOL byte strings. -/
def Supported (program : Prog (RiscV.Word 64)) : Prop :=
  SupportedIn [] program ∧ ProgByteRanged program

/-- Distinct Lean names can collapse to the same HOL byte string, so the
representability condition above is necessary for an unrestricted bridge. -/
theorem names_outside_byte_range_can_collide :
    ∃ a b : String, a ≠ b ∧ ofString a = ofString b := by
  refine ⟨String.singleton (Char.ofNat 0), String.singleton (Char.ofNat 256), ?_, ?_⟩ <;> decide

/-- Function renaming leaves this call-free source fragment unchanged. -/
theorem supportedIn_fperm {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) (a b : MlString) :
    fpermHOL a b (progToHOL program) = progToHOL program := by
  induction supported <;> simp_all [progToHOL,fpermHOL]

theorem supported_fperm {program : Prog (RiscV.Word 64)}
    (supported : Supported program) (a b : MlString) :
    fpermHOL a b (progToHOL program) = progToHOL program :=
  supportedIn_fperm supported.1 a b

/-- The prefixed source body used by the existing countdown correspondence. -/
def countdown (n : Nat) : Prog (RiscV.Word 64) :=
  .dec "x" .one (.const (BitVec.ofNat 64 n))
    (.seq .skip (.seq (.while (.var .local "x") (PanToCrepSteps.countdownBody "x")) (.return (.const 0))))

/-- A parameter-free comparison whose conditional takes the first branch. -/
def branching : Prog (RiscV.Word 64) :=
  .ite (.cmp .lower (.const 0) (.const 1)) (.return (.const 7)) (.return (.const 9))

theorem countdown_supported (n : Nat) : Supported (countdown n) := by
  constructor
  · exact .decl "x" (.const _) (.seq .skip (.seq
    (.while (.local "x" (by simp)) (.assign "x" (by simp)
      (.op .sub (.local "x" (by simp)) (.const _)))) (.ret (.const _))))
  · simp [countdown,PanToCrepSteps.countdownBody,ProgByteRanged,ExpByteRanged,ListExpByteRanged,ShapeByteRanged,NameRanged]

theorem branching_supported : Supported branching := by
  constructor
  · exact .ite (.cmp .lower (.const _) (.const _)) (.ret (.const _)) (.ret (.const _))
  · simp [branching,ProgByteRanged,ExpByteRanged]

end SteppedFlapjack.Concrete
