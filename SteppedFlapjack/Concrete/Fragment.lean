import SteppedFlapjack.PanToCrepSteps.CountedCountdown

/-! A syntactic, locally scoped scalar fragment for the first compiler pass. -/
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString

/-- Expressions in the supported scalar fragment; local reads must be in scope. -/
inductive Scalar (scope : List VarName) : Exp (RiscV.Word 64) → Prop
  | const (value) : Scalar scope (.const value)
  | local (name) : name ∈ scope → Scalar scope (.var .local name)
  | load {address} : Scalar scope address → Scalar scope (.load .one address)
  | op (operator) {a b} : Scalar scope a → Scalar scope b → Scalar scope (.op operator [a,b])
  | cmp (operator) {a b} : Scalar scope a → Scalar scope b → Scalar scope (.cmp operator a b)
  | shift (operator) {a b} : Scalar scope a → Scalar scope b → Scalar scope (.shift operator a b)

/-- Supported function bodies have scalar locals and expressions, including
nested conditionals and loops. Declarations bind only their own body. -/
inductive SupportedIn : List VarName → Prog (RiscV.Word 64) → Prop
  | skip {scope} : SupportedIn scope .skip
  | store {scope address value} : Scalar scope address → Scalar scope value → SupportedIn scope (.store address value)
  | assign {scope} (name) {e} : name ∈ scope → Scalar scope e → SupportedIn scope (.assign .local name e)
  | decl {scope} (name) {e body} : Scalar scope e → SupportedIn (name :: scope) body →
      SupportedIn scope (.dec name .one e body)
  | seq {scope a b} : SupportedIn scope a → SupportedIn scope b → SupportedIn scope (.seq a b)
  | ite {scope e a b} : Scalar scope e → SupportedIn scope a → SupportedIn scope b → SupportedIn scope (.ite e a b)
  | while {scope e body} : Scalar scope e → SupportedIn scope body → SupportedIn scope (.while e body)
  | ret {scope e} : Scalar scope e → SupportedIn scope (.return e)

/-- Scalar source programs with ordinary and tail calls. -/
inductive CallSupportedIn : List VarName → Prog (RiscV.Word 64) → Prop
  | base {scope program} : SupportedIn scope program → CallSupportedIn scope program
  | tail {scope} (name) (args) : (∀ e ∈ args, Scalar scope e) → CallSupportedIn scope (.call none name args)
  | call {scope} (dest name) (args) {cont} : (∀ e ∈ args, Scalar scope e) →
      CallSupportedIn (dest :: scope) cont → CallSupportedIn scope (.decCall dest .one name args cont)
  | decl {scope} (name) {e body} : Scalar scope e → CallSupportedIn (name :: scope) body →
      CallSupportedIn scope (.dec name .one e body)
  | seq {scope a b} : CallSupportedIn scope a → CallSupportedIn scope b → CallSupportedIn scope (.seq a b)
  | ite {scope e a b} : Scalar scope e → CallSupportedIn scope a → CallSupportedIn scope b → CallSupportedIn scope (.ite e a b)
  | while {scope e body} : Scalar scope e → CallSupportedIn scope body → CallSupportedIn scope (.while e body)

/-- A parameter-free body begins with no locals and its identifiers are
representable by HOL byte strings. -/
def CallFreeSupported (program : Prog (RiscV.Word 64)) : Prop :=
  SupportedIn [] program ∧ ProgByteRanged program

/-- Parameter-free call-aware source bodies with byte-representable identifiers. -/
def Supported (program : Prog (RiscV.Word 64)) : Prop :=
  CallSupportedIn [] program ∧ ProgByteRanged program

/-- The original call-free fragment is included in the call-aware fragment. -/
theorem CallFreeSupported.toSupported {program : Prog (RiscV.Word 64)}
    (supported : CallFreeSupported program) : Supported program :=
  ⟨.base supported.1, supported.2⟩

open SteppedFlapjack.PanToCrepSteps

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 10000 in
/-- Call-free evaluation does not inspect function tables or call contracts. -/
theorem supported_calls_irrel {σ : Type} (context : PanValueFfiContext (RiscV.Word 64))
    (primitive : PanPrimitiveHandler (RiscV.Word 64)) (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (structs : StructContext) (functions otherFunctions : List (FunName × List VarName × Prog (RiscV.Word 64)))
    (base top bytes : RiscV.Word 64) (fuel : Nat)
    (access : Option (PanValueMemoryAccess (RiscV.Word 64))) (contracts : Option PanValueCallContracts) :
    ∀ (scope : List VarName) (p : Prog (RiscV.Word 64)), SupportedIn scope p →
      ∀ locals globals memory ffi,
      evalPanValueFfiProgSteps context primitive handler structs functions base top bytes fuel locals globals memory ffi p
        (memoryAccess := access) (contracts := contracts) =
      evalPanValueFfiProgSteps context primitive handler structs otherFunctions base top bytes fuel locals globals memory ffi p
        (memoryAccess := access) := by
  induction fuel with
  | zero => intros; simp [evalPanValueFfiProgSteps]
  | succ fuel ih =>
    intro scope p shape locals globals memory ffi
    cases shape with
    | skip => simp [evalPanValueFfiProgSteps]
    | store address value => simp [evalPanValueFfiProgSteps]
    | assign name member scalar => simp [evalPanValueFfiProgSteps]
    | decl name scalar body =>
      simp only [evalPanValueFfiProgSteps, ih _ _ body]
    | seq a b =>
      simp only [evalPanValueFfiProgSteps, ih _ _ a, ih _ _ b]
    | ite scalar a b =>
      simp only [evalPanValueFfiProgSteps, ih _ _ a, ih _ _ b]
    | «while» scalar body =>
      simp only [evalPanValueFfiProgSteps, ih _ _ body, ih _ _ (SupportedIn.while scalar body)]
    | ret scalar => simp [evalPanValueFfiProgSteps]

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
    (supported : CallFreeSupported program) (a b : MlString) :
    fpermHOL a b (progToHOL program) = progToHOL program :=
  supportedIn_fperm supported.1 a b

/-- The prefixed source body used by the existing countdown correspondence. -/
def countdown (n : Nat) : Prog (RiscV.Word 64) :=
  .dec "x" .one (.const (BitVec.ofNat 64 n))
    (.seq .skip (.seq (.while (.var .local "x") (PanToCrepSteps.countdownBody "x")) (.return (.const 0))))

/-- The natural countdown, without the compiler-oriented skip prefix. -/
def naturalCountdown (n : Nat) : Prog (RiscV.Word 64) :=
  .dec "x" .one (.const (BitVec.ofNat 64 n))
    (.seq (.while (.var .local "x") (PanToCrepSteps.countdownBody "x")) (.return (.const 0)))

def naturalCountdownHOL (n : Nat) : ProgHOL 64 := progToHOL (naturalCountdown n)

/-- A parameter-free comparison whose conditional takes the first branch. -/
def branching : Prog (RiscV.Word 64) :=
  .ite (.cmp .lower (.const 0) (.const 1)) (.return (.const 7)) (.return (.const 9))

theorem countdown_supported (n : Nat) : CallFreeSupported (countdown n) := by
  constructor
  · exact .decl "x" (.const _) (.seq .skip (.seq
    (.while (.local "x" (by simp)) (.assign "x" (by simp)
      (.op .sub (.local "x" (by simp)) (.const _)))) (.ret (.const _))))
  · simp [countdown,PanToCrepSteps.countdownBody,ProgByteRanged,ExpByteRanged,ListExpByteRanged,ShapeByteRanged,NameRanged]

theorem naturalCountdown_supported (n : Nat) : CallFreeSupported (naturalCountdown n) := by
  constructor
  · exact .decl "x" (.const _) (.seq
      (.while (.local "x" (by simp)) (.assign "x" (by simp)
        (.op .sub (.local "x" (by simp)) (.const _)))) (.ret (.const _)))
  · simp [naturalCountdown,PanToCrepSteps.countdownBody,ProgByteRanged,ExpByteRanged,
      ListExpByteRanged,ShapeByteRanged,NameRanged]

theorem branching_supported : CallFreeSupported branching := by
  constructor
  · exact .ite (.cmp .lower (.const _) (.const _)) (.ret (.const _)) (.ret (.const _))
  · simp [branching,ProgByteRanged,ExpByteRanged]

end SteppedFlapjack.Concrete
