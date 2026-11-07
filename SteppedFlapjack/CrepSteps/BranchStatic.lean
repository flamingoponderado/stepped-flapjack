import SteppedFlapjack.CrepSteps.BranchClock

/-! Static evaluator visit bounds for loop-free Crep branches. -/
namespace SteppedFlapjack.CrepSteps
open Flapjack SteppedFlapjack.CrepToLoopSteps

/-- A Crep program without calls or loops. Expressions are unrestricted:
the Crep visit measure treats their evaluation as atomic. -/
inductive StaticProgram {width : Nat} [NeZero width] : CrepProgHOL width → Prop
  | leaf (p : CrepProgHOL width) : (match p with | .dec _ _ _ | .seq _ _ | .ite _ _ _ | .while _ _ | .call _ _ _ => false | _ => true) → StaticProgram p
  | dec (name : Nat) (value : CrepExpHOL width) {body} : StaticProgram body → StaticProgram (.dec name value body)
  | seq {a b} : StaticProgram a → StaticProgram b → StaticProgram (.seq a b)
  | ite (condition : CrepExpHOL width) {a b} : StaticProgram a → StaticProgram b → StaticProgram (.ite condition a b)

/-- A loop-free Crep run visits no more statements than its syntax size,
independently of the complexity of its expressions. -/
theorem staticProgram_steps {width : Nat} [NeZero width] {σ : Type}
    {p : CrepProgHOL width} (shape : StaticProgram p) (source : CrepSemHOLState width σ) :
    steps p source ≤ sizeOf p := by
  induction shape generalizing source with
  | leaf p leaf =>
    rw [steps_leaf p source leaf]
    cases p <;> simp_all <;> omega
  | @dec name value body hb ih =>
    rw [steps_dec]
    rcases evalCrepSemHOLExp source value with _ | v
    · simp_wf; omega
    · have bound := ih (CrepSemHOLState.setVar name v source)
      simp_wf; omega
  | @seq a b ha hb iha ihb =>
    rw [steps_seq]
    have first := iha source
    rcases evalCrepSemHOLProgExact source a with ⟨out,post⟩
    cases out with
    | none => have second := ihb post; simp_wf; omega
    | some r => simp_wf; omega
  | @ite e a b ha hb iha ihb =>
    rw [steps_ite]
    have first := iha source
    have second := ihb source
    rcases evalCrepSemHOLExp source e with _ | ⟨v⟩
    · simp_wf; omega
    · cases v with
      | word w => simp_wf; split <;> omega

/-- Every direct-expression program is loop-free. -/
theorem exprProgram_staticShape {width : Nat} [NeZero width]
    {p : CrepProgHOL width} (shape : ExprProgram p) : StaticProgram p := by
  induction shape with
  | leaf leaf => cases leaf <;> exact .leaf _ rfl
  | returnNil => exact .leaf _ rfl
  | returnOne e => exact .leaf _ rfl
  | assign name e => exact .leaf _ rfl
  | storeGlob name e => exact .leaf _ rfl
  | store a b => exact .leaf _ rfl
  | seq a b iha ihb => exact .seq iha ihb

/-- Every existing branch shape is loop-free, including its declarations. -/
theorem branchProgram_staticShape {width : Nat} [NeZero width]
    {p : CrepProgHOL width} (shape : BranchProgram p) : StaticProgram p := by
  induction shape with
  | expr shape => exact exprProgram_staticShape shape
  | dec value body ih => exact .dec _ _ ih
  | seq a b iha ihb => exact .seq iha ihb
  | ite condition a b iha ihb => exact .ite _ iha ihb

/-- An expression-program execution visits no more nodes than its syntax size. -/
theorem exprProgram_static {width : Nat} [NeZero width] {σ : Type}
    {p : CrepProgHOL width} (shape : ExprProgram p) (source : CrepSemHOLState width σ) :
    steps p source ≤ sizeOf p :=
  staticProgram_steps (exprProgram_staticShape shape) source

/-- A loop-free direct-expression branch visits no more nodes than its syntax size. -/
theorem branchProgram_static {width : Nat} [NeZero width] {σ : Type}
    {p : CrepProgHOL width} (shape : BranchProgram p) (source : CrepSemHOLState width σ) :
    steps p source ≤ sizeOf p :=
  staticProgram_steps (branchProgram_staticShape shape) source

end SteppedFlapjack.CrepSteps
