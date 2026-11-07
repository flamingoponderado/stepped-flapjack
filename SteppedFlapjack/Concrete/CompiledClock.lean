import SteppedFlapjack.Concrete.ControlClock
namespace SteppedFlapjack.Concrete
open Flapjack Flapjack.Pancake.PanLang SteppedFlapjack.PanToCrepSteps

def holWeight {width : Nat} [NeZero width] : ProgHOL width → Nat
  | .dec _ _ _ body => 1 + holWeight body
  | .seq a b => 1 + holWeight a + holWeight b
  | .ite _ a b => 1 + holWeight a + holWeight b
  | .while _ body => 1 + holWeight body
  | _ => 1

private theorem crepSizePos {width : Nat} [NeZero width] (p : CrepProgHOL width) : 1 ≤ sizeOf p := by
  cases p <;> simp_wf <;> omega

private theorem frontend_weight {width : Nat} [NeZero width] {context : PanToCrepContextExact width} {p : ProgHOL width}
    (shape : FrontendProgram context p) : holWeight p ≤ sizeOf (compileProgExactHOLW context p) := by
  induction shape with
  | skip | «break» | «continue» | tick | store | assign | ret =>
    simpa [holWeight] using crepSizePos (compileProgExactHOLW _ _)
  | @decl ctxt name e body he hb ih =>
    obtain ⟨value,compiled⟩ := frontendDecl_compile ctxt name e body he
    rw [compiled]
    simp only [holWeight]
    simp_wf
    omega
  | @seq ctxt a b ha hb iha ihb =>
    simp only [holWeight,compileProgExactHOLW]
    simp_wf
    omega
  | @ite ctxt e a b he ha hb iha ihb =>
    obtain ⟨value,compiled⟩ := frontendScalar_compile he
    simp only [holWeight,compileProgExactHOLW,compileIfExactHOLW,compiled]
    simp_wf
    omega
  | @«while» ctxt e body he hb ih =>
    obtain ⟨value,compiled⟩ := frontendScalar_compile he
    simp only [holWeight,compileProgExactHOLW,compileWhileExactHOLW,compiled]
    simp_wf
    omega
private theorem weightsAgree {scope : List VarName} {program : Prog (RiscV.Word 64)}
    (supported : SupportedIn scope program) : programWeight program = holWeight (progToHOL program) := by
  induction supported <;> simp_all [programWeight,holWeight,progToHOL,shapeToHOL]

/-- Generated Crep code size dominates the source's statement weight. -/
theorem supported_weight_le_compiled {program : Prog (RiscV.Word 64)} (supported : Supported program)
    (context : PanToCrepContextExact 64) : programWeight program ≤ sizeOf (compileProgExactHOLW context (progToHOL program)) := by
  rw [weightsAgree supported.1]
  exact frontend_weight (supported_frontend_shape supported context)

/-- A supported run uses at most the generated code size times its initial
clock plus one source control visits. -/
theorem supported_control_compiled_clock {σ : Type} {program : Prog (RiscV.Word 64)}
    (supported : Supported program) (context : PanToCrepContextExact 64)
    (source sourceFinal : PanSemStateFiniteExact 64 σ) (result : Option (PanSemResultExact 64))
    (run : source.evaluateHOLFiniteState (progToHOL program) = (result,sourceFinal)) (nonerror : result ≠ some .error) :
    controlSteps (progToHOL program) source ≤
      sizeOf (compileProgExactHOLW context (progToHOL program)) * (source.clock+1) := by
  have cost := supported_control_clock supported source sourceFinal result run nonerror
  have weight := supported_weight_le_compiled supported context
  have clock : source.clock - sourceFinal.clock + 1 ≤ source.clock+1 := by omega
  exact cost.trans ((Nat.mul_le_mul weight clock))

end SteppedFlapjack.Concrete
