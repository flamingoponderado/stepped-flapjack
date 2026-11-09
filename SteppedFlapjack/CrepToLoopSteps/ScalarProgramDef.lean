import SteppedFlapjack.CrepToLoopSteps.ScalarPrefix

namespace SteppedFlapjack.CrepToLoopSteps
open Flapjack

/-- Crep programs produced by the phase-one frontend, including nested loops. -/
inductive ScalarProgram {width : Nat} [NeZero width] : CrepProgHOL width → Prop
  | skip : ScalarProgram .skip
  | break (n) : ScalarProgram (.break n)
  | continue (n) : ScalarProgram (.continue n)
  | tick : ScalarProgram .tick
  | ret {e} : CompiledScalar e → ScalarProgram (.return [e])
  | assign (n) {e} : CompiledScalar e → ScalarProgram (.assign n e)
  | store {a b} : CompiledScalar a → CompiledScalar b → ScalarProgram (.store a b)
  | dec (n) {e body} : CompiledScalar e → ScalarProgram body → ScalarProgram (.dec n e body)
  | seq {a b} : ScalarProgram a → ScalarProgram b → ScalarProgram (.seq a b)
  | ite {e a b} : CompiledScalar e → ScalarProgram a → ScalarProgram b → ScalarProgram (.ite e a b)
  | while {e body} : CompiledScalar e → ScalarProgram body → ScalarProgram (.while e body)


end SteppedFlapjack.CrepToLoopSteps
