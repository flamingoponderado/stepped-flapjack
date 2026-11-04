import SteppedFlapjack

/-! Axiom audit: fails the build if any declaration in a `SteppedFlapjack`
module depends on an axiom other than `propext`, `Classical.choice` and
`Quot.sound`. A `sorry` shows up here as `sorryAx`, so this also rejects
unfinished proofs. -/

namespace SteppedFlapjack.Test.Axioms

open Lean Elab Command

/-- The axioms a `SteppedFlapjack` declaration may depend on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The declarations of the `SteppedFlapjack` modules, excluding the tests. -/
def packageDecls (env : Environment) : Array Name := Id.run do
  let mut out := #[]
  for (n, _) in env.constants.toList do
    if n.isInternal then continue
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    if (`SteppedFlapjack).isPrefixOf mod && !(`SteppedFlapjack.Test).isPrefixOf mod then
      out := out.push n
  return out

elab "#check_package_axioms" : command => do
  let decls := packageDecls (← getEnv)
  let mut offenders : Array MessageData := #[]
  for d in decls do
    let extra := (← collectAxioms d).filter (!allowedAxioms.contains ·)
    unless extra.isEmpty do offenders := offenders.push m!"{d}: {extra.toList}"
  if offenders.isEmpty then
    logInfo m!"{decls.size} SteppedFlapjack declarations use only {allowedAxioms}"
  else
    throwError m!"declarations using non-standard axioms:\n" ++
      MessageData.joinSep offenders.toList "\n"

#check_package_axioms

end SteppedFlapjack.Test.Axioms
