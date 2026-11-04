import SteppedFlapjack

/-! Axiom audit: fails the build if any declaration in a `SteppedFlapjack`
module depends on an axiom other than `propext`, `Classical.choice` and
`Quot.sound`. A `sorry` shows up here as `sorryAx`, so this also rejects
unfinished proofs. Private and compiler-generated declarations are included,
and the audit fails if a non-test source file under `SteppedFlapjack/` is not
imported through `SteppedFlapjack` or if it finds no declarations at all.

Lake does not track the source listing as a dependency of this module, so
locally a newly added, unimported file is only reported once this module
rebuilds. CI builds the package from scratch, so it always runs. -/

namespace SteppedFlapjack.Test.Axioms

open Lean Elab Command

/-- The axioms a `SteppedFlapjack` declaration may depend on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Whether `mod` is a non-test `SteppedFlapjack` module. -/
def isPackageModule (mod : Name) : Bool :=
  ((`SteppedFlapjack).isPrefixOf mod || mod == `SteppedFlapjack) &&
    !(`SteppedFlapjack.Test).isPrefixOf mod && mod != `SteppedFlapjack.Tests

/-- Every declaration of the non-test `SteppedFlapjack` modules, including
private and compiler-generated ones. -/
def packageDecls (env : Environment) : Array Name := Id.run do
  let mut out := #[]
  for (n, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    if isPackageModule env.header.moduleNames[idx.toNat]! then out := out.push n
  return out

/-- The non-test module names of the `.lean` files under `SteppedFlapjack/`,
plus the root `SteppedFlapjack`. -/
def sourceModules : IO (Array Name) := do
  let dir : System.FilePath := "SteppedFlapjack"
  unless ← dir.isDir do
    throw <| IO.userError s!"axiom audit: source directory {dir} not found"
  let files ← dir.walkDir
  let mut mods := #[`SteppedFlapjack]
  for f in files do
    if f.extension == some "lean" then
      let comps := (f.withExtension "").components
      let mod := comps.foldl (fun n c => Name.str n c) Name.anonymous
      if isPackageModule mod then mods := mods.push mod
  return mods

elab "#check_package_axioms" : command => do
  let env ← getEnv
  -- Every non-test source module must be imported, or it would go unchecked.
  let imported := env.header.moduleNames
  let missing := (← sourceModules).filter (!imported.contains ·)
  unless missing.isEmpty do
    throwError m!"axiom audit: modules not imported by SteppedFlapjack: {missing.toList}"
  let decls := packageDecls env
  if decls.isEmpty then throwError "axiom audit: no SteppedFlapjack declarations found"
  let mut offenders : Array MessageData := #[]
  for d in decls do
    let extra := (← collectAxioms d).filter (!allowedAxioms.contains ·)
    unless extra.isEmpty do offenders := offenders.push m!"{d}: {extra.toList}"
  if offenders.isEmpty then
    logInfo m!"{decls.size} declarations in {imported.filter isPackageModule |>.size} \
      SteppedFlapjack modules use only {allowedAxioms}"
  else
    throwError m!"declarations using non-standard axioms:\n" ++
      MessageData.joinSep offenders.toList "\n"

#check_package_axioms

end SteppedFlapjack.Test.Axioms
