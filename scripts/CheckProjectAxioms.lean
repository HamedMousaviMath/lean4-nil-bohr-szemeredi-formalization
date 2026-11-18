import NilBohr
import Lean.Util.CollectAxioms

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let declarations := env.constants.fold (init := #[]) fun names name info =>
    match env.getModuleIdxFor? name with
    | some index =>
      let origin := env.allImportedModuleNames[index.toNat]!
      -- Code generation also adds unsafe declarations to the environment.
      if (`NilBohr).isPrefixOf origin && !info.isUnsafe && !info.isPartial then
        names.push name
      else
        names
    | none => names
  if declarations.isEmpty then
    throwError "No project declarations found"
  let (_, audit) := ((declarations.forM CollectAxioms.collect).run env).run {}
  let expected := #[`propext, `Classical.choice, `Quot.sound]
  let unexpected := audit.axioms.filter (fun name => !expected.contains name)
  unless unexpected.isEmpty do
    throwError "Unexpected project axiom dependencies: {unexpected}"
  logInfo m!"Project-wide audit passed for {declarations.size} safe declarations. Axioms: {audit.axioms}"
