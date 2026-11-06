module
public meta import Lean.Elab.Command

public meta section
open Lean Elab Command

/-- Re-export every public declaration of one module under its relative name in
another namespace. This keeps compatibility wrappers free of duplicated proofs. -/
elab "export_module " mod:ident " from " ns:ident : command => do
  let env ← getEnv
  let some idx := env.getModuleIdx? mod.getId
    | throwError "unknown module {mod.getId}"
  let curr ← getCurrNamespace
  for declName in env.header.moduleData[idx]!.constNames do
    if ns.getId.isPrefixOf declName && !declName.isInternal then
      let shortName := declName.replacePrefix ns.getId .anonymous
      modify fun s => { s with env := Lean.addAlias s.env (curr ++ shortName) declName }
