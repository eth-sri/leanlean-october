module

public meta import Chazelle.Programs.Tactics
public meta import Lean.Util.FoldConsts

/-! Arithmetic for layout predicates of a single RAM stage. The tactic unfolds small
natural-number definitions used by the goal, without making those definitions global simp rules. -/

public meta section
open Lean Meta Elab Tactic

private def layoutType : Expr → Bool
  | .forallE _ a b _ => (a.isConstOf ``Nat || a.isConstOf ``Bool) && layoutType b
  | e => e.isConstOf ``Nat || e.isConstOf ``Bool || e.isProp

private def layoutDefs (env : Environment) (roots : Array Name) : Array Name := Id.run do
  let mut pending := roots
  let mut seen : NameSet := {}
  let mut defs := #[]
  for _ in [:4] do
    let layer := pending
    pending := #[]
    for n in layer do
      if seen.contains n then continue
      seen := seen.insert n
      unless (`Chazelle).isPrefixOf (privateToUserName n) do continue
      let some (.defnInfo d) := env.find? n | continue
      unless layoutType d.type && d.value.approxDepth < 35 do continue
      defs := defs.push n
      pending := pending ++ d.value.getUsedConstants
    if pending.isEmpty then break
  return defs

/-- Solve a register guard by unfolding its local layout and using linear arithmetic. -/
elab "register_guard" : tactic => withMainContext do
  let old ← saveState
  try
    evalTactic (← `(tactic| solve | reg_omega))
  catch _ =>
    old.restore
    let mut ns := (← getMainTarget).getUsedConstants
    for d in ← getLCtx do
      unless d.isImplementationDetail do ns := ns ++ d.type.getUsedConstants
    let defs := layoutDefs (← getEnv) ns
    let rules ← defs.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
    evalTactic (← `(tactic| solve |
      (simp (config := {failIfUnchanged := false}) only
        [ram_layout, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, $rules,*] at * <;>
        first | assumption | decide | omega)))

end
