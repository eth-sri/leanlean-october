module

public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.GCongr
public meta import Lean.Elab.Tactic.Omega

/-! # Polynomial size and cost estimates

When a bound `a ≤ b` is known, write the larger parameter as `a + d`. Polynomial
normalization then exposes common monomials on both sides of a cost estimate, and
nonnegativity of the remaining natural-number terms suffices.
-/

public meta section
namespace Chazelle.Cost
open Lean Elab Meta Tactic

private def expandBounds : TacticM Unit := do
  let fvars := (← getLCtx).getFVarIds
  for f in fvars do
    withMainContext do
      let some d := (← getLCtx).find? f | return ()
      let t := d.type.consumeMData
      unless (t.isAppOfArity ``LE.le 4 || t.isAppOfArity ``LT.lt 4) &&
          t.getAppArgs[0]!.isConstOf ``Nat do return ()
      let lhs := t.appFn!.appArg!
      let rhs := t.appArg!
      unless rhs.isFVar && !lhs.containsFVar rhs.fvarId! && !lhs.isRawNatLit do return ()
      let hyp ← Term.exprToSyntax d.toExpr
      let le ← if t.isAppOf ``LT.lt then `(Nat.succ_le_of_lt $hyp) else pure hyp
      evalTactic (← `(tactic| obtain ⟨_, he⟩ := Nat.exists_eq_add_of_le $le; subst he))

/-- Normalize a polynomial inequality after exposing nonnegative slack variables. -/
elab "cost_bound" : tactic => do
  evalTactic (← `(tactic| intros))
  withMainContext do
    evalTactic (← `(tactic| simp (config := {failIfUnchanged := false}) only
      [Nat.add_le_add_iff_right, Nat.add_lt_add_iff_right, Nat.lt_succ_iff] at *))
    unless (← getGoals).isEmpty do withMainContext expandBounds
  unless (← getGoals).isEmpty do
    evalTactic (← `(tactic| first | omega | (gcongr <;> omega) | (ring_nf at * <;> omega)))

end Chazelle.Cost
