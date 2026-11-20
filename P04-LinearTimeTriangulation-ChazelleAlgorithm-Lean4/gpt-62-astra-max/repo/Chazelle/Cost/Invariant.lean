module
public meta import Lean.Elab.Tactic.Omega
public meta import Lean.Meta.Tactic.Assert

/-!
# Reading bounds from invariants

RAM and geometric invariants package their equations and inequalities into conjunctions or
records. Expose their proof fields for arithmetic and rewriting, without eliminating the
original invariant (which a later step may need as a whole).
-/

public meta section
namespace Chazelle.Cost
open Lean Meta Elab Tactic

private def relation (e : Expr) : Bool :=
  [``Eq, ``Ne, ``LT.lt, ``LE.le].contains e.getForallBody.getAppFn.constName!

/-- Traverse proof-valued fields without changing the context. Both bound extraction and
proof search can stop the traversal once they have enough facts. -/
partial def foldFields {α} (visit : Expr → Expr → α → α) (stop : α → Bool)
    (p t : Expr) (depth : Nat) (acc : α) : MetaM α := do
  if depth == 0 || stop acc then return acc
  let t := t.consumeMData
  let mut acc := visit p t acc
  let .const n _ := (← whnf t).getAppFn | return acc
  let some info := getStructureInfo? (← getEnv) n | return acc
  for i in [:info.fieldNames.size] do
    let f := mkProj n i p
    let ft ← inferType f
    if ← isProp ft then acc ← foldFields visit stop f ft (depth-1) acc
  return acc

elab "invariant_facts" : tactic => withMainContext do
  let keep (p t : Expr) (hs : Array Hypothesis) :=
    if t.getForallBody.getAppFn.isConst && relation t && !p.isFVar && !hs.any (·.type == t) then
      hs.push ⟨`bound, t, p, .default, .default⟩
    else hs
  let mut facts := #[]
  for d in ← getLCtx do
    if !d.isImplementationDetail && (← isProp d.type) then
      facts ← foldFields keep (·.size ≥ 60) d.toExpr d.type 12 facts
  let (_,g) ← (← getMainGoal).assertHypotheses facts
  replaceMainGoal [g]

end Chazelle.Cost
