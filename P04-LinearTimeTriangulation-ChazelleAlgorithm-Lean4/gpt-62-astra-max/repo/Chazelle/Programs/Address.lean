module

public meta import Lean.Elab.Tactic.Omega
public meta import Lean.Elab.Tactic.Simp
public meta import Lean.Util.FoldConsts
public import Mathlib.Tactic.Linarith

/-!
# Arithmetic of register addresses

Register names, offsets, and tests for membership in scratch bands are defined close to
individual programs. To compare addresses we need their arithmetic meanings, but not the
implementations of the program, machine, or geometry in the surrounding context.
-/

public meta section
namespace Chazelle.Programs
open Lean Meta Elab Tactic

private def scalar : Expr → Bool
  | .forallE _ t b _ => (t.isConstOf ``Nat || t.isConstOf ``Bool) && scalar b
  | t => t.isConstOf ``Nat || t.isConstOf ``Bool || t == .sort .zero

/-- Collect the scalar definitions mentioned in a register calculation, including those in
another address definition. Ignore recursive functions. -/
private partial def addresses (env : Environment) (ns : Array Name) (seen : NameSet) : NameSet :=
  ns.foldl (init := seen) fun s n => Id.run do
    unless n.getRoot == `Chazelle && !s.contains n do return s
    let some (.defnInfo d) := env.find? n | return s
    unless scalar d.type do return s
    let deps := d.value.getUsedConstants
    if deps.contains n || deps.any (fun a => a matches .str _ "rec" | .str _ "brecOn") then
      return s
    return addresses env deps (s.insert n)

/-- Unfold the vocabulary of a register bound and solve its Presburger arithmetic. -/
elab "address_omega" : tactic => do
  evalTactic (← `(tactic| intros))
  withMainContext do
    let env ← getEnv
    let mut ds := addresses env (← getMainTarget).getUsedConstants {}
    for d in ← getLCtx do
      unless d.isImplementationDetail do ds := addresses env d.type.getUsedConstants ds
    let ids := (ds.toList ++ [``Bool.or_eq_true, ``Bool.or_eq_false_iff, ``Bool.and_eq_true,
      ``decide_eq_true_eq, ``decide_eq_false_iff_not]).map mkIdent |>.toArray
    let ss ← ids.mapM fun i => `(Parser.Tactic.simpLemma| $i:ident)
    evalTactic (← `(tactic| (simp (config := {failIfUnchanged := false}) only
      [$ss,*] at * <;> omega)))

private def dischargeGuards (arg : Term) : TermElabM Expr := do
  let mut e ← Term.elabTerm arg none
  let mut t ← inferType e
  while !t.isAppOf ``Not do
    let .forallE _ d b _ ← whnf t | break
    unless ← isProp d do break
    let h ← Term.elabTerm (← `(by first | assumption | rfl | decide | omega | address_omega | linarith)) d
    e := mkApp e h
    t := b.instantiate1 h
  return e

/-- Read a fact about an array cell or register at a particular index. Its guards (range,
non-aliasing, scratch membership, etc.) are proof arguments, discharged in the caller's
context. Keeping them as tactic obligations allows the index itself to be inferred by a rewrite. -/
elab "at_index " f:term:max i:term:max : term => do dischargeGuards (← `($f $i))

/-- Apply a guarded lemma that does not require an index argument. -/
elab "guarded " f:term:max : term => dischargeGuards f

end Chazelle.Programs
