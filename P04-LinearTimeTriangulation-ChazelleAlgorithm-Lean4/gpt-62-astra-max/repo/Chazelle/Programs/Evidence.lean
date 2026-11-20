module

public import Chazelle.Programs.Address
public import Chazelle.Cost.Invariant
public meta import Lean.Elab.Tactic.Rewrite

/-! # Applying a verification rule from its data

Many rules interleave data (a program, register or index) with proofs of range, frame
and invariant conditions. In a context already containing those facts, only the data
distinguish the application (inferable trailing data can be omitted). `from_facts (rule data …)` elaborates an ordinary application
of `rule`, solving the explicit proof arguments. An optional list supplies additional
facts, for example fields of an invariant. Named arguments work as usual. -/

public meta section
namespace Chazelle.Programs
open Lean Meta Elab Term Tactic

/-- Read a fact from a hypothesis or one of its proof fields. For an indexed fact,
instantiate the index by matching the goal and check the remaining guards locally. -/
elab "local_fact" : tactic => withMainContext do
  let g ← getMainGoal
  let target ← instantiateMVars (← g.getType)
  let mut ps : Array (Expr × Expr) := #[]
  for d in (← getLCtx).decls.toList.reverse do
    if let some d := d then
      if !d.isImplementationDetail && (← isProp d.type) then
        ps ← Cost.foldFields (fun p t acc => acc.push (p,t)) (·.size ≥ 160) d.toExpr d.type 16 ps
  for (p,t) in ps do
    if t.getAppFn == target.getAppFn && (← isDefEq t target) then
      g.assign p; replaceMainGoal []; return
  for (p,t) in ps do
    unless t.isForall && t.getForallBody.getAppFn == target.getAppFn do continue
    let saved ← saveState
    try
      replaceMainGoal (← g.apply p)
      evalTactic (← `(tactic| all_goals first | assumption | rfl | decide | omega))
      return
    catch _ => saved.restore
  throwError "no matching local fact"

/-- Reassemble a postcondition (a conjunction or proof record) from the available facts.
Do not try arbitrary inductive constructors when an arithmetic obligation remains. -/
elab "record_facts" : tactic => do
  let rec solve : Nat → TacticM Unit
    | 0 => throwError "postcondition nested too deeply"
    | depth+1 => withMainContext do
      try evalTactic (← `(tactic| first | assumption | rfl | local_fact)); return
      catch _ => pure ()
      let t ← whnf (← getMainTarget)
      if t.getAppFn.isConst && (← isProp t) && (getStructureInfo? (← getEnv) t.getAppFn.constName!).isSome then
        let gs ← (← getMainGoal).constructor
        for g in gs do setGoals [g]; solve depth
      else evalTactic (← `(tactic| first | decide | omega | address_omega))
  focus (solve 24)

/-- Rewrite at the index selected by the match, checking a rule's side conditions before
applying the next rewrite. This is useful for reads across guarded writes and for
bounds that depend on a matched index. -/
elab "rw_facts" rs:Lean.Parser.Tactic.rwRuleSeq loc:(Lean.Parser.Tactic.location)? : tactic => focus do
  let place := expandOptLocation (mkOptionalNode loc)
  withRWRulesSeq (← getRef)[0] rs fun symm term => do
    withLocation place (rewriteLocalDecl term symm ·) (rewriteTarget term symm)
      (fun _ => throwError "no matching occurrence")
    let main :: guards ← getGoals | return
    setGoals guards
    evalTactic (← `(tactic| all_goals first | assumption | rfl | decide | omega | local_fact | address_omega))
    unless (← getUnsolvedGoals).isEmpty do throwError "unsolved rewrite condition"
    setGoals [main]
  evalTactic (← `(tactic| try rfl))

elab "from_facts " t:term:max hs:(" [" term,* "]")? : term <= goal => do
  let t := if t.raw.isOfKind ``Parser.Term.paren then t.raw[1] else t.raw
  let (head, args) := if t.isOfKind ``Parser.Term.app then (t[0], t[1].getArgs) else (t, #[])
  let (named, data) := args.partition (·.isOfKind ``Parser.Term.namedArgument)
  let f ← if head.isIdent then
    match ← resolveId? head (withInfo := false) with
    | some e => pure e
    | none => elabTerm head none
  else elabTerm head none
  let extras : Array Term := hs.map (fun h => h.raw[1].getSepArgs.map (⟨·⟩)) |>.getD #[]
  let hints ← extras.mapM fun e => `(tactic| exact $e)
  let pf ← `(by first | assumption $[| $hints:tactic]* | rfl | local_fact | decide | omega | address_omega)
  let filled ← forallTelescope (← inferType f) fun xs _ => do
    let mut res := named
    let mut i := 0
    for x in xs do
      let d ← x.fvarId!.getDecl
      unless d.binderInfo.isExplicit && !named.any (fun a => a[1].getId == d.userName) do continue
      if ← isProp d.type then res := res.push pf.raw
      else if let some a := data[i]? then res := res.push a; i := i+1
      else res := res.push (← `(_)).raw
    if i != data.size then throwError "too many data arguments"
    return res
  elabTermEnsuringType (mkNode ``Parser.Term.app #[head, mkNullNode filled]) goal

end Chazelle.Programs
