module

public import Chazelle.Machine.Basic
public import Chazelle.Programs.Evidence

/-! # Reading a word through intermediate configurations

Postconditions give both concrete values of cells and frames saying which other
cells retain their values. To recover a word after several commands, follow these
equations back through the preceding configurations. The same equations may reside
in the proof fields of an environment, rather than in separate hypotheses.
-/

public meta section
namespace Chazelle.Programs
open Lean Meta Elab Tactic Machine

private def word (e : Expr) : Bool :=
  [``Config.nmem, ``Config.nreg, ``Config.rmem, ``Config.rreg, ``Config.output].contains
    e.getAppFn.constName!

/-- Normalize word reads using the known cells, frame equations and write equations. -/
elab "read_words" : tactic => withMainContext do
  let mut facts : Array (Expr × Expr) := #[]
  for d in (← getLCtx).decls.toList.reverse do
    if let some d := d then
      if !d.isImplementationDetail && (← isProp d.type) then
        facts ← Cost.foldFields (fun p t a => a.push (p,t)) (·.size ≥ 480) d.toExpr d.type 16 facts
  let mut ss := #[]
  for (p,t) in facts do
    let use ← forallTelescopeReducing t fun _ tail => do
      let some (_,l,_) := tail.eq? | return false
      return l.getAppFn.isConst && word l
    if use then
      let h ← Term.exprToSyntax p
      ss := ss.push (← `(Parser.Tactic.simpLemma| $h:term))
  evalTactic (← `(tactic| solve | simp (config := {maxSteps := 4000})
    (disch := first | assumption | decide | omega | address_omega) only
    [upd_same, upd_other, $ss,*]))

end Chazelle.Programs
