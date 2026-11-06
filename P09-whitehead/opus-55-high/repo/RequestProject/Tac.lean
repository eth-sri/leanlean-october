import Lean.Elab.Command

open Lean Elab Command in
/-- The backward-compatibility options used throughout the project. -/
elab "bwd" : command => modifyScope fun s => { s with opts :=
  ((s.opts.setBool `backward.defeqAttrib.useBackward true).setBool
    `backward.isDefEq.respectTransparency false).setBool `backward.isDefEq.respectTransparency.types false }

/-- `rw` at default transparency. -/
macro "rwd " s:Lean.Parser.Tactic.rwRuleSeq l:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| rw (config := { transparency := .default }) $s:rwRuleSeq $[$l:location]?)

macro "rwd " s:Lean.Parser.Tactic.rwRuleSeq : conv =>
  `(conv| rw (config := { transparency := .default }) $s:rwRuleSeq)

/-- Linear induction on a finitely supported function, closing the zero and sum cases. -/
syntax "lin_ind " ident ident ident (" using " tactic)? " => " tacticSeq : tactic
macro_rules
  | `(tactic| lin_ind $c $e $n $[using $t]? => $s) => do
    let t ← match t with | some t => pure t | none => `(tactic| simp_all)
    `(tactic| induction $c:ident using $(Lean.mkIdent `Finsupp.induction_linear) with
      | zero => simp
      | add _ _ _ _ => $t:tactic
      | single $e $n => $s)

/-- Linear induction on a finitely supported function with an explicit sum case. -/
syntax "lin_ind " ident " with " ident ident ident ident " => " tacticSeq " | " ident ident " => " tacticSeq : tactic
macro_rules
  | `(tactic| lin_ind $c with $a $b $ha $hb => $t | $e $n => $s) =>
    `(tactic| induction $c:ident using $(Lean.mkIdent `Finsupp.induction_linear) with
      | zero => simp
      | add $a $b $ha $hb => $t
      | single $e $n => $s)
