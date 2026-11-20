module
public import Chazelle.Programs.Verification

/-! # Symbolic evaluation of natural-register blocks

The register-only evaluator describes its effect as a succession of point writes.
Reduce the instruction lists, distribute the postcondition, then normalize each read.
The hypothesis at a symbolic address supplies the non-aliasing test; at a literal
address the test is just a computation.
-/
public meta section
namespace Chazelle.Programs
open Lean Elab Tactic Meta Machine

/-- Definitions of instruction lists and of their register semantics. Traverse the
lists' dependencies, not the geometric functions computing individual operands. -/
private partial def unfolds (env : Environment) (ns : Array Name) (seen : NameSet) : NameSet :=
  ns.foldl (init := seen) fun s n => Id.run do
    unless n.getRoot == `Chazelle && !s.contains n do return s
    let some (.defnInfo d) := env.find? n | return s
    let t := d.type.getForallBody
    let list := t.isAppOfArity ``List 1 && t.appArg!.isConstOf ``Instr
    let .str pre field := n | return s
    let family := #["regB", "regI", "dstI", "okB", "okI"]
    let evaluator := family.contains field
    unless list || evaluator do return s
    return unfolds env (d.value.getUsedConstants ++ (if evaluator then family.map (Name.str pre) else #[])) (s.insert n)

elab "register_block" hs:(" [" Parser.Tactic.simpLemma,* "]")? : tactic => withMainContext do
  let env ← getEnv
  let mut ns := unfolds env (← getMainTarget).getUsedConstants {}
  for d in ← getLCtx do
    unless d.isImplementationDetail do ns := unfolds env d.type.getUsedConstants ns
  let fs ← ns.toList.toArray.mapM fun n => `(Parser.Tactic.simpLemma| $(mkIdent n):ident)
  let extra : Array (TSyntax ``Parser.Tactic.simpLemma) := hs.map (fun h => h.raw[1].getSepArgs.map (⟨·⟩)) |>.getD #[]
  evalTactic (← `(tactic| (
    simp (config := {failIfUnchanged := false}) only [$fs,*, $extra,*]
    repeat' first | apply And.intro | intro
    all_goals first | rfl | assumption | decide | solve |
      simp (config := {failIfUnchanged := false})
        (disch := first | assumption | decide | omega | address_omega) only
        [upd_same, upd_other, *, $fs,*, $extra,*] <;> first | decide | assumption | omega | address_omega)))

end Chazelle.Programs
