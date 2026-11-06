module

public meta import Lean
public meta import Chazelle.Spec

public meta section

open Lean Meta Elab Tactic
namespace Chazelle.Tactic

private partial def resultType : Expr → Expr
  | .forallE _ _ b _ => resultType b
  | e => e

private partial def body : Expr → Expr
  | .lam _ _ b _ => body b
  | e => e

private def arithmeticType (e : Expr) : Bool :=
  let e := resultType e
  e.isConstOf ``Nat || e.isConstOf ``Int || e.isConstOf ``Bool || e == .sort .zero

private def base (n : Name) : Bool :=
  n.toString.startsWith "Nat." || n.toString.startsWith "Int." ||
  n.toString.startsWith "Bool." || n.toString.startsWith "Decidable." ||
  n.toString.startsWith "inst" || #[``Nat, ``Int, ``Bool, ``decide, ``BEq.beq, ``bne, ``And, ``Or, ``Not, ``Eq, ``Ne, ``True,
    ``False, ``LE.le, ``LT.lt, ``HAdd.hAdd, ``HSub.hSub, ``HMul.hMul, ``HDiv.hDiv,
    ``HMod.hMod, ``OfNat.ofNat, ``Neg.neg, ``Min.min, ``Max.max].contains n

abbrev ArithMemo := Std.HashMap Name Bool
initialize arithMemo : IO.Ref ArithMemo ← IO.mkRef {}

private partial def arithAlias (env : Environment) (n : Name) : StateM ArithMemo Bool := do
  if let some b := (← get)[n]? then return b
  modify (·.insert n false)
  let some (.defnInfo ci) := env.find? n | return false
  unless arithmeticType ci.type do return false
  let deps := (body ci.value).getUsedConstants
  if deps.size ≥ 40 then return false
  for d in deps do
    if base d then continue
    if (env.getProjectionFnInfo? d).isSome &&
        (env.find? d).any (fun ci => arithmeticType ci.type) then continue
    if d.toString.startsWith "Chazelle." && (← arithAlias env d) then continue
    return false
  modify (·.insert n true)
  return true

private def isAlias (env : Environment) (n : Name) : IO Bool := do
  let (b, c) := (arithAlias env n).run (← arithMemo.get)
  arithMemo.set c
  return b

private def runAtCaller (stx : Syntax) : TacticM Unit := do
  let info := SourceInfo.fromRef (← getRef)
  withoutRecover <| evalTactic (stx.rewriteBottomUp (Syntax.setInfo info))

private def arithmeticAliases (context := true) : TacticM (Array Name) := do
  let env ← getEnv
  let mut ns : Array Name := #[]
  let mut es := #[(← getMainTarget)]
  if context then
    for decl in ← getLCtx do
      unless decl.isImplementationDetail do es := es.push decl.type
  for e in es do
    for n in e.getUsedConstants do
      if !ns.contains n && n.toString.startsWith "Chazelle." then
        if ← isAlias env n then ns := ns.push n
  let mut i := 0
  while i < ns.size do
    let n := ns[i]!
    i := i + 1
    if let some ci := env.find? n then
      for d in (body (ci.value?.getD default)).getUsedConstants do
        if !ns.contains d && d.toString.startsWith "Chazelle." then
          if ← isAlias env d then ns := ns.push d
  return ns

/-- Normalize the small arithmetic aliases used for registers, memory offsets and
register ranges, then use Presburger arithmetic. Semantic RAM predicates are not
unfolded. -/
elab "omega_nf" : tactic => withMainContext <|
    withOptions (fun o => o.setBool `linter.unusedSimpArgs false) do
  let saved ← saveState
  let env ← getEnv
  let targetAliases ← arithmeticAliases false
  unless targetAliases.isEmpty do
    let txt := "solve | simp [" ++ String.intercalate ", " (targetAliases.toList.map toString) ++ "]"
    if let .ok stx := Parser.runParserCategory env `tactic txt then
      try
        runAtCaller stx
        return
      catch _ => saved.restore (restoreInfo := true)
  try
    withoutRecover <| runAtCaller (← `(tactic| omega))
    return
  catch _ => saved.restore (restoreInfo := true)
  let env ← getEnv
  let ns ← arithmeticAliases
  if ns.isEmpty then
    runAtCaller (← `(tactic| omega))
  else
    let args := "[" ++ String.intercalate ", " (ns.toList.map toString) ++ "]"
    let txt := "first | (simp " ++ args ++ "; all_goals omega) | " ++
      "(simp_all only " ++ args ++ "; all_goals omega) | " ++
      "(simp only " ++ args ++ " at *; all_goals omega)"
    match Parser.runParserCategory env `tactic txt with
    | .ok stx => runAtCaller stx
    | .error msg => throwError "{msg}"

/-- Discharge structural RAM invariants by congruence closure, after exposing the
small arithmetic aliases and invariant records in the local context. -/
elab "ram_grind" : tactic => withMainContext do
  let env ← getEnv
  let mut ns ← arithmeticAliases
  let mut es := #[(← getMainTarget)]
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do es := es.push decl.type
  for e in es do
    for n in e.getUsedConstants do
      unless ns.contains n || !n.toString.startsWith "Chazelle." do
        if let some ci := env.find? n then
          if resultType ci.type == .sort .zero &&
              ((getStructureInfo? env n).isSome || (match ci with
                | .defnInfo ci => ci.value.sizeWithoutSharing < 500
                | _ => false)) then
            ns := ns.push n
  ns ← ns.filterM (fun n => return !(← isReducible n))
  let txt := "grind [" ++ String.intercalate ", " (ns.toList.map toString) ++ "]"
  match Parser.runParserCategory env `tactic txt with
  | .ok stx => runAtCaller stx
  | .error msg => throwError "{msg}"

/-- Congruence closure with the small definitions occurring in the goal or local
invariants exposed. Explicit hints are needed only for supporting lemmas. -/
private def coreGrind (context : Bool) (extra : Array String) : TacticM Unit := withMainContext do
  let env ← getEnv
  let mut ns ← arithmeticAliases context
  let mut es := #[(← getMainTarget)]
  if context then
    for d in ← getLCtx do
      unless d.isImplementationDetail do
        es := es.push d.type
        if let some v := d.value? then es := es.push v
  for e in es do
    for n in e.getUsedConstants do
      unless ns.contains n || !n.toString.startsWith "Chazelle." do
        if let some ci := env.find? n then
          let eligible := if (getStructureInfo? env n).isSome then
              resultType ci.type == .sort .zero
            else match ci with
              | .defnInfo d =>
                (d.value.sizeWithoutSharing < 150 ||
                  (resultType ci.type == .sort .zero && d.value.sizeWithoutSharing < 500)) &&
                  !d.value.getUsedConstants.contains n
              | _ => false
          if eligible then ns := ns.push n
  ns ← ns.filterM (fun n => return !(← isReducible n))
  let ids := ns.toList.map toString ++ extra.toList
  let txt := "grind [" ++ String.intercalate ", " ids ++ "]"
  match Parser.runParserCategory env `tactic txt with
  | .ok stx => runAtCaller stx
  | .error msg => throwError "{msg}"

private def coreGrindAuto (extra : Array String := #[]) : TacticM Unit := do
  let saved ← saveState
  let ok ← tryCatchRuntimeEx (do
    withOptions (fun o => o.set `maxHeartbeats (1000 : Nat)) <|
      withTheReader Core.Context (fun c => { c with maxHeartbeats := 1000000 }) <|
        withCurrHeartbeats <| coreGrind false extra
    pure true) (fun _ => pure false)
  unless ok do
    saved.restore (restoreInfo := true)
    coreGrind true extra

elab "core_grind" : tactic => coreGrindAuto
elab "core_grind" "[" ids:ident,* "]" : tactic =>
  coreGrindAuto (ids.getElems.map (·.getId.toString))

/-- Simplify a RAM update, using arithmetic register-range invariants to discharge
unchanged-register conditions. Local configuration abbreviations are expanded only
where needed by the simplifier. -/
elab "ram_simp" : tactic => do
  runAtCaller (← `(tactic| (intros; simp +zetaDelta +contextual
    (disch := omega_nf) [Chazelle.upd, ite_eq_right, *])))

/-- Simplify RAM updates throughout the context as well as the goal. This keeps
symbolic-execution word bounds available after the register values are normalized. -/
elab "ram_all" : tactic => do
  runAtCaller (← `(tactic| (intros; simp +zetaDelta +contextual
    (disch := omega_nf) [Chazelle.upd, ite_eq_right, *] at *; all_goals try assumption)))

end Chazelle.Tactic
