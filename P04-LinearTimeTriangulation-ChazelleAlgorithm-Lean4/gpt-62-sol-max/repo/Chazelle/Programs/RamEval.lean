module

public import Chazelle.Programs.Tactics
public meta import Mathlib.Tactic.Ring
public meta import Lean.Elab.Tactic.Meta

/-! Proof automation for register blocks and for transporting data across RAM frames. -/

namespace Chazelle.Programs

open Machine Lean.Parser.Tactic

/-- A block preserves any register outside its list of destinations. -/
public theorem regB_keep {m f : ℕ → ℕ} {l : List Instr} {q : ℕ}
    (h : q ∉ l.map dstI) : regB m l f q = f q :=
  regB_other m l f fun _ hi e => h (e ▸ List.mem_map_of_mem hi)

public meta section

/-- Reduce a block's write footprint and check that the requested register is outside it. -/
syntax "register_keep" (simpArgs)? : tactic
macro_rules
  | `(tactic| register_keep $[[$rs,*]]?) => do
    let rs := (rs.map (·.getElems)).getD #[]
    `(tactic| solve
      | (intros; apply regB_keep
         simp (config := {failIfUnchanged := false}) only
           [dstI, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
            ram_layout, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, $rs,*] at *
         all_goals first | contradiction | tauto | omega))

/-- Simplify the register expressions in a straight-line block, using linear
arithmetic for separation of symbolic registers. Optional rules specify the block
and any domain-specific equations used by its side conditions. In `normalized`
mode, it first normalizes the layout in the hypotheses and also compares the
linear address expressions underneath memory reads. -/
syntax "register_block" ("normalized")? (simpArgs)? : tactic
macro_rules
  | `(tactic| register_block $[normalized%$norm]? $[[$args,*]]?) => do
    let args := (args.map (·.getElems)).getD #[]
    let step ← `(tactic| simp (config := { failIfUnchanged := false, maxDischargeDepth := 1 })
      (disch := first | assumption | decide | omega |
        (simp only [ram_layout, Nat.reduceAdd] at * <;> omega)) only
      [reg_check, regB, regI, dstI, ram_layout, ram_cfg, Nat.reduceEqDiff, Nat.reduceAdd,
       Nat.reduceSub, Nat.reduceMul, Nat.zero_add, Nat.add_zero, List.length_cons, List.length_nil,
       and_true, true_and, *, $args,*])
    if norm.isSome then
      return ← `(tactic| solve
        | (simp only [ram_layout, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul] at *
           $step
           repeat' (first | assumption | rfl | apply And.intro | intro)
           all_goals first | reg_omega | ($step; reg_omega) |
             (congr 1 <;> reg_omega) | (congr 1 <;> (first | reg_omega | congr 1 <;> reg_omega)) |
             (ring_nf at * <;> reg_omega)))
    `(tactic| solve
      | (intros; $step; repeat (first | assumption | rfl | apply And.intro | intro)
         all_goals first | reg_omega | ($step; reg_omega) |
           ((try simp only [ram_layout, Nat.reduceAdd] at *); $step <;> first | reg_omega |
             (ring_nf at *; first | assumption | omega))))

open Lean Meta Elab Tactic

/-- Elaborate an application and discharge its explicit proof holes using register
arithmetic. This also works in an `obtain` or `have` where the result type is inferred. -/
syntax (name := ramApp) "ram_app%" term:max : term

@[term_elab ramApp] def elabRamApp : Term.TermElab := fun stx expected => do
  let old := (← getMCtx).decls
  let e ← Term.elabTerm stx[1] expected
  Term.synthesizeSyntheticMVars
  for hole in ← getMVars e do
    unless old.contains hole || (← hole.isAssigned) || !(← hole.getKind).isSyntheticOpaque do
      unless ← isProp (← hole.getType) do
        throwErrorAt stx "ram_app% only discharges proof arguments"
      let (rest, _) ← Elab.runTactic hole (← `(tactic| first | rfl | reg_omega))
        (← readThe Term.Context) (← getThe Term.State)
      unless rest.isEmpty do
        throwErrorAt stx "ram_app% did not solve all its side conditions"
  instantiateMVars e


private def stateRead (e : Expr) : Bool :=
  (e.find? fun a => a.isConstOf ``Config.nreg || a.isConstOf ``Config.rreg ||
      a.isConstOf ``Config.nmem || a.isConstOf ``Config.rmem || a.isConstOf ``Config.output ||
      a.isConstOf ``Config.pc || a.isConstOf ``upd ||
      match a with | .proj ``Config .. => true | _ => false).isSome

private partial def stateResult (e : Expr) : Bool :=
  match e with
  | .forallE _ _ b _ => stateResult b
  | .app (.app (.app (.const ``Eq _) _) lhs) _ => stateRead lhs
  | _ => false

/-- Look through conjunctive and structured frames, but only index equations for reads.
In particular, geometric invariants and quantified word bounds are not simp rules. -/
private partial def collectReads (f : Expr) (fuel : Nat) (acc : Array Expr) : MetaM (Array Expr) := do
  if fuel == 0 then return acc
  let ty ← inferType f
  if stateResult ty then return acc.push f
  let some n := ty.getAppFn.constName? | return acc
  if n != ``And && !(`Chazelle).isPrefixOf n then return acc
  let ty ← whnf ty
  if ty.isAppOf ``And then
    let acc ← collectReads (← mkAppM ``And.left #[f]) (fuel - 1) acc
    return ← collectReads (← mkAppM ``And.right #[f]) (fuel - 1) acc
  let some n := ty.getAppFn.constName? | return acc
  let env ← getEnv
  let some str := getStructureInfo? env n | return acc
  let mut acc := acc
  for name in str.fieldNames do
    let some proj := getProjFnForField? env n name | continue
    try
      let pr ← mkAppM proj #[f]
      if stateResult (← inferType pr) then acc := acc.push pr
    catch _ => pure ()
  return acc

/-- Follow the local frame equations back to the state where a register or cell was set.
External equations and definitions may be supplied as additional simp rules. -/
syntax "frame_simp" (simpArgs)? : tactic
elab_rules : tactic
  | `(tactic| frame_simp $[[$args,*]]?) => withMainContext do
    let args := (args.map (·.getElems)).getD #[]
    let stx ← `(tactic| simp (config := {maxSteps := 1200, maxDischargeDepth := 1})
      (disch := first | assumption | decide | omega |
        (simp only [ram_layout, beq_eq_false_iff_ne, decide_eq_false_iff_not, Bool.or_eq_false_iff,
          Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, $args,*] at * <;> omega)) only
      [ram_cfg, ram_layout, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMul, Nat.reduceEqDiff,
        Nat.zero_add, Nat.add_zero, and_true, true_and, $args,*])
    let r ← mkSimpContext stx (eraseLocal := false) (ignoreStarArg := false)
    let mut ts := r.ctx.simpTheorems
    for d in ← getLCtx do
      unless d.isImplementationDetail do
        let rules ← collectReads d.toExpr 9 #[]
        for p in rules do
          try
            ts ← ts.addTheorem (.other (← mkFreshUserName `read)) p
          catch _ => pure ()
    let (goal, _) ← r.dischargeWrapper.with fun disch => do
      simpTarget (← getMainGoal) (r.ctx.setSimpTheorems ts) r.simprocs disch
    replaceMainGoal goal.toList

/-- Close a frame or word-bound goal after rewriting the relevant state reads. -/
syntax "frame_finish" (simpArgs)? : tactic
macro_rules
  | `(tactic| frame_finish $[$args]?) => `(tactic| solve
    | (repeat (first | assumption | rfl | apply And.intro | intro)
       all_goals first | assumption | decide | omega |
         (frame_simp $[$args]? <;> first | assumption | rfl | decide | reg_omega | (ring; done))))

end

end Chazelle.Programs

namespace Chazelle.Programs

open Lean Meta Elab Tactic Lean.Parser.Tactic Machine Machine.Stmt

public section

/-- Extend a postcondition using properties of the execution itself. -/
theorem spec_extend {P : Polygon} {W : ℕ} {s : Stmt} {c : Config} {Q R : Config → ℕ → Prop}
    (run : ∃ d k, Exec P W s c d k ∧ Q d k)
    (post : ∀ d k, Exec P W s c d k → Q d k → R d k) :
    ∃ d k, Exec P W s c d k ∧ R d k :=
  let ⟨d, k, ex, q⟩ := run
  ⟨d, k, ex, post d k ex q⟩


/-- Branches of a register comparison can be verified under their own guards. -/
theorem spec_ifLtN_cases {P : Polygon} {W a b : ℕ} {t e : Stmt}
    {c : Config} {Q : Config → ℕ → Prop}
    (ht : c.nreg a < c.nreg b → ∃ d k, Exec P W t c d k ∧ Q d (k + 1))
    (he : ¬ c.nreg a < c.nreg b → ∃ d k, Exec P W e c d k ∧ Q d (k + 2)) :
    ∃ d k, Exec P W (.ifLtN a b t e) c d k ∧ Q d k :=
  if h : c.nreg a < c.nreg b then spec_ifLtN_true h (ht h) else spec_ifLtN_false h (he h)

theorem spec_ifLtR_cases {P : Polygon} {W a b : ℕ} {t e : Stmt}
    {c : Config} {Q : Config → ℕ → Prop}
    (ht : c.rreg a < c.rreg b → ∃ d k, Exec P W t c d k ∧ Q d (k + 1))
    (he : ¬ c.rreg a < c.rreg b → ∃ d k, Exec P W e c d k ∧ Q d (k + 2)) :
    ∃ d k, Exec P W (.ifLtR a b t e) c d k ∧ Q d k :=
  if h : c.rreg a < c.rreg b then spec_ifLtR_true h (ht h) else spec_ifLtR_false h (he h)

theorem spec_single {P : Polygon} {W : ℕ} {c : Config} {i : Instr} {Q : Config → ℕ → Prop}
    (h : ∃ d k, Exec P W (block [i]) c d k ∧ Q d k) :
    ∃ d k, Exec P W (.instr i) c d k ∧ Q d k := by
  obtain ⟨d, k, e, q⟩ := h
  cases e with
  | seq e rest => cases rest; exact ⟨_, _, e, q⟩

end

public meta section

/-- View a verification goal without unfolding any user definitions in its postcondition. -/
private def withSpec {α : Type} (e : Expr)
    (f : Expr → Expr → Expr → Expr → Array Expr → Expr → MetaM α) : MetaM α := do
  let (``Exists, #[_, p]) := (← whnfR e).getAppFnArgs |
    throwError "expected an existential execution specification"
  lambdaTelescope p fun ds b => do
    let (``Exists, #[_, q]) := (← whnfR b).getAppFnArgs |
      throwError "expected an existential cost"
    lambdaTelescope q fun ks r => do
      let (``And, #[ex, post]) := (← whnfR r).getAppFnArgs |
        throwError "expected execution and postcondition"
      let (``Exec, #[P, W, s, c, _, _]) := ex.getAppFnArgs |
        throwError "expected an execution"
      f P W s c (ds ++ ks) post

private def derivablePost (e : Expr) : Bool :=
  let n := e.getAppFn.constName?
  n == some `Chazelle.Core.SignK.FrameB || n == some ``WordsBounded

private partial def payload (post : Expr) : MetaM (Option Expr) := do
  if derivablePost post then return none
  let (``And, #[a,b]) := post.getAppFnArgs | return some post
  match ← payload a, ← payload b with
  | some l, some r => return some (mkApp2 (mkConst ``And) l r)
  | l, r => return l.or r

/-- Remove the static frames (and output word bounds) from an execution goal. It is
  enough to prove the remaining postcondition by symbolic execution. A `disch`
  clause can supply a write check for a block with symbolic register indices. -/
syntax "exec_frame" (discharger)? : tactic

elab_rules : tactic
  | `(tactic| exec_frame $[$discharge]?) => withMainContext do
    let g ← getMainGoal
    let (h, found) ← withSpec (← g.getType) fun P W s c args post => do
      let q ← payload post
      let f ← mkLambdaFVars args (q.getD (mkConst ``True))
      pure (← mkAppOptM ``spec_extend #[P, W, s, c, f, ← mkLambdaFVars args post], q != some post)
    unless found do throwError "no static frame in the postcondition"
    let [run, proof] ← g.apply h | throwError "unexpected execution specification"
    let (args, proof) ← proof.introN 4
    let ex := mkFVar args[2]!
    let q := mkFVar args[3]!
    let rec dischargePost (n : Nat) (goal : MVarId) (q : Option Expr) : TacticM Unit := goal.withContext do
      let n + 1 := n | throwError "postcondition is too deeply nested"
      let t ← whnfR (← goal.getType)
      if derivablePost t then
        if t.getAppFn.isConstOf ``WordsBounded then
          let p ← mkAppM ``Exec.wb_right #[ex]
          unless ← isDefEq (← inferType p) t do throwError "not the output word bound"
          goal.assign p
        else
          let #[B, _, _] := t.getAppArgs | throwError "invalid register frame"
          let e := (← inferType ex).getAppArgs
          let result ← mkAppOptM `Chazelle.Core.SignK.exec_frameB
            #[e[0]!, e[1]!, B, e[2]!, e[3]!, e[4]!, e[5]!, ex]
          let [check] ← goal.apply result | throwError "invalid write check"
          setGoals [check]
          match discharge with
          | some d => evalTactic d.raw[3]
          | none => evalTactic (← `(tactic| first | assumption | rfl | decide))
          unless (← getUnsolvedGoals).isEmpty do throwError "unsolved static write check"
        return
      let (``And, #[a,b]) := t.getAppFnArgs |
        let p ← q.getDM (throwError "missing postcondition")
        unless ← isDefEq (← inferType p) t do throwError "postcondition shape changed"
        goal.assign p
      let [l,r] ← goal.apply (mkConst ``And.intro) | throwError "invalid conjunction"
      match ← payload a, ← payload b, q with
      | some _, some _, some q =>
        dischargePost n l (some (← mkAppM ``And.left #[q]))
        dischargePost n r (some (← mkAppM ``And.right #[q]))
      | a', b', q =>
        dischargePost n l (if a'.isSome then q else none)
        dischargePost n r (if b'.isSome then q else none)
    let rest ← getGoals
    dischargePost 100 proof (some q)
    setGoals (run :: rest.drop 1)

/-- Finish the arithmetic and unchanged-state conditions of a small RAM fragment.
  The caller can give the equations of any domain-specific postcondition. -/
syntax "ram_post" (simpArgs)? : tactic
macro_rules
  | `(tactic| ram_post $[[$rs,*]]?) => do
    let rs := (rs.map (·.getElems)).getD #[]
    `(tactic| solve
      | (repeat (first | assumption | rfl | apply And.intro | intro)
         all_goals first | decide | omega |
           (ram_simp [*, $rs,*] <;> first | assumption | rfl | decide | reg_omega | (ring; done)) |
           (frame_finish [$rs,*]) |
           (simp (disch := reg_omega) [*, $rs,*] <;> first | assumption | decide | reg_omega | (ring; done))))

/-- Compose `Exec` certificates for a short straight-line or conditional fragment.
  Unknown loop invariants and domain postconditions stay in the calling theorem. -/
syntax "ram_exec" ("cases")? (simpArgs)? : tactic
macro_rules
  | `(tactic| ram_exec $[cases%$split]? $[[$rs,*]]?) => do
    let rs := (rs.map (·.getElems)).getD #[]
    let branch ← if split.isSome then
      `(tactic| (first | refine spec_ifLtN_cases ?_ ?_ | refine spec_ifLtR_cases ?_ ?_) <;>
        (intro h; try ram_simp [*, $rs,*] at h))
    else `(tactic| fail)
    `(tactic| solve
      | (try exec_frame
         repeat' (first
           | exec_block! (disch := ram_post [$rs,*])
           | refine spec_seq ?_
           | (refine spec_skip ‹WordsBounded _ _› ?_; ram_post [$rs,*])
           | (refine spec_ifLtN_true ?_ ?_; focus ram_post [$rs,*])
           | (refine spec_ifLtN_false ?_ ?_; focus ram_post [$rs,*])
           | (refine spec_ifLtR_true ?_ ?_; focus ram_post [$rs,*])
           | (refine spec_ifLtR_false ?_ ?_; focus ram_post [$rs,*])
           | (refine spec_single ?_; exec_block! (disch := ram_post [$rs,*]))
           | ($branch:tactic))
         all_goals ram_post [$rs,*]))

/-- Compose already verified executions along the control flow of a statement.
A branch is taken only when its guard is provable; loops use local certificates.
The tactic infers intermediate states as well as the exact accumulated cost. -/
syntax "ram_path" (simpArgs)? : tactic

private partial def solvePath (fuel : Nat) (edges : Array Expr) (guard : Syntax)
    (g : MVarId) : TacticM Unit := g.withContext do
  if fuel == 0 then throwError "ram_path: path is too long"
  if ← g.isAssigned then return
  let t ← instantiateMVars (← g.getType)
  let (``Exec, #[_, _, s, _, _, _]) := t.getAppFnArgs | throwError "ram_path: expected Exec"
  for e in edges do
    if ← isDefEq (← inferType e) t then
      g.assign e
      return
  let step (rule : Name) := do
    let subgoals ← g.apply (← mkConstWithFreshMVarLevels rule) {newGoals := .all}
    for goal in subgoals do
      unless ← goal.isAssigned do
        let u ← instantiateMVars (← goal.getType)
        if u.isAppOf ``Exec then solvePath (fuel - 1) edges guard goal
        else if ← isProp u then
          goal.withContext do
            if u.isAppOf ``WordsBounded then
              if !(← goal.assumptionCore) then
                let mut found := false
                for e in edges do
                  let h ← mkAppM ``Exec.wb_right #[e]
                  if ← isDefEq (← inferType h) u then
                    goal.assign h
                    found := true
                    break
                unless found do throwError "ram_path: missing word bound"
            else
              setGoals [goal]
              evalTactic guard
              unless (← getUnsolvedGoals).isEmpty do throwError "ram_path: unresolved guard"
    for goal in subgoals do
      unless ← goal.isAssigned do throwError "ram_path: cannot infer state or cost"
  let branch (yes no : Name) := do
    let saved ← saveState
    try step yes catch _ =>
      saved.restore
      step no
  match (← whnf s).getAppFn.constName? with
  | some ``Stmt.seq => step ``Exec.seq
  | some ``Stmt.skip => step ``Exec.skip
  | some ``Stmt.ifLtN => branch ``Exec.ifLtN_true ``Exec.ifLtN_false
  | some ``Stmt.ifLtR => branch ``Exec.ifLtR_true ``Exec.ifLtR_false
  | some ``Stmt.whileLtN => step ``Exec.whileLtN_false
  | some ``Stmt.whileLtR => step ``Exec.whileLtR_false
  | _ => throwError "ram_path: no local execution of {s}"

elab_rules : tactic
  | `(tactic| ram_path $[[$rs,*]]?) => withMainContext do
    let rs := (rs.map (·.getElems)).getD #[]
    let proof ← `(tactic| first | assumption | omega | ram_state [$rs,*] | linarith)
    let mut edges := #[]
    for d in ← getLCtx do
      unless d.isImplementationDetail do
        if d.type.isAppOf ``Exec then edges := edges.push d.toExpr
    let g ← getMainGoal
    let gs ← getGoals
    solvePath 64 edges proof g
    setGoals (gs.drop 1)

/-- Specialize the word bounds at addresses and registers occurring in the goal.
The addresses need not be literals. -/
elab "word_omega" : tactic => withMainContext do
  let g ← getMainGoal
  let rec reads (e : Expr) (acc : Std.HashSet Expr) : Std.HashSet Expr :=
    let acc := if (e.isAppOfArity ``Config.nreg 2 || e.isAppOfArity ``Config.nmem 2) &&
      !e.hasLooseBVars && !e.hasExprMVar then acc.insert e else acc
    match e with
    | .app f x => reads x (reads f acc)
    | .mdata _ x => reads x acc
    | _ => acc
  let mut rs := reads (← instantiateMVars (← g.getType)) {}
  let mut bounds := #[]
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      if d.type.isAppOf ``WordsBounded then
        bounds := bounds.push (d.type.getArg! 1, d.toExpr)
      else if d.type.isAppOf ``Exec then
        bounds := bounds.push (d.type.getArg! 4, ← mkAppM ``Exec.wb_right #[d.toExpr])
      else if d.type.isAppOf ``Eq then
        rs := reads d.type rs
  let mut hs := #[]
  for (c, hw) in bounds do
    for read in rs.toArray do
      if read.getArg! 0 == c then
        let fld := if read.isAppOf ``Config.nreg then ``And.left else ``And.right
        let v := mkApp (← mkAppM fld #[hw]) (read.getArg! 1)
        hs := hs.push {userName := ← mkFreshUserName `bound, type := ← inferType v, value := v}
  let (_, g) ← g.assertHypotheses hs
  replaceMainGoal [g]
  evalTactic (← `(tactic| omega))

/-- Recover a register frame either from the verified write footprint, or by
chaining local frames and weakening their write masks. -/
syntax "ram_frame" (simpArgs)? : tactic

private def regFrame := `Chazelle.Core.SignK.FrameB
private def memFrame := `Chazelle.Core.BuildRam.FrameM

private structure FrameEdge where
  kind : Name
  args : Array Expr
  src : Expr
  dst : Expr
  cert : Expr

private def readFrameEdge (h : Expr) (type : Expr) : Option FrameEdge := do
  let (kind, args) := type.getAppFnArgs
  if kind == ``Exec then
    return ⟨kind, args, args[3]!, args[4]!, h⟩
  if kind == regFrame || kind == memFrame then
    return ⟨kind, args, args[1]!, args[2]!, h⟩
  none

private def maskUnfolds (masks : List Expr) : MetaM (Array (TSyntax ``simpLemma)) := do
  let env ← getEnv
  let mut rules := #[]
  for e in masks do
    let some n := e.getAppFn.constName? | continue
    unless (`Chazelle.Core).isPrefixOf n do continue
    let some (.defnInfo _) := env.find? n | continue
    if rules.any (fun r => r.raw[2].getId == n) then continue
    let r ← `(simpLemma| $(mkIdent n):ident)
    rules := rules.push r
  return rules

private partial def frameEdges (h : Expr) (depth : Nat) (acc : Array FrameEdge) : MetaM (Array FrameEdge) := do
  if depth == 0 then return acc
  let ty ← inferType h
  if let some e := readFrameEdge h ty then return acc.push e
  if ty.isAppOfArity ``And 2 then
    let acc ← frameEdges (← mkAppM ``And.left #[h]) (depth-1) acc
    frameEdges (← mkAppM ``And.right #[h]) (depth-1) acc
  else return acc

private partial def solveFrame (fuel : Nat) (steps : Array FrameEdge) (check : Syntax)
    (rules : Array Syntax)
    (frameName : Name) (mask src dst : Expr) : TacticM Expr := do
  if fuel == 0 then throwError "ram_frame: chain is too long"
  if ← isDefEq src dst then
    return ← mkAppM (frameName ++ `refl) #[mask, src]
  -- Try a direct certificate before looking for a chain of intermediate states.
  for direct in [true, false] do
    for e in steps.reverse do
      if e.dst != dst && e.dst.isFVar && dst.isFVar then continue
      if (e.src == src) != direct || e.src == e.dst then continue
      unless e.kind == ``Exec || e.kind == frameName || frameName == memFrame do continue
      let saved ← saveState
      try
        unless ← isDefEq e.dst dst do throwError "nonmatching target state"
        let last ← if e.kind == ``Exec then do
          let (wr, rule) := if frameName == regFrame then
              (`Chazelle.Core.SignK.wr, `Chazelle.Core.SignK.exec_frameB)
            else (`Chazelle.Core.BuildRam.wrM, `Chazelle.Core.BuildRam.exec_frameM)
          let target ← mkAppM wr #[mask, e.args[2]!]
          let p ← mkFreshExprSyntheticOpaqueMVar (← mkEq target (mkConst ``Bool.true))
          setGoals [p.mvarId!]
          evalTactic check
          unless (← getUnsolvedGoals).isEmpty do throwError "unverified write footprint"
          mkAppOptM rule #[e.args[0]!, e.args[1]!, mask, e.args[2]!, e.src, dst, e.args[5]!, e.cert, p]
        else do
          let last ← if e.kind == frameName then pure e.cert else
            mkAppM `Chazelle.Core.BuildRam.FrameB.toM #[e.cert]
          if ← isDefEq e.args[0]! mask then pure last else do
            let p ← mkAppOptM (frameName ++ `mono) #[e.args[0]!, mask, e.src, dst, last]
            let u ← whnf (← inferType p)
            let cond ← mkFreshExprSyntheticOpaqueMVar u.bindingDomain!
            setGoals [cond.mvarId!]
            let unfolded ← maskUnfolds [mask, e.args[0]!]
            let names : TSyntaxArray [``simpErase, ``simpLemma] :=
              ((rules.filter (!·.isOfKind ``simpStar)) ++ unfolded.map TSyntax.raw).map (⟨·⟩)
            evalTactic (← `(tactic| solve
              | intro r hr; assumption
              | intro r hr; simp_all [ram_layout, $names,*] <;> omega))
            unless (← getUnsolvedGoals).isEmpty do throwError "unverified mask inclusion"
            pure (mkApp p cond)
        if ← isDefEq e.src src then return last
        let prior ← solveFrame (fuel - 1) (steps.filter (·.dst != dst)) check rules frameName mask src e.src
        return ← mkAppM (frameName ++ `trans) #[prior, last]
      catch _ => saved.restore
  throwError "ram_frame: no verified frame chain"

elab_rules : tactic
  | `(tactic| ram_frame $[[$rs,*]]?) => withMainContext do
    let rs := (rs.map (·.getElems)).getD #[]
    let check ← `(tactic| solve
      | assumption | rfl | decide
      | simp (disch := reg_omega) only [write_check, block, ram_layout, Bool.true_and,
          Bool.and_true, $rs,*])
    let mut steps := #[]
    for d in ← getLCtx do
      steps ← frameEdges d.toExpr 5 steps
    let g ← getMainGoal
    let (kind, #[mask, src, dst]) := (← instantiateMVars (← g.getType)).getAppFnArgs |
      throwError "ram_frame: expected a register frame"
    unless kind == regFrame || kind == memFrame do throwError "ram_frame: expected a register frame"
    let gs ← getGoals
    g.assign (← solveFrame 20 steps check (rs.map TSyntax.raw) kind mask src dst)
    setGoals (gs.drop 1)

end

end Chazelle.Programs
