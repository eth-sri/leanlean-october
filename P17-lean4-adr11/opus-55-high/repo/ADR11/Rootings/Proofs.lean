module

public import ADR11.Computation.Toolkit

/-!
# The `msc` tactics

The gene tree distributions of small species trees are computed by the verified engine of
`ADR11.Computation.Engine`. `root_certsB` checks, for several gene trees at once, that their
probabilities are given polynomials `evalPoly τ.length Pᵢ` (comparing polynomials by combining
like terms of their difference, `root_polyEqB`); `msCert` builds the tree shape and the codes from
the clusters. The tactics `msc`, `msc_rw` and `msc_have` compute the polynomials by evaluation,
check them by `decide +kernel`, and turn them into closed forms in the variables
`exp (-τ.length C)`.
-/
@[expose] public section

namespace ADR11

open Finset _root_.ADR11.Computation

/-! ### Comparing polynomials by combining like terms -/

/-- Adds a term to a polynomial, combining it with the term of the same monomial if there is
one. -/
def root_addTerm (t : ℚ × List (ℕ × ℕ)) : List (ℚ × List (ℕ × ℕ)) → List (ℚ × List (ℕ × ℕ))
  | [] => [t]
  | s :: l => if s.2 = t.2 then (s.1 + t.1, s.2) :: l else s :: root_addTerm t l

theorem root_evalPoly_addTerm {n : ℕ} (len : Finset (Fin n) → ℝ) (t : ℚ × List (ℕ × ℕ)) :
    ∀ l, evalPoly len (root_addTerm t l) = t.1 * monoVal len t.2 + evalPoly len l
  | [] => by simp [root_addTerm]
  | s :: l => by
    unfold root_addTerm
    split_ifs with h
    · simp_all <;> grind
    · simp only [evalPoly_cons, root_evalPoly_addTerm len t l]
      ring

/-- The polynomial with like terms combined. -/
def root_normPoly (P : List (ℚ × List (ℕ × ℕ))) : List (ℚ × List (ℕ × ℕ)) :=
  P.foldr root_addTerm []

theorem root_evalPoly_normPoly {n : ℕ} (len : Finset (Fin n) → ℝ) :
    ∀ P, evalPoly len (root_normPoly P) = evalPoly len P
  | [] => rfl
  | t :: P => by
    rw [root_normPoly, List.foldr_cons, ← root_normPoly, root_evalPoly_addTerm,
      root_evalPoly_normPoly len P, evalPoly_cons]

/-- Whether two polynomials are equal: the coefficients of their difference all vanish once like
terms are combined. -/
def root_polyEqB (P Q : List (ℚ × List (ℕ × ℕ))) : Bool :=
  (root_normPoly (P ++ Q.map fun t => (-t.1, t.2))).all fun t => t.1 == 0

theorem root_evalPoly_append {n : ℕ} (len : Finset (Fin n) → ℝ)
    (P Q : List (ℚ × List (ℕ × ℕ))) : evalPoly len (P ++ Q) = evalPoly len P + evalPoly len Q := by
  simp [evalPoly, List.sum_append]

theorem root_evalPoly_neg {n : ℕ} (len : Finset (Fin n) → ℝ) :
    ∀ Q : List (ℚ × List (ℕ × ℕ)), evalPoly len (Q.map fun t => (-t.1, t.2)) = -evalPoly len Q
  | [] => by simp
  | t :: Q => by
    rw [List.map_cons, evalPoly_cons, evalPoly_cons, root_evalPoly_neg len Q]
    push_cast
    ring

theorem root_evalPoly_eq_of_polyEqB {n : ℕ} (len : Finset (Fin n) → ℝ)
    {P Q : List (ℚ × List (ℕ × ℕ))} (h : root_polyEqB P Q = true) :
    evalPoly len P = evalPoly len Q := by
  have h0 : ∀ L : List (ℚ × List (ℕ × ℕ)), (L.all fun t => t.1 == 0) = true →
      evalPoly len L = 0 := by
    intro L hL
    induction L with
    | nil => rfl
    | cons t L ih =>
      simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hL
      rw [evalPoly_cons, hL.1, ih hL.2]
      simp
  have e := h0 _ h
  rw [root_evalPoly_normPoly, root_evalPoly_append, root_evalPoly_neg] at e
  linarith

/-! ### Certificates for several gene trees at once -/

/-- Checks that the computation `R` succeeded with valid codes, and that for each target
`(u, P)` the probability of the family with codes `u` is the polynomial `P`. -/
def root_certsB (m : ℕ) (R : Option (List CTerm))
    (targets : List (List ℕ × List (ℚ × List (ℕ × ℕ)))) : Bool :=
  match R with
  | some M => M.all (fun τ => decide (Valid m τ.forest)) &&
      targets.all fun t => decide (Valid m t.1) && root_polyEqB (collect M t.1) t.2
  | none => false

theorem root_eq_evalPoly_of_certsB {m n : ℕ} (len : Finset (Fin n) → ℝ)
    {R : Option (List CTerm)} {targets : List (List ℕ × List (ℚ × List (ℕ × ℕ)))}
    (h : root_certsB m R targets = true) {t : List ℕ × List (ℚ × List (ℕ × ℕ))}
    (ht : t ∈ targets) :
    ∃ M, R = some M ∧
      (M.map fun τ => if decF m τ.forest = decF m t.1 then τ.val len else 0).sum =
        evalPoly len t.2 := by
  cases R with
  | none => simp [root_certsB] at h
  | some M =>
    simp only [root_certsB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    refine ⟨M, rfl, ?_⟩
    rw [sum_eq_evalPoly_collect len M t.1 h.1 (h.2 t ht).1]
    exact root_evalPoly_eq_of_polyEqB len (h.2 t ht).2

/-- The probability of an unrooted gene tree, from a certificate for several gene trees. -/
theorem root_unrootedDist_eq_evalPoly {n : ℕ} (σ : SpeciesTree (Fin n))
    {H : Finset (Finset (Fin n))} (hσ : σ.clusters = H) (T : PTree) (hwf : T.wfB n H = true)
    (htop : T.code = 2 ^ n - 1) {targets : List (List ℕ × List (ℚ × List (ℕ × ℕ)))}
    (hc : root_certsB n (T.unrootedL n n id) targets = true)
    {t : List ℕ × List (ℚ × List (ℕ × ℕ))} (ht : t ∈ targets) {U : Finset (Finset (Fin n))}
    (hu : decF n t.1 = U) : σ.unrootedDist id U = evalPoly σ.length t.2 := by
  obtain ⟨M, hM, hval⟩ := root_eq_evalPoly_of_certsB σ.length hc ht
  rw [SpeciesTree.unrootedDist_eq_unrootedDistOf, hσ,
    T.unrootedL_spec H σ.length hwf htop M hM U, ← hu, hval]

end ADR11

namespace ADR11.Computation
open Finset Lean Meta Elab Tactic

def codesOf (n : ℕ) (U : Finset (Finset (Fin n))) : List ℕ :=
  (List.range (2 ^ n)).filter fun c => decC n c ∈ U

def shapeOf (n : ℕ) (H : Finset (Finset (Fin n))) : PTree :=
  go n (2 ^ n - 1)
where
  go : ℕ → ℕ → PTree
  | 0, c => .node c []
  | k + 1, c => .node c ((codesOf n (childClusters H (decC n c))).map (go k))

def msCert (n : ℕ) (H : Finset (Finset (Fin n)))
    (ts : List (Finset (Finset (Fin n)) × List (ℚ × List (ℕ × ℕ)))) : Bool :=
  (shapeOf n H).wfB n H && root_certsB n ((shapeOf n H).unrootedL n n id)
    (ts.map fun t => (codesOf n t.1, t.2)) && ts.all fun t => decide (decF n (codesOf n t.1) = t.1)

theorem msCert_spec {n : ℕ} {σ : SpeciesTree (Fin n)} {H} (hσ : σ.clusters = H) {ts}
    (h : msCert n H ts = true) : ts.Forall fun t => σ.unrootedDist id t.1 = evalPoly σ.length t.2 := by
  simp only [msCert, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  refine List.forall_iff_forall_mem.2 fun t ht => root_unrootedDist_eq_evalPoly σ hσ _ h.1.1
    (by cases n <;> rfl) h.1.2 (List.mem_map_of_mem ht) (h.2 t ht)

def msPoly (n : ℕ) (H : Finset (Finset (Fin n))) (U : Finset (Finset (Fin n))) :
    List (ℚ × List (ℕ × ℕ)) :=
  match (shapeOf n H).unrootedL n n id with
  | some M => (root_normPoly (collect M (codesOf n U))).filter (·.1 != 0)
  | none => []

meta unsafe def evalMsPolyImpl (e : Expr) : MetaM (List (ℚ × List (ℕ × ℕ))) :=
  evalExpr (List (ℚ × List (ℕ × ℕ))) (mkApp (mkConst ``List [0]) (mkApp2 (mkConst ``Prod [0, 0])
    (mkConst ``Rat) (mkApp (mkConst ``List [0]) (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``Nat)
    (mkConst ``Nat))))) e

@[implemented_by evalMsPolyImpl]
meta opaque evalMsPoly (e : Expr) : MetaM (List (ℚ × List (ℕ × ℕ)))

meta partial def collectUD (σ e : Expr) (acc : Array Expr) : Array Expr :=
  let acc := if e.isAppOfArity ``ADR11.SpeciesTree.unrootedDist 9 && e.appFn!.appFn!.appArg! == σ &&
    !acc.contains e.appArg! then acc.push e.appArg! else acc
  match e with
  | .app f a => collectUD σ a (collectUD σ f acc)
  | .mdata _ b => collectUD σ b acc
  | .letE _ t v b _ => collectUD σ b (collectUD σ v (collectUD σ t acc))
  | .lam _ t b _ | .forallE _ t b _ => collectUD σ b (collectUD σ t acc)
  | _ => acc

meta def ratStr (q : ℚ) : String := if q.den = 1 then s!"({q.num} : ℚ)" else s!"({q.num} / {q.den} : ℚ)"

meta def polyStr (P : List (ℚ × List (ℕ × ℕ))) : String :=
  "[" ++ ", ".intercalate (P.map fun t => s!"({ratStr t.1}, {t.2})") ++ "]"

meta def numT (k : ℕ) : Term := Syntax.mkNumLit (toString k)

meta def parseT (s : String) : CoreM Term := do
  pure ⟨← ofExcept (Parser.runParserCategory (← getEnv) `term s)⟩

meta def setT (n c : ℕ) : CoreM Term :=
  parseT ("{" ++ ", ".intercalate (((List.range n).filter c.testBit).map toString) ++ "}")

/-- The closed form of a polynomial, in the variables `exp (-σ.length C)`. -/
meta def polyT (σ : Term) (n : ℕ) (P : List (ℚ × List (ℕ × ℕ))) : TermElabM Term := do
  let deg (m : List (ℕ × ℕ)) := (m.map (·.2)).sum
  let P := P.mergeSort fun a b => deg a.2 ≥ deg b.2
  let mut acc : Option Term := none
  for (q, m) in P do
    let neg := decide (q < 0) && acc.isSome
    let q := if neg then -q else q
    let a := numT q.num.natAbs
    let c : Term ← if q.den = 1 then (if q.num < 0 then `(-$a) else pure a)
      else if q.num < 0 then `(-$a / $(numT q.den)) else `($a / $(numT q.den))
    let mut t : Option Term := if q.num.natAbs = 1 && q.den = 1 && !m.isEmpty then none else some c
    for (c, k) in m do
      let x ← `(Real.exp (-ADR11.SpeciesTree.length $σ $(← setT n c)))
      let x ← if k = 1 then pure x else `($x ^ $(numT k))
      t ← match t with | none => pure (some x) | some y => pure (some (← `($y * $x)))
    let t' ← if q = -1 && !m.isEmpty then `(-$(t.get!)) else pure t.get!
    acc ← match acc with
      | none => pure (some t')
      | some s => pure (some (← if neg then `($s - $t') else `($s + $t')))
  match acc with | some t => pure t | none => `(0)

/-- The data of `msc`: the tree `σ` and its number of taxa, and the polynomials of the gene trees
`us` (by default those in the goal). -/
meta def mscData (h : Term) (us : Option (Array Expr)) :
    TacticM (Expr × Nat × Array (Expr × List (ℚ × List (ℕ × ℕ))) × Array Term) := withMainContext do
  let hE ← Term.elabTerm h none
  let some (_, lhs, H) := (← instantiateMVars (← inferType hE)).eq? | throwError "msc: bad hypothesis"
  let σ := lhs.appArg!
  let H ← instantiateMVars H
  let n := (← whnfR (← inferType H)).appArg!.appArg!.appArg!
  let some nv ← (evalNat n).run | throwError "msc: n"
  let us := us.getD (collectUD σ (← instantiateMVars (← getMainTarget)) #[])
  let mut res := #[]
  let mut codes : Array ℕ := #[]
  for U in us do
    let P ← evalMsPoly (mkApp3 (mkConst ``msPoly) n H U)
    for t in P do for ae in t.2 do if !codes.contains ae.1 then codes := codes.push ae.1
    res := res.push (U, P)
  let lems ← codes.mapM fun c => do
    `(show ADR11.Computation.decC $(numT nv) $(numT c) = ($(← setT nv c) : Finset (Fin $(numT nv)))
        by decide +kernel)
  pure (σ, nv, res, lems)

meta def mscCert (h : Term) (res : Array (Expr × List (ℚ × List (ℕ × ℕ)))) : TacticM Term := do
  let ts ← res.mapM fun (U, P) => do
    `(($(← Term.exprToSyntax U), $(⟨← ofExcept (Parser.runParserCategory (← getEnv) `term (polyStr P))⟩)))
  `(msCert_spec $h (ts := [$ts,*]) (by decide +kernel))

/-- `msc h`, for `h : σ.clusters = H`, proves the equations `σ.unrootedDist id U = e` in the goal
(a conjunction), where `e` is a polynomial in the `exp (-σ.length C)`. -/
meta def mscRw (hs : Array Term) (extra : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :
    TacticM Unit := withMainContext do
  evalTactic (← `(tactic| ((try dsimp only); (try simp only [ADR11.u]))))
  let mut lems : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := extra
  for h in hs do
    let (_, _, res, ls) ← mscData h none
    for l in ls do lems := lems.push (← `(Lean.Parser.Tactic.simpLemma| $l:term))
    let hm := mkIdent (Name.mkSimple s!"hmsc{lems.size}")
    lems := lems.push (← `(Lean.Parser.Tactic.simpLemma| $hm:ident))
    evalTactic (← `(tactic| (have $hm := $(← mscCert h res); simp only [List.Forall] at $hm:ident)))
  evalTactic (← `(tactic| (
    simp only [evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil, $lems,*, neg_add, Real.exp_add]
    push_cast)))

syntax "msc" (ppSpace colGt term:max)+ (" with " Lean.Parser.Tactic.simpLemma,*)? : tactic
syntax "msc_rw" (ppSpace colGt term:max)+ (" with " Lean.Parser.Tactic.simpLemma,*)? : tactic

/-- `msc h₁ … hₖ with l₁, …`, for `hᵢ : σᵢ.clusters = Hᵢ`, proves the equations in the goal (a
conjunction) between expressions in the probabilities `σᵢ.unrootedDist id U` of gene trees, by
computing these probabilities as polynomials in the `exp (-σᵢ.length C)`. `msc_rw` only rewrites
the probabilities. -/
elab_rules : tactic
  | `(tactic| msc $hs* $[with $ls,*]?) => do
    mscRw hs (ls.map (·.getElems) |>.getD #[])
    evalTactic (← `(tactic| all_goals (repeat' apply And.intro) <;> first | trivial | ring))
  | `(tactic| msc_rw $hs* $[with $ls,*]?) => mscRw hs (ls.map (·.getElems) |>.getD #[])

/-- `msc_have h`, for `h : σ.clusters = H`, adds the closed forms of the probabilities of the
gene trees `u σ i` (five taxa) or the three quartets (four taxa) to the context. -/
elab "msc_have " h:term : tactic => withMainContext do
  let hE ← Term.elabTerm h none
  let some (_, lhs, _) := (← instantiateMVars (← inferType hE)).eq? | throwError "msc: bad hypothesis"
  let σ := lhs.appArg!
  let some nv ← (evalNat (← whnfR (← inferType σ)).appArg!.appArg!).run | throwError "msc: n"
  let σT ← Term.exprToSyntax σ
  let lhss : Array Term ← if nv = 5 then (List.range 15).toArray.mapM fun i => `(ADR11.u $σT $(numT (i+1)))
    else (List.range 3).toArray.mapM fun j =>
      `(ADR11.SpeciesTree.unrootedDist $σT id (ADR11.treeOfClusters {{0, $(numT (j+1))}}))
  let us ← lhss.mapM fun l => do
    let e ← instantiateMVars (← Term.withSynthesize (Term.elabTerm l none))
    pure (if e.isAppOf ``ADR11.u then mkApp (mkConst ``ADR11.T5) e.appArg! else e.appArg!)
  let (_, _, res, lems) ← mscData h us
  let lems : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ← lems.mapM fun l => `(Lean.Parser.Tactic.simpLemma| $l:term)
  let names := (List.range res.size).toArray.map fun i => mkIdent (Name.mkSimple s!"hmsc{i}")
  let mut tacs : Array (TSyntax `tactic) := #[]
  for i in [0:res.size] do
    let hi := names[i]!
    tacs := tacs.push (← `(tactic| have : $(lhss[i]!) = $(← polyT σT nv res[i]!.2) := Eq.trans $hi
      (by simp only [evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil, $lems,*]; push_cast; ring)))
  evalTactic (← `(tactic| (
    have hmsc := $(← mscCert h res)
    simp only [List.Forall] at hmsc
    obtain ⟨$names,*⟩ := hmsc)))
  for t in tacs do evalTactic t
  evalTactic (← `(tactic| clear $names*))

end ADR11.Computation
