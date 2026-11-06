module

public import ADR11.Computation.Toolkit
public import ADR11.Rootings.Support

/-!
# Machinery for the closed forms of `ADR11.Rootings.Statements`

The gene tree distributions of the rootings of the standard unrooted trees are computed by the
verified engine of `ADR11.Computation.Engine`: for a tree shape `T` of the species tree,
`root_u5` (five taxa) and `root_q4` (four taxa) give the probabilities of all the gene trees
`T5 i` (resp. the three quartets) as polynomials `evalPoly τ.length Pᵢ`, from one certificate
`root_certsB … = true` checked by `decide`. The tactic `root_finish` then turns these
polynomials into the closed forms in the variables `exp (-τ.length C)`.

`root_certsB` is a cheaper variant of `ADR11.Computation.certB` for several gene trees at once:
families of clusters are compared through their bitmasks (`root_collect`), and polynomials by
combining like terms of their difference (`root_polyEqB`).
-/
@[expose] public section

namespace ADR11

open Finset _root_.ADR11.Computation

/-! ### Comparing families of clusters by their bitmasks -/

theorem root_famMask_eq_iff (a b : List ℕ) :
    root_famMask a = root_famMask b ↔ sameSet a b = true := by
  rw [root_famMask_eq_iff_sameSet]
  rfl

/-- `collect`, comparing families by their bitmasks. -/
def root_collect (M : List CTerm) (u : List ℕ) : Poly :=
  (M.filter fun τ => root_famMask τ.forest == root_famMask u).map fun τ =>
    (τ.coef, normKey τ.key)

theorem root_collect_eq (M : List CTerm) (u : List ℕ) : root_collect M u = collect M u := by
  unfold root_collect collect
  congr 1
  apply List.filter_congr
  intro τ _
  rw [Bool.eq_iff_iff, beq_iff_eq, root_famMask_eq_iff]

/-! ### Comparing polynomials by combining like terms -/

/-- Adds a term to a polynomial, combining it with the term of the same monomial if there is
one. -/
def root_addTerm (t : Term) : Poly → Poly
  | [] => [t]
  | s :: l => if s.2 = t.2 then (s.1 + t.1, s.2) :: l else s :: root_addTerm t l

theorem root_evalPoly_addTerm {n : ℕ} (len : FinFam n → ℝ) (t : Term) :
    ∀ l, evalPoly len (root_addTerm t l) = t.1 * monoVal len t.2 + evalPoly len l
  | [] => by simp [root_addTerm]
  | s :: l => by
    unfold root_addTerm
    split_ifs with h
    · simp only [evalPoly_cons, h]
      push_cast
      ring
    · simp only [evalPoly_cons, root_evalPoly_addTerm len t l]
      ring

/-- The polynomial with like terms combined. -/
def root_normPoly (P : Poly) : Poly :=
  P.foldr root_addTerm []

theorem root_evalPoly_normPoly {n : ℕ} (len : FinFam n → ℝ) :
    ∀ P, evalPoly len (root_normPoly P) = evalPoly len P
  | [] => rfl
  | t :: P => by
    rw [root_normPoly, List.foldr_cons, ← root_normPoly, root_evalPoly_addTerm,
      root_evalPoly_normPoly len P, evalPoly_cons]

/-- Whether two polynomials are equal: the coefficients of their difference all vanish once like
terms are combined. -/
def root_polyEqB (P Q : Poly) : Bool :=
  (root_normPoly (P ++ Q.map fun t => (-t.1, t.2))).all fun t => t.1 == 0

theorem root_evalPoly_append {n : ℕ} (len : FinFam n → ℝ)
    (P Q : Poly) : evalPoly len (P ++ Q) = evalPoly len P + evalPoly len Q := by
  simp [evalPoly, List.sum_append]

theorem root_evalPoly_neg {n : ℕ} (len : FinFam n → ℝ) :
    ∀ Q : Poly, evalPoly len (Q.map fun t => (-t.1, t.2)) = -evalPoly len Q
  | [] => by simp
  | t :: Q => by
    rw [List.map_cons, evalPoly_cons, evalPoly_cons, root_evalPoly_neg len Q]
    push_cast
    ring

theorem root_evalPoly_eq_of_polyEqB {n : ℕ} (len : FinFam n → ℝ)
    {P Q : Poly} (h : root_polyEqB P Q = true) :
    evalPoly len P = evalPoly len Q := by
  have h0 : ∀ L : Poly, (L.all fun t => t.1 == 0) = true →
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
    (targets : List (List ℕ × Poly)) : Bool :=
  match R with
  | some M => M.all (fun τ => decide (Valid m τ.forest)) &&
      targets.all fun t => decide (Valid m t.1) && root_polyEqB (root_collect M t.1) t.2
  | none => false

theorem root_eq_evalPoly_of_certsB {m n : ℕ} (len : FinFam n → ℝ)
    {R : Option (List CTerm)} {targets : List (List ℕ × Poly)}
    (h : root_certsB m R targets = true) {t : List ℕ × Poly}
    (ht : t ∈ targets) :
    ∃ M, R = some M ∧
      (M.map fun τ => if decF m τ.forest = decF m t.1 then τ.val len else 0).sum =
        evalPoly len t.2 := by
  cases R with
  | none => simp [root_certsB] at h
  | some M =>
    simp only [root_certsB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    refine ⟨M, rfl, ?_⟩
    rw [sum_eq_evalPoly_collect len M t.1 h.1 (h.2 t ht).1, ← root_collect_eq]
    exact root_evalPoly_eq_of_polyEqB len (h.2 t ht).2

/-- The probability of an unrooted gene tree, from a certificate for several gene trees. -/
theorem root_unrootedDist_eq_evalPoly {n : ℕ} (σ : SpeciesTree (Fin n))
    {H : FamN n} (hσ : σ.clusters = H) (T : PTree) (hwf : T.wfB n H = true)
    (htop : T.code = 2 ^ n - 1) {targets : List (List ℕ × Poly)}
    (hc : root_certsB n (T.unrootedL n n id) targets = true)
    {t : List ℕ × Poly} (ht : t ∈ targets) {U : FamN n}
    (hu : decF n t.1 = U) : σ.unrootedDist id U = evalPoly σ.length t.2 := by
  obtain ⟨M, hM, hval⟩ := root_eq_evalPoly_of_certsB σ.length hc ht
  rw [SpeciesTree.unrootedDist_eq_unrootedDistOf, hσ,
    T.unrootedL_spec H σ.length hwf htop M hM U, ← hu, hval]

/-- The fifteen gene tree probabilities `u τ i` of a species tree on `Fin 5` with tree shape `T`,
from one certificate. -/
theorem root_u5 (τ : ST5) {H : Fam5} (hτ : τ.clusters = H)
    (T : PTree) (hwf : T.wfB 5 H = true) (htop : T.code = 31)
    {P₁ P₂ P₃ P₄ P₅ P₆ P₇ P₈ P₉ P₁₀ P₁₁ P₁₂ P₁₃ P₁₄ P₁₅ : Poly}
    (hc : root_certsB 5 (T.unrootedL 5 5 id)
      [(root_T5code 1, P₁), (root_T5code 2, P₂), (root_T5code 3, P₃), (root_T5code 4, P₄),
       (root_T5code 5, P₅), (root_T5code 6, P₆), (root_T5code 7, P₇), (root_T5code 8, P₈),
       (root_T5code 9, P₉), (root_T5code 10, P₁₀), (root_T5code 11, P₁₁),
       (root_T5code 12, P₁₂), (root_T5code 13, P₁₃), (root_T5code 14, P₁₄),
       (root_T5code 15, P₁₅)] = true) :
    u τ 1 = evalPoly τ.length P₁ ∧ u τ 2 = evalPoly τ.length P₂ ∧
    u τ 3 = evalPoly τ.length P₃ ∧ u τ 4 = evalPoly τ.length P₄ ∧
    u τ 5 = evalPoly τ.length P₅ ∧ u τ 6 = evalPoly τ.length P₆ ∧
    u τ 7 = evalPoly τ.length P₇ ∧ u τ 8 = evalPoly τ.length P₈ ∧
    u τ 9 = evalPoly τ.length P₉ ∧ u τ 10 = evalPoly τ.length P₁₀ ∧
    u τ 11 = evalPoly τ.length P₁₁ ∧ u τ 12 = evalPoly τ.length P₁₂ ∧
    u τ 13 = evalPoly τ.length P₁₃ ∧ u τ 14 = evalPoly τ.length P₁₄ ∧
    u τ 15 = evalPoly τ.length P₁₅ := by
  have key : ∀ i ∈ F15, ∀ P, (root_T5code i, P) ∈
      [(root_T5code 1, P₁), (root_T5code 2, P₂), (root_T5code 3, P₃), (root_T5code 4, P₄),
       (root_T5code 5, P₅), (root_T5code 6, P₆), (root_T5code 7, P₇), (root_T5code 8, P₈),
       (root_T5code 9, P₉), (root_T5code 10, P₁₀), (root_T5code 11, P₁₁),
       (root_T5code 12, P₁₂), (root_T5code 13, P₁₃), (root_T5code 14, P₁₄),
       (root_T5code 15, P₁₅)] → u τ i = evalPoly τ.length P :=
    fun i hi P hm => root_unrootedDist_eq_evalPoly τ hτ T hwf htop hc hm (root_decF_T5code hi)
  refine ⟨key 1 (by decide) _ (by simp), key 2 (by decide) _ (by simp),
    key 3 (by decide) _ (by simp), key 4 (by decide) _ (by simp), key 5 (by decide) _ (by simp),
    key 6 (by decide) _ (by simp), key 7 (by decide) _ (by simp), key 8 (by decide) _ (by simp),
    key 9 (by decide) _ (by simp), key 10 (by decide) _ (by simp),
    key 11 (by decide) _ (by simp), key 12 (by decide) _ (by simp),
    key 13 (by decide) _ (by simp), key 14 (by decide) _ (by simp),
    key 15 (by decide) _ (by simp)⟩

theorem root_decC5_3 : decC 5 3 = {0, 1} := by decide
theorem root_decC5_7 : decC 5 7 = {0, 1, 2} := by decide
theorem root_decC5_15 : decC 5 15 = {0, 1, 2, 3} := by decide
theorem root_decC5_23 : decC 5 23 = {0, 1, 2, 4} := by decide
theorem root_decC5_24 : decC 5 24 = {3, 4} := by decide
theorem root_decC5_27 : decC 5 27 = {0, 1, 3, 4} := by decide
theorem root_decC5_28 : decC 5 28 = {2, 3, 4} := by decide
theorem root_decC5_29 : decC 5 29 = {0, 2, 3, 4} := by decide
theorem root_decC5_30 : decC 5 30 = {1, 2, 3, 4} := by decide

/-! ### Four taxa -/

/-- The three quartet probabilities of a species tree on `Fin 4` with tree shape `T`, from one
certificate. -/
theorem root_q4 (τ : ST4) {H : Fam4} (hτ : τ.clusters = H)
    (T : PTree) (hwf : T.wfB 4 H = true) (htop : T.code = 15)
    {P₁ P₂ P₃ : Poly}
    (hc : root_certsB 4 (T.unrootedL 4 4 id)
      [(root_Q4code 3, P₁), (root_Q4code 5, P₂), (root_Q4code 9, P₃)] = true) :
    τ.unrootedDist id (treeOfClusters {{0, 1}}) = evalPoly τ.length P₁ ∧
    τ.unrootedDist id (treeOfClusters {{0, 2}}) = evalPoly τ.length P₂ ∧
    τ.unrootedDist id (treeOfClusters {{0, 3}}) = evalPoly τ.length P₃ :=
  ⟨root_unrootedDist_eq_evalPoly τ hτ T hwf htop hc (t := (root_Q4code 3, P₁))
      List.mem_cons_self root_decF_Q4code_3,
    root_unrootedDist_eq_evalPoly τ hτ T hwf htop hc (t := (root_Q4code 5, P₂))
      (List.mem_cons_of_mem _ List.mem_cons_self) root_decF_Q4code_5,
    root_unrootedDist_eq_evalPoly τ hτ T hwf htop hc (t := (root_Q4code 9, P₃))
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      root_decF_Q4code_9⟩

theorem root_decC4_3 : decC 4 3 = {0, 1} := by decide
theorem root_decC4_12 : decC 4 12 = {2, 3} := by decide

/-! ### Closing the goals -/

/-- Proves a conjunction of equations `p = e`, where `e` is a closed form in the variables
`exp (-τ.length C)` (possibly introduced by `let`), from hypotheses `p = evalPoly τ.length P` in
the context. -/
macro "root_finish" : tactic => `(tactic| (
  try dsimp only
  simp only [*, evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil, root_decC5_3,
    root_decC5_7, root_decC5_15, root_decC5_23, root_decC5_24, root_decC5_27, root_decC5_28,
    root_decC5_29, root_decC5_30, root_decC4_3, root_decC4_12]
  push_cast
  repeat' apply And.intro
  all_goals ring))

/-! ### The closed forms of `ADR11.Rootings.Statements`

The formulas of `ADR11.Rootings.Statements` are the engine's polynomials written in the variables
`e^{-τ.length C}`: both the statements (the closed forms) and the proofs (the engine's
polynomials, which the kernel then checks with `decide`) are computed from the tree shape and the
clusters alone, so `ADR11.Rootings.Statements` contains only `rooting` commands. -/

/-- A set of taxa as `{0, 1, 2}`. -/
def rootSetStr (n : ℕ) (A : FinFam n) : String :=
  "{" ++ String.intercalate ", " ((List.range n).filterMap fun i =>
    if h : i < n then (if (⟨i, h⟩ : Fin n) ∈ A then some (toString i) else none) else none) ++ "}"

/-- The factors of a monomial, smallest clusters first. -/
def rootKeySort (n : ℕ) (key : Mono) : Mono :=
  key.filter (·.2 != 0) |>.mergeSort fun a b =>
    (decC n a.1).card < (decC n b.1).card ||
      ((decC n a.1).card = (decC n b.1).card && a.1 ≤ b.1)

/-- A monomial as `exp (-τ.length {0, 1}) ^ 2 * …`. -/
def rootMonoStr (nm : ℕ → String) (key : Mono) : String :=
  String.intercalate " * " ((rootKeySort 5 key).map fun p =>
    if p.2 = 1 then nm p.1 else nm p.1 ++ " ^ " ++ toString p.2)

/-- A term `c * m`, with `1 * m` and the empty monomial abbreviated. -/
def rootTermStr (nm : ℕ → String) (q : ℚ) (key : Mono) : String :=
  let m := rootMonoStr nm key
  if m = "" then toString q else if q = 1 then m else toString q ++ " * " ++ m

/-- Combines like terms. -/
def rootComb : Poly → Poly
  | [] => []
  | t :: ts => root_addTerm t (rootComb ts)

/-- A monomial's degree. -/
def rootDeg (key : Mono) : ℕ := (key.map (·.2)).sum

/-- A monomial's factors, canonically ordered and as text (for a deterministic sort). -/
def rootKeyCode (n : ℕ) (key : Mono) : String :=
  String.intercalate "," ((rootKeySort n key).map fun p => toString p.1 ++ "^" ++ toString p.2)

/-- Sorts a polynomial by decreasing degree, then canonically. -/
def rootPolySort (n : ℕ) (P : Poly) : Poly :=
  P.mergeSort fun a b =>
    rootDeg b.2 < rootDeg a.2 ||
      (rootDeg a.2 = rootDeg b.2 && decide (rootKeyCode n a.2 ≤ rootKeyCode n b.2))

/-- The polynomial of the `i`-th gene tree on `Fin 5`. -/
def rootPoly5 (T : PTree) (i : ℕ) : Poly :=
  rootPolySort 5 (rootComb (root_collect ((T.unrootedL 5 5 id).getD []) (root_T5code i)))

/-- The polynomial of the `i`-th quartet on `Fin 4`. -/
def rootPoly4 (T : PTree) (i : ℕ) : Poly :=
  rootPolySort 4 (rootComb (root_collect ((T.unrootedL 4 4 id).getD []) (root_Q4code i)))

/-- A polynomial with nonzero coefficients as a closed form in `e^{-τ.length C}`. -/
def rootPolyStr (nm : ℕ → String) (P : Poly) : String :=
  match P.filter (·.1 != 0) with
  | [] => "0"
  | (q, key) :: ts =>
    rootTermStr nm q key ++ String.join (ts.map fun s =>
      if s.1 < 0 then " - " ++ rootTermStr nm (-s.1) s.2
      else " + " ++ rootTermStr nm s.1 s.2)

/-- The variable `exp (-τ.length C)` of the cluster with code `c`. -/
def rootExpVar (v : String) (n : ℕ) (c : ℕ) : String :=
  "exp (-" ++ v ++ ".length " ++ rootSetStr n (decC n c) ++ ")"

/-- The fifteen probabilities of a 5-taxon tree as a conjunction of closed forms. -/
def rootStmt5v (v : String) (nm : ℕ → String) (P : ℕ → Poly) : String :=
  String.intercalate " ∧ " ((List.range 15).map fun i =>
    "u " ++ v ++ " " ++ toString (i + 1) ++ " = " ++ rootPolyStr nm (P (i + 1)))

/-- An `if`-chain giving the `i`-th polynomial of `P` in the variables `nm`. -/
def rootChainStr (nm : ℕ → String) (P : ℕ → Poly) : String :=
  (List.range 15).foldr (fun k acc =>
    "if i = " ++ toString (k + 1) ++ " then " ++ rootPolyStr nm (P (k + 1)) ++ " else " ++ acc) "0"

/-- The polynomials of the fifteen gene trees on `Fin 5`, as text. -/
def rootPs5 (T : PTree) : List String :=
  (List.range 15).map fun i => toString (rootPoly5 T (i + 1))

/-- The polynomials of the three quartets on `Fin 4`, as text. -/
def rootPs4 (T : PTree) : List String :=
  (List.range 3).map fun i => toString (rootPoly4 T ([3, 5, 9].getD i 0))

/-- The statement of `rootingDist5_k_j`: the fifteen probabilities of a tree shape `T`. -/
def rootStmt5 (T : PTree) : String :=
  rootStmt5v "τ" (rootExpVar "τ" 5) (rootPoly5 T)

/-- The statement of `rootingDist4_1_j`: the three quartet probabilities of a tree shape `T`. -/
def rootStmt4 (T : PTree) : String :=
  String.intercalate " ∧ " ((List.range 3).map fun i =>
    let a := [3, 5, 9].getD i 0
    "τ.unrootedDist id (treeOfClusters {" ++ rootSetStr 4 (decC 4 a) ++ "}) = "
      ++ rootPolyStr (rootExpVar "τ" 4) (rootPoly4 T a))

/-! ### Filling in the polynomials by computation

The polynomials `Pᵢ` that `root_u5` and `root_q4` certify are the engine's own computation, so
they need not be written out by hand: the tactics `root_at5` and `root_at4` run the engine at
elaboration time and pass the result to `root_u5` (resp. `root_q4`), which the kernel then checks
with `decide`, and close the goal with `root_finish`. -/

open Lean Elab Tactic Meta Parser in
elab "root_at5" tt:term:max hyp:term:max tree:term : tactic => unsafe do
  let ps ← evalExpr (List String) (mkApp (mkConst ``List [.zero]) (mkConst ``String []))
    (mkApp (mkConst ``rootPs5) (← elabTerm tree (some (.const ``PTree []))))
  let ts ← ps.mapM fun s => do
    match runParserCategory (← getEnv) `term s with
    | .ok stx => pure ⟨stx⟩
    | .error e => throwError "root_at: {e}"
  match ts with
  | [p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15] =>
    evalTactic (← `(tactic| obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
        h15⟩ := root_u5 $tt $hyp $tree (by decide +kernel) rfl (by decide +kernel)
          (P₁ := $p1) (P₂ := $p2) (P₃ := $p3) (P₄ := $p4) (P₅ := $p5) (P₆ := $p6) (P₇ := $p7)
          (P₈ := $p8) (P₉ := $p9) (P₁₀ := $p10) (P₁₁ := $p11) (P₁₂ := $p12) (P₁₃ := $p13)
          (P₁₄ := $p14) (P₁₅ := $p15)))
    evalTactic (← `(tactic| root_finish))
  | _ => throwError "root_at5: expected fifteen polynomials"

open Lean Elab Tactic Meta Parser in
elab "root_at4" tt:term:max hyp:term:max tree:term : tactic => unsafe do
  let ps ← evalExpr (List String) (mkApp (mkConst ``List [.zero]) (mkConst ``String []))
    (mkApp (mkConst ``rootPs4) (← elabTerm tree (some (.const ``PTree []))))
  let ts ← ps.mapM fun s => do
    match runParserCategory (← getEnv) `term s with
    | .ok stx => pure ⟨stx⟩
    | .error e => throwError "root_at: {e}"
  match ts with
  | [p1, p2, p3] =>
    evalTactic (← `(tactic| obtain ⟨h1, h2, h3⟩ := root_q4 $tt $hyp $tree (by decide +kernel) rfl
      (by decide +kernel) (P₁ := $p1) (P₂ := $p2) (P₃ := $p3)))
    evalTactic (← `(tactic| root_finish))
  | _ => throwError "root_at4: expected three polynomials"

open Lean Elab Command Term Meta Parser in
/-- Generates a theorem of `ADR11.Rootings.Statements` (with its statement and its proof) from the
number of taxa, the tree shape and the clusters. -/
elab "rooting" tk:num nm:ident cl:term:max tr:term : command => unsafe do
  let n := if tk.getNat = 4 then 4 else 5
  let treeE ← liftTermElabM do
    instantiateMVars (← elabTerm tr (some (.const ``PTree [])))
  let stmt ← liftTermElabM do
    evalExpr String (mkConst ``String [])
      (mkApp (mkConst (if n = 4 then ``rootStmt4 else ``rootStmt5)) treeE)
  let .ok stx0 := runParserCategory (← getEnv) `term stmt | throwError "rooting: bad statement"
  let stx : TSyntax `term := ⟨stx0⟩
  let iτ : Ident := mkIdent `τ
  let ih : Ident := mkIdent `hτ
  let cmd ← if n = 4 then
    `(command| theorem $nm ($iτ : ST4) ($ih : SpeciesTree.clusters $iτ = hierarchyOf
        $cl) : $stx := by root_at4 $iτ $ih $tr)
  else
    `(command| theorem $nm ($iτ : ST5) ($ih : SpeciesTree.clusters $iτ = hierarchyOf
        $cl) : $stx := by root_at5 $iτ $ih $tr)
  elabCommand cmd

end ADR11
