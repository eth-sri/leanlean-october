module

public import ADR11.Computation.Caterpillar5

/-!
# Unrooted gene tree distributions of 5-taxon species trees

The fifteen unrooted gene tree probabilities `u σ i = ℙ_σ(T_i)` (`ADR11.u`, `1 ≤ i ≤ 15`) of the
twelve rooted 5-taxon species tree shapes of the paper, with one lineage per taxon, as
polynomials in the transformed lengths `e^{-x}` of the internal edges, verified by the engine of
`ADR11.Computation.Toolkit` (one certificate per shape):

* `u_bal5`, `u_cat5`, `u_pseudo5`: the balanced tree `(((a,b):x,c):y,(d,e):z)` (`balanced5`),
  the caterpillar `((((a,b):x,c):y,d):z,e)` (`caterpillar5`) and the pseudocaterpillar
  `(((a,b):x,(d,e):y):z,c)` (`pseudocaterpillar5`);
* `u_polytomy5`: the nine nonbinary representatives `P₁, …, P₉` of Table 6 (`polytomy5 k`).

Each states `u σ i = evalPoly σ.length (P i)` for `1 ≤ i ≤ 15`, where `P i` is a list of pairs
(coefficient, monomial) and a monomial is a list of pairs (code of a cluster `A`, exponent `e`)
standing for `(e^{-σ.length A})^e`. The codes are `3 = {0,1}`, `7 = {0,1,2}`, `15 = {0,1,2,3}`,
`24 = {3,4}`, `27 = {0,1,3,4}` (`decC_5_3`, `decC_5_7`, `decC_5_15`, `decC_5_24`, `decC_5_27`).
To get an explicit formula, rewrite with the lemma, then
`simp only [cat5Poly, evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil, decC_5_3, …]`,
`push_cast` and `ring`; for instance `u σ 1` of the caterpillar is
`1 - 2/3 X - 2/3 Y + 1/3 X Y + 1/18 X Y³ + 1/90 X Y³ Z⁶` (equation (12)).

`u_eq_evalPoly_of_certAllB` is the general statement: one certificate gives the fifteen
probabilities of any 5-taxon tree shape. `T5_inj`: the fifteen gene trees `T_i` are distinct.
-/

@[expose] public section

namespace ADR11.Computation

open Finset Real

abbrev k37z6 : Mono := [(3, 1), (7, 3), (15, 6)]
abbrev k3x6 : Mono := [(3, 1), (24, 1), (27, 6)]
abbrev k37c : Mono := [(3, 1), (7, 3), (24, 1)]
abbrev k37b : Mono := [(3, 1), (7, 1), (24, 1)]
abbrev k7c : Mono := [(7, 1), (24, 1)]
abbrev k37 : Mono := [(3, 1), (7, 3)]
abbrev k37a : Mono := [(3, 1), (7, 1)]
abbrev k3c : Mono := [(3, 1), (24, 1)]
abbrev k3 : Mono := [(3, 1)]
abbrev k7 : Mono := [(7, 1)]
abbrev k24 : Mono := [(24, 1)]

/-! ### The fifteen unrooted 5-taxon gene trees -/

/-- The codes of the unrooted 5-taxon tree with the nontrivial splits `B | Bᶜ` and `C | Cᶜ`,
`b` and `c` being the codes of `B` and `C`. -/
def t5Code (b c : ℕ) : List ℕ := unrootL 5 [1, 2, 4, 8, 16, b, c, 31]

/-- The codes of the paper's unrooted gene tree `T_i` (`ADR11.T5 i`). -/
def T5code : ℕ → List ℕ
  | 1 => t5Code 3 7 | 2 => t5Code 3 11 | 3 => t5Code 3 19 | 4 => t5Code 5 7
  | 5 => t5Code 5 13 | 6 => t5Code 5 21 | 7 => t5Code 9 11 | 8 => t5Code 9 13
  | 9 => t5Code 9 25 | 10 => t5Code 17 19 | 11 => t5Code 17 21 | 12 => t5Code 17 25
  | 13 => t5Code 6 7 | 14 => t5Code 10 11 | 15 => t5Code 18 19
  | _ => []

theorem decF_T5code : ∀ i ∈ F15, decF 5 (T5code i) = T5 i := by decide

theorem valid_T5code : ∀ i ∈ F15, Valid 5 (T5code i) := by decide

theorem T5code_sameSet : ∀ i ∈ F15, ∀ j ∈ F15,
    sameSet (T5code i) (T5code j) = true → i = j := by decide

/-- The fifteen unrooted gene trees `T_i` are distinct. -/
theorem T5_inj {i j : ℕ} (hi : i ∈ F15) (hj : j ∈ F15) (h : T5 i = T5 j) : i = j := by
  rw [← decF_T5code i hi, ← decF_T5code j hj,
    decF_eq_iff_sameSet (valid_T5code i hi) (valid_T5code j hj)] at h
  exact T5code_sameSet i hi j hj h

/-- The certificate targets for the fifteen gene trees `T_i`, `P i` giving `u σ i`. -/
def T5targets (P : ℕ → Poly) : List (List ℕ × Poly) :=
  (List.range' 1 15).map fun i => (T5code i, P i)

/-- One certificate gives the fifteen unrooted gene tree probabilities of a 5-taxon species tree:
`u σ i = evalPoly σ.length (P i)` for `1 ≤ i ≤ 15`. The certificate also checks that no other
unrooted gene tree is produced. -/
theorem u_eq_evalPoly_of_certAllB (σ : ST5) {H : Fam5}
    (hσ : σ.clusters = H) (T : PTree) (hwf : T.wfB 5 H = true) (htop : T.code = 31)
    (P : ℕ → Poly)
    (hc : certAllB 5 (T.unrootedL 5 5 id) (T5targets P) = true) {i : ℕ} (hi : i ∈ F15) :
    u σ i = evalPoly σ.length (P i) := by
  have hmem : ∀ j ∈ List.range' 1 15, j ∈ F15 := by
    intro j hj
    rw [List.mem_range'_1] at hj
    rw [mem_Icc]
    omega
  rw [u, unrootedDist_eq_sum_targets σ hσ T hwf htop hc, T5targets, List.map_map]
  rw [show ((fun t : List ℕ × Poly =>
      if decF 5 t.1 = T5 i then evalPoly σ.length t.2 else 0) ∘ fun j => (T5code j, P j)) =
      fun j => if decF 5 (T5code j) = T5 i then evalPoly σ.length (P j) else 0 from rfl]
  have hterm : ∀ j ∈ List.range' 1 15,
      (if decF 5 (T5code j) = T5 i then evalPoly σ.length (P j) else 0) =
        if j = i then evalPoly σ.length (P j) else 0 := by
    intro j hj
    rw [decF_T5code j (hmem j hj)]
    by_cases h : j = i
    · subst h
      simp
    · rw [ite_eq_right (fun h' => h (T5_inj (hmem j hj) hi h')), ite_eq_right h]
  rw [List.map_congr_left hterm, ← List.sum_toFinset _ List.nodup_range', Finset.sum_ite_eq',
    ite_eq_left (List.mem_toFinset.2 (List.mem_range'_1.2 (by rw [mem_Icc] at hi; omega)))]

/-! ### Codes of the clusters -/

theorem decC_5_3 : decC 5 3 = {0, 1} := by decide

theorem decC_5_7 : decC 5 7 = {0, 1, 2} := by decide

theorem decC_5_15 : decC 5 15 = {0, 1, 2, 3} := by decide

theorem decC_5_24 : decC 5 24 = {3, 4} := by decide

theorem decC_5_27 : decC 5 27 = {0, 1, 3, 4} := by decide

/-! ### Tree shapes -/

/-- The tree shape of the balanced tree `(((a,b),c),(d,e))`. -/
def bal5Shape : PTree :=
  .node 31 [.node 7 [.node 3 [.leaf 0, .leaf 1], .leaf 2], .node 24 [.leaf 3, .leaf 4]]

/-- The tree shape of the pseudocaterpillar `(((a,b),(d,e)),c)`. -/
def pseudo5Shape : PTree :=
  .node 31 [.node 27 [.node 3 [.leaf 0, .leaf 1], .node 24 [.leaf 3, .leaf 4]], .leaf 2]

theorem bal5Shape_wfB : bal5Shape.wfB 5 balanced5 = true := by decide

theorem pseudo5Shape_wfB : pseudo5Shape.wfB 5 pseudocaterpillar5 = true := by decide

/-! ### The three binary shapes -/

/-- `u₁, …, u₁₅` for the balanced tree, with `X = e^{-x}` (code `3`), `Y = e^{-y}` (code `7`),
`Z = e^{-z}` (code `24`): equation (11). -/
def bal5Poly : ℕ → Poly
  | 1 => [(1, []), (-2/3, k3), (-2/3, k7c), (1/3, k37b),
      (1/15, k37c)]
  | 2 | 3 => [(1/3, k7c), (-1/6, k37b),
      (-1/10, k37c)]
  | 4 | 13 => [(1/3, k3), (-1/3, k37b),
      (1/15, k37c)]
  | 5 | 6 | 9 | 12 => [(1/6, k37b), (-1/10, k37c)]
  | _ => [(1/15, k37c)]

/-- `u₁, …, u₁₅` for the caterpillar, with `X = e^{-x}` (code `3`), `Y = e^{-y}` (code `7`),
`Z = e^{-z}` (code `15`): equation (12). -/
def cat5Poly : ℕ → Poly
  | 1 => [(1, []), (-2/3, k3), (-2/3, k7), (1/3, k37a),
      (1/18, k37), (1/90, k37z6)]
  | 2 => [(1/3, k7), (-1/6, k37a), (-1/9, k37),
      (1/90, k37z6)]
  | 3 => [(1/3, k7), (-1/6, k37a), (-1/18, k37),
      (-2/45, k37z6)]
  | 4 | 13 => [(1/3, k3), (-1/3, k37a), (1/18, k37),
      (1/90, k37z6)]
  | 5 | 12 => [(1/6, k37a), (-1/9, k37),
      (1/90, k37z6)]
  | 6 | 9 => [(1/6, k37a), (-1/18, k37),
      (-2/45, k37z6)]
  | _ => [(1/18, k37), (1/90, k37z6)]

/-- `u₁, …, u₁₅` for the pseudocaterpillar, with `X = e^{-x}` (code `3`), `Y = e^{-y}`
(code `24`), `Z = e^{-z}` (code `27`): equation (13). -/
def pseudo5Poly : ℕ → Poly
  | 1 => [(1, []), (-2/3, k3), (-2/3, k24), (4/9, k3c),
      (-2/45, k3x6)]
  | 2 | 3 => [(1/3, k24), (-5/18, k3c), (1/90, k3x6)]
  | 4 | 13 => [(1/3, k3), (-5/18, k3c), (1/90, k3x6)]
  | 8 | 11 => [(1/9, k3c), (-2/45, k3x6)]
  | _ => [(1/18, k3c), (1/90, k3x6)]

theorem bal5_cert : certAllB 5 (bal5Shape.unrootedL 5 5 id) (T5targets bal5Poly) = true := by
  decide +kernel

theorem cat5_cert : certAllB 5 (cat5Shape.unrootedL 5 5 id) (T5targets cat5Poly) = true := by
  decide +kernel

theorem pseudo5_cert :
    certAllB 5 (pseudo5Shape.unrootedL 5 5 id) (T5targets pseudo5Poly) = true := by
  decide +kernel

/-- The unrooted gene tree probabilities of the balanced species tree (equation (11)). -/
theorem u_bal5 (σ : ST5) (hσ : σ.clusters = balanced5) {i : ℕ}
    (hi : i ∈ F15) : u σ i = evalPoly σ.length (bal5Poly i) :=
  u_eq_evalPoly_of_certAllB σ hσ bal5Shape bal5Shape_wfB rfl bal5Poly bal5_cert hi

/-- The unrooted gene tree probabilities of the caterpillar species tree (equation (12)). -/
theorem u_cat5 (σ : ST5) (hσ : σ.clusters = caterpillar5) {i : ℕ}
    (hi : i ∈ F15) : u σ i = evalPoly σ.length (cat5Poly i) :=
  u_eq_evalPoly_of_certAllB σ hσ cat5Shape cat5Shape_wfB rfl cat5Poly cat5_cert hi

/-- The unrooted gene tree probabilities of the pseudocaterpillar species tree (equation (13)). -/
theorem u_pseudo5 (σ : ST5) (hσ : σ.clusters = pseudocaterpillar5) {i : ℕ}
    (hi : i ∈ F15) : u σ i = evalPoly σ.length (pseudo5Poly i) :=
  u_eq_evalPoly_of_certAllB σ hσ pseudo5Shape pseudo5Shape_wfB rfl pseudo5Poly pseudo5_cert hi

/-! ### The nine nonbinary shapes (Table 7) -/

end ADR11.Computation
