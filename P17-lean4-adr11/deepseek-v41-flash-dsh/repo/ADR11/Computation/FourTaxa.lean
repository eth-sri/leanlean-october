module

public import ADR11.Computation.Toolkit

/-!
# Unrooted gene tree distributions of 4-taxon species trees

With one lineage per taxon on `Fin 4`, the unrooted gene trees are the three quartets
`treeOfClusters {{0, 1}}` (`T_{AB|CD}`), `treeOfClusters {{0, 2}}` (`T_{AC|BD}`) and
`treeOfClusters {{0, 3}}` (`T_{AD|BC}`); every other `T` has probability `0`. This file gives the
complete unrooted gene tree distribution, as a function of `T`, of the species trees on `Fin 4`
used in the paper:

* `unrootedDist_bal4`: the balanced tree `((a,b):x,(c,d):y)` (`balanced4`);
* `unrootedDist_cat4_0123`, `_0132`, `_2301`, `_2310`: the caterpillars `(((a,b):x,c):y,d)`
  (`caterpillar4`), `(((a,b):x,d):y,c)`, `(((c,d):x,a):y,b)`, `(((c,d):x,b):y,a)`;
* `unrootedDist_star4`: the unresolved tree `(a,b,c,d)` (`hierarchyOf ∅`);
* `unrootedDist_cherry4`: `((a,b):x,c,d)` (`hierarchyOf {{0, 1}}`);
* `unrootedDist_triple4`: `((a,b,c):y,d)` (`hierarchyOf {{0, 1, 2}}`).

`unrootedDist_eq_quartets` is the general statement behind them: run the engine on a tree shape
and read the three quartet probabilities.
-/

@[expose] public section

namespace ADR11.Computation

open Finset Real

/-- The codes of the unrooted quartet tree with the split `A | Aᶜ`, where `0 ∈ A` and `a` is the
code of `A`. -/
def quartetCode (a : ℕ) : List ℕ := unrootL 4 [1, 2, 4, 8, a, 15]

theorem decF_quartetCode_3 : decF 4 (quartetCode 3) = treeOfClusters {{0, 1}} := by
  decide

theorem decF_quartetCode_5 : decF 4 (quartetCode 5) = treeOfClusters {{0, 2}} := by
  decide

theorem decF_quartetCode_9 : decF 4 (quartetCode 9) = treeOfClusters {{0, 3}} := by
  decide

theorem quartet_ne_01_02 :
    (treeOfClusters {{0, 1}} : Fam4) ≠ treeOfClusters {{0, 2}} := by
  decide

theorem quartet_ne_01_03 :
    (treeOfClusters {{0, 1}} : Fam4) ≠ treeOfClusters {{0, 3}} := by
  decide

theorem quartet_ne_02_03 :
    (treeOfClusters {{0, 2}} : Fam4) ≠ treeOfClusters {{0, 3}} := by
  decide

/-- An unrooted gene tree distribution on `Fin 4` computed by the engine, as a function of the
gene tree. -/
theorem unrootedDist_eq_quartets (σ : ST4) {H : Fam4}
    (hσ : σ.clusters = H) (T : PTree) (hwf : T.wfB 4 H = true) (htop : T.code = 15)
    {P₁ P₂ P₃ : Poly}
    (hc : certAllB 4 (T.unrootedL 4 4 id)
      [(quartetCode 3, P₁), (quartetCode 5, P₂), (quartetCode 9, P₃)] = true)
    (U : Fam4) :
    σ.unrootedDist id U =
      if U = treeOfClusters {{0, 1}} then evalPoly σ.length P₁
      else if U = treeOfClusters {{0, 2}} then evalPoly σ.length P₂
      else if U = treeOfClusters {{0, 3}} then evalPoly σ.length P₃ else 0 :=
  unrootedDist_eq_ite₃ σ hσ T hwf htop hc decF_quartetCode_3 decF_quartetCode_5
    decF_quartetCode_9 quartet_ne_01_02 quartet_ne_01_03 quartet_ne_02_03 U

/-- The balanced species tree `((a,b):x,(c,d):y)`. -/
theorem unrootedDist_bal4 (σ : ST4) (hσ : σ.clusters = balanced4)
    (U : Fam4) :
    σ.unrootedDist id U =
      if U = treeOfClusters {{0, 1}} then
        1 - 2 / 3 * exp (-(σ.length {0, 1} + σ.length {2, 3}))
      else if U = treeOfClusters {{0, 2}} then
        1 / 3 * exp (-(σ.length {0, 1} + σ.length {2, 3}))
      else if U = treeOfClusters {{0, 3}} then
        1 / 3 * exp (-(σ.length {0, 1} + σ.length {2, 3}))
      else 0 := by
  rw [unrootedDist_eq_quartets σ hσ (.node 15 [.node 3 [.leaf 0, .leaf 1], .node 12 [.leaf 2, .leaf 3]])
    (by decide) rfl (P₁ := [(1, []), (-2 / 3, [(3, 1), (12, 1)])])
    (P₂ := [(1 / 3, [(3, 1), (12, 1)])]) (P₃ := [(1 / 3, [(3, 1), (12, 1)])]) (by decide +kernel)]
  have h3 : decC 4 3 = {0, 1} := by decide
  have h12 : decC 4 12 = {2, 3} := by decide
  simp only [evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil, h3, h12, neg_add,
    Real.exp_add]
  push_cast
  split_ifs <;> ring

/-- The caterpillar species tree `(((a,b):x,c):y,d)`. -/
theorem unrootedDist_cat4_0123 (σ : ST4) (hσ : σ.clusters = caterpillar4)
    (U : Fam4) :
    σ.unrootedDist id U =
      if U = treeOfClusters {{0, 1}} then 1 - 2 / 3 * exp (-σ.length {0, 1})
      else if U = treeOfClusters {{0, 2}} then 1 / 3 * exp (-σ.length {0, 1})
      else if U = treeOfClusters {{0, 3}} then 1 / 3 * exp (-σ.length {0, 1})
      else 0 := by
  rw [unrootedDist_eq_quartets σ hσ (.node 15 [.node 7 [.node 3 [.leaf 0, .leaf 1], .leaf 2], .leaf 3])
    (by decide) rfl (P₁ := [(1, []), (-2 / 3, [(3, 1)])]) (P₂ := [(1 / 3, [(3, 1)])])
    (P₃ := [(1 / 3, [(3, 1)])]) (by decide +kernel)]
  have h3 : decC 4 3 = {0, 1} := by decide
  simp only [evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil, h3]
  push_cast
  split_ifs <;> ring

/-- The caterpillar species tree `(((a,b):x,d):y,c)`. -/
theorem unrootedDist_cat4_0132 (σ : ST4)
    (hσ : σ.clusters = hierarchyOf {{0, 1}, {0, 1, 3}}) (U : Fam4) :
    σ.unrootedDist id U =
      if U = treeOfClusters {{0, 1}} then 1 - 2 / 3 * exp (-σ.length {0, 1})
      else if U = treeOfClusters {{0, 2}} then 1 / 3 * exp (-σ.length {0, 1})
      else if U = treeOfClusters {{0, 3}} then 1 / 3 * exp (-σ.length {0, 1})
      else 0 := by
  rw [unrootedDist_eq_quartets σ hσ (.node 15 [.node 11 [.node 3 [.leaf 0, .leaf 1], .leaf 3], .leaf 2])
    (by decide) rfl (P₁ := [(1, []), (-2 / 3, [(3, 1)])]) (P₂ := [(1 / 3, [(3, 1)])])
    (P₃ := [(1 / 3, [(3, 1)])]) (by decide +kernel)]
  have h3 : decC 4 3 = {0, 1} := by decide
  simp only [evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil, h3]
  push_cast
  split_ifs <;> ring

/-- The caterpillar species tree `(((c,d):x,a):y,b)`. -/
theorem unrootedDist_cat4_2301 (σ : ST4)
    (hσ : σ.clusters = hierarchyOf {{2, 3}, {0, 2, 3}}) (U : Fam4) :
    σ.unrootedDist id U =
      if U = treeOfClusters {{0, 1}} then 1 - 2 / 3 * exp (-σ.length {2, 3})
      else if U = treeOfClusters {{0, 2}} then 1 / 3 * exp (-σ.length {2, 3})
      else if U = treeOfClusters {{0, 3}} then 1 / 3 * exp (-σ.length {2, 3})
      else 0 := by
  rw [unrootedDist_eq_quartets σ hσ (.node 15 [.node 13 [.node 12 [.leaf 2, .leaf 3], .leaf 0], .leaf 1])
    (by decide) rfl (P₁ := [(1, []), (-2 / 3, [(12, 1)])]) (P₂ := [(1 / 3, [(12, 1)])])
    (P₃ := [(1 / 3, [(12, 1)])]) (by decide +kernel)]
  have h12 : decC 4 12 = {2, 3} := by decide
  simp only [evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil, h12]
  push_cast
  split_ifs <;> ring

/-- The caterpillar species tree `(((c,d):x,b):y,a)`. -/
theorem unrootedDist_cat4_2310 (σ : ST4)
    (hσ : σ.clusters = hierarchyOf {{2, 3}, {1, 2, 3}}) (U : Fam4) :
    σ.unrootedDist id U =
      if U = treeOfClusters {{0, 1}} then 1 - 2 / 3 * exp (-σ.length {2, 3})
      else if U = treeOfClusters {{0, 2}} then 1 / 3 * exp (-σ.length {2, 3})
      else if U = treeOfClusters {{0, 3}} then 1 / 3 * exp (-σ.length {2, 3})
      else 0 := by
  rw [unrootedDist_eq_quartets σ hσ (.node 15 [.node 14 [.node 12 [.leaf 2, .leaf 3], .leaf 1], .leaf 0])
    (by decide) rfl (P₁ := [(1, []), (-2 / 3, [(12, 1)])]) (P₂ := [(1 / 3, [(12, 1)])])
    (P₃ := [(1 / 3, [(12, 1)])]) (by decide +kernel)]
  have h12 : decC 4 12 = {2, 3} := by decide
  simp only [evalPoly_cons, evalPoly_nil, monoVal_cons, monoVal_nil, h12]
  push_cast
  split_ifs <;> ring

/-! ### Arbitrary labellings

For distinct `a b c d : Fin 4`, the complete unrooted gene tree distributions of the caterpillar
`(((a,b):x,c):y,d)`, the balanced tree `((a,b):x,(c,d):y)`, `((a,b):x,c,d)` and `((a,b,c):y,d)`,
in terms of the quartets `treeOfClusters {{a, b}}`, `treeOfClusters {{a, c}}`,
`treeOfClusters {{a, d}}`. Each is proved for all labellings at once by a kernel computation. -/

end ADR11.Computation
