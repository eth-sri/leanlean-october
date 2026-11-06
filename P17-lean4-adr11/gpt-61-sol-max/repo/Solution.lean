module

public import ADR11.Model
public import ADR11.MSC.Marginal
public import ADR11.Trees.Hierarchy
public import ADR11.SmallTrees
public import ADR11.MSC.Relabel
public import ADR11.Trees.Classify
public import ADR11.Coalescent.Absorption
public import ADR11.Identifiability.FourTaxaAnalysis
public import ADR11.Rootings.Proofs
public import ADR11.Trees.RootLocation
public import ADR11.Nonbinary.Proposition11
/-!
# Solution: the Challenge's theorems, proved from the library

Each theorem of `Challenge.lean` is restated verbatim, with the same name, and proved from the
development. The definitions it uses are those of `ADR11.Defs`, of which `Challenge.lean` holds a
verbatim copy.
-/

@[expose] public section

namespace ADR11.Challenge

open ADR11 Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

local notation "Q₄(" a "," b "|" c "," d ")" =>
  {{a, b}, {c, d}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3}, {0, 1, 2}}

alias unrootedDist_nonneg := ADR11.unrootedDist_nonneg

alias unrootedDist_sum := ADR11.unrootedDist_sum

/-- Section 4.1, balanced species tree `((a,b):x,(c,d):y)` on `Fin 4`: the unrooted gene trees
`AB|CD`, `AC|BD`, `AD|BC` (each given by the sides of its splits, trivial ones included) have
probabilities `1 - (2/3)e^{-(x+y)}`, `(1/3)e^{-(x+y)}`, `(1/3)e^{-(x+y)}`. -/
theorem fourTaxa_balanced (σ : SpeciesTree (Fin 4))
    (hσ : σ.clusters = {univ, {0, 1}, {2, 3}, {0}, {1}, {2}, {3}}) :
    σ.unrootedDist id Q₄(0,1|2,3) = 1 - 2 / 3 * exp (-(σ.length {0, 1} + σ.length {2, 3})) ∧
    σ.unrootedDist id Q₄(0,2|1,3) = 1 / 3 * exp (-(σ.length {0, 1} + σ.length {2, 3})) ∧
    σ.unrootedDist id Q₄(0,3|1,2) = 1 / 3 * exp (-(σ.length {0, 1} + σ.length {2, 3})) := by
  convert Q4.dist 1 4 σ (hσ.trans (by decide)) using 4 <;>
    first | decide | simp [Q4.key, Q4.codes, root_decC4_3,
      root_decC4_12, exp_add, mul_comm]

/-- Section 4.1, rooted caterpillar species tree `(((a,b):x,c):y,d)` on `Fin 4`: the unrooted gene
trees `AB|CD`, `AC|BD`, `AD|BC` have probabilities `1 - (2/3)e^{-x}`, `(1/3)e^{-x}`,
`(1/3)e^{-x}`. -/
theorem fourTaxa_caterpillar (σ : SpeciesTree (Fin 4))
    (hσ : σ.clusters = {univ, {0, 1}, {0, 1, 2}, {0}, {1}, {2}, {3}}) :
    σ.unrootedDist id Q₄(0,1|2,3) = 1 - 2 / 3 * exp (-σ.length {0, 1}) ∧
    σ.unrootedDist id Q₄(0,2|1,3) = 1 / 3 * exp (-σ.length {0, 1}) ∧
    σ.unrootedDist id Q₄(0,3|1,2) = 1 / 3 * exp (-σ.length {0, 1}) := by
  convert Q4.dist 1 0 σ (hσ.trans (by decide)) using 4 <;>
    first | decide | simp [Q4.key, Q4.codes, root_decC4_3, mul_comm]

/-- **Theorem 9** (`|X| ≥ 5`): the unrooted topological gene tree distribution arising from the
multispecies coalescent for samples of one lineage per taxon determines the binary metric species
tree. -/
theorem theorem9 (hX : 5 ≤ Fintype.card X) (σ σ' : SpeciesTree X) (hσ : σ.IsBinary)
    (hσ' : σ'.IsBinary) (h : σ.unrootedDist id = σ'.unrootedDist id) :
    σ.SameRootedMetricTree σ' := ADR11.proposition11_theorem9 hX σ σ' h

/-- **Theorem 9** (`|X| = 4`): the unrooted gene tree distribution determines only the unrooted
metric species tree. -/
theorem theorem9_four (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) (hσ : σ.IsBinary)
    (hσ' : σ'.IsBinary) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' := ADR11.unrootedDist_eq_iff_four hX σ σ'

theorem proposition3 (hX : Fintype.card X = 4) :
    (∀ σ σ' : SpeciesTree X, σ.IsBinary → σ'.IsBinary →
        σ.unrootedDist id = σ'.unrootedDist id → σ.SameUnrootedMetricTree σ') ∧
      ∃ σ σ' : SpeciesTree X, σ.IsBinary ∧ σ'.IsBinary ∧
        σ.unrootedDist id = σ'.unrootedDist id ∧ ¬ σ.SameRootedMetricTree σ' := by
  refine ⟨fun σ σ' _ _ => (unrootedDist_eq_iff_four hX σ σ').1, ?_⟩
  let C (x : Fin 4) := hierarchyOf {{0, 1}, {0, 1, x}}
  let mk (H : Family (Fin 4)) (h : IsHierarchy H) : SpeciesTree (Fin 4) :=
    ⟨H, h.1, h.2.1, h.2.2.1, h.2.2.2, fun _ => 1, fun _ _ _ => one_pos⟩
  let σ₁ := mk (C 2) (by decide)
  let σ₂ := mk (C 3) (by decide)
  let e : Fin 4 ≃ X := (Fintype.equivFinOfCardEq hX).symm
  refine ⟨σ₁.relabel e, σ₂.relabel e, ?_, ?_, ?_, ?_⟩
  all_goals try (apply (SpeciesTree.isBinary_relabel_iff _ e).2; unfold SpeciesTree.IsBinary; decide)
  · apply (SpeciesTree.unrootedDist_relabel_eq_iff σ₁ σ₂ e).2
    apply (unrootedDist_eq_iff_four rfl σ₁ σ₂).2
    norm_num [SpeciesTree.SameUnrootedMetricTree, SpeciesTree.unrootedLength,
      σ₁, σ₂, mk, C, sum_const]
    decide
  · exact fun hs => (by decide : C 2 ≠ C 3)
      ((SpeciesTree.sameRootedMetricTree_relabel_iff σ₁ σ₂ e).1 hs).1

/-- **Corollary 10**: with `ℓ x > 0` lineages `(x, k)`, `k < ℓ x`, sampled from each taxon `x`, if
`|X| ≥ 4` and some `ℓ x ≥ 2`, or `|X| = 3` and two of the `ℓ x` are `≥ 2`, the unrooted gene tree
distribution determines the binary rooted species tree, its internal edge lengths, and the
pendant edge length of every taxon `x` with `ℓ x ≥ 2`. -/
theorem corollary10 (ℓ : X → ℕ) (hℓ : ∀ x, 0 < ℓ x)
    (hcond : (4 ≤ Fintype.card X ∧ ∃ x, 2 ≤ ℓ x) ∨
      (Fintype.card X = 3 ∧ ∃ x y, x ≠ y ∧ 2 ≤ ℓ x ∧ 2 ≤ ℓ y))
    (σ σ' : SpeciesTree X) (hσ : σ.IsBinary) (hσ' : σ'.IsBinary)
    (h : σ.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X) =
      σ'.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X)) :
    σ.SameRootedMetricTree σ' ∧ ∀ x, 2 ≤ ℓ x → σ.length {x} = σ'.length {x} := ADR11.proposition11_corollary10 ℓ hℓ hcond σ σ' h

alias proposition11_theorem9 := ADR11.proposition11_theorem9

alias proposition11_theorem9_four := ADR11.unrootedDist_eq_iff_four

alias proposition11_corollary10 := ADR11.proposition11_corollary10

end ADR11.Challenge
