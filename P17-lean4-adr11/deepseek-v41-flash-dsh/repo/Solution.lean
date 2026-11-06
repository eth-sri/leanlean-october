module

public import ADR11.Model
public import ADR11.FourTaxa
public import ADR11.Identifiability.Theorem9
public import ADR11.Identifiability.Proposition3
public import ADR11.Identifiability.Corollary10
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

/-- The unrooted gene tree probabilities are nonnegative. -/
alias unrootedDist_nonneg := ADR11.unrootedDist_nonneg

/-- The unrooted gene tree probabilities sum to `1`. -/
alias unrootedDist_sum := ADR11.unrootedDist_sum

theorem fourTaxa_balanced (σ : SpeciesTree (Fin 4))
    (hσ : σ.clusters = {univ, {0, 1}, {2, 3}, {0}, {1}, {2}, {3}}) :
    σ.unrootedDist id {{0, 1}, {2, 3}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3},
        {0, 1, 2}} = 1 - 2 / 3 * exp (-(σ.length {0, 1} + σ.length {2, 3})) ∧
    σ.unrootedDist id {{0, 2}, {1, 3}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3},
        {0, 1, 2}} = 1 / 3 * exp (-(σ.length {0, 1} + σ.length {2, 3})) ∧
    σ.unrootedDist id {{0, 3}, {1, 2}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3},
        {0, 1, 2}} = 1 / 3 * exp (-(σ.length {0, 1} + σ.length {2, 3})) := by
  have h4 : (balanced4 : Finset (Finset (Fin 4))) = {univ, {0, 1}, {2, 3}, {0}, {1}, {2}, {3}} := by
    decide
  have t1 : treeOfClusters ({{0, 1}} : Finset (Finset (Fin 4))) =
      {{0, 1}, {2, 3}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3}, {0, 1, 2}} := by decide
  have t2 : treeOfClusters ({{0, 2}} : Finset (Finset (Fin 4))) =
      {{0, 2}, {1, 3}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3}, {0, 1, 2}} := by decide
  have t3 : treeOfClusters ({{0, 3}} : Finset (Finset (Fin 4))) =
      {{0, 3}, {1, 2}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3}, {0, 1, 2}} := by decide
  have := ADR11.fourTaxa_balanced σ (hσ.trans h4.symm)
  rwa [t1, t2, t3] at this


theorem fourTaxa_caterpillar (σ : SpeciesTree (Fin 4))
    (hσ : σ.clusters = {univ, {0, 1}, {0, 1, 2}, {0}, {1}, {2}, {3}}) :
    σ.unrootedDist id {{0, 1}, {2, 3}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3},
        {0, 1, 2}} = 1 - 2 / 3 * exp (-σ.length {0, 1}) ∧
    σ.unrootedDist id {{0, 2}, {1, 3}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3},
        {0, 1, 2}} = 1 / 3 * exp (-σ.length {0, 1}) ∧
    σ.unrootedDist id {{0, 3}, {1, 2}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3},
        {0, 1, 2}} = 1 / 3 * exp (-σ.length {0, 1}) := by
  have h4 : (caterpillar4 : Finset (Finset (Fin 4))) =
      {univ, {0, 1}, {0, 1, 2}, {0}, {1}, {2}, {3}} := by decide
  have t1 : treeOfClusters ({{0, 1}} : Finset (Finset (Fin 4))) =
      {{0, 1}, {2, 3}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3}, {0, 1, 2}} := by decide
  have t2 : treeOfClusters ({{0, 2}} : Finset (Finset (Fin 4))) =
      {{0, 2}, {1, 3}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3}, {0, 1, 2}} := by decide
  have t3 : treeOfClusters ({{0, 3}} : Finset (Finset (Fin 4))) =
      {{0, 3}, {1, 2}, {0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3}, {0, 1, 2}} := by decide
  have := ADR11.fourTaxa_caterpillar σ (hσ.trans h4.symm)
  rwa [t1, t2, t3] at this


/-- **Theorem 9** (`|X| ≥ 5`): the unrooted topological gene tree distribution arising from the
multispecies coalescent for samples of one lineage per taxon determines the binary metric species
tree. -/
alias theorem9 := ADR11.theorem9

/-- **Theorem 9** (`|X| = 4`): the unrooted gene tree distribution determines only the unrooted
metric species tree. -/
alias theorem9_four := ADR11.theorem9_four

/-- **Proposition 3**: for `|X| = 4` taxa, `σ⁻` is identifiable from the unrooted gene tree
distribution, but `σ⁺` is not. -/
alias proposition3 := ADR11.proposition3

/-- **Corollary 10**: with `ℓ x > 0` lineages `(x, k)`, `k < ℓ x`, sampled from each taxon `x`, if
`|X| ≥ 4` and some `ℓ x ≥ 2`, or `|X| = 3` and two of the `ℓ x` are `≥ 2`, the unrooted gene tree
distribution determines the binary rooted species tree, its internal edge lengths, and the
pendant edge length of every taxon `x` with `ℓ x ≥ 2`. -/
alias corollary10 := ADR11.corollary10

/-- **Proposition 11** (Theorem 9, `|X| ≥ 5`, for species trees that need not be binary). -/
alias proposition11_theorem9 := ADR11.proposition11_theorem9

/-- **Proposition 11** (Theorem 9, `|X| = 4`, for species trees that need not be binary). -/
alias proposition11_theorem9_four := ADR11.proposition11_theorem9_four

/-- **Proposition 11** (Corollary 10 for species trees that need not be binary). -/
alias proposition11_corollary10 := ADR11.proposition11_corollary10

end ADR11.Challenge
