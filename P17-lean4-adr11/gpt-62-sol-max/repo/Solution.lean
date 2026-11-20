module

public import ADR11.Identifiability.Sampling

/-!
# Solution: the Challenge's theorems, proved from the library

These benchmark results use the shared definitions from `ADR11.Defs`.
-/

@[expose] public section

namespace ADR11.Challenge

open ADR11 Finset Real ADR11.Computation

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The unrooted gene tree probabilities are nonnegative. -/
alias unrootedDist_nonneg := SpeciesTree.unrootedDist_nonneg

/-- The unrooted gene tree probabilities sum to `1`. -/
alias unrootedDist_sum := SpeciesTree.unrootedDist_sum

local notation "trivial₄" => ({{0}, {1}, {2}, {3}, {1, 2, 3}, {0, 2, 3}, {0, 1, 3}, {0, 1, 2}} :
  Finset (Finset (Fin 4)))
local notation "ab_cd" => insert {0, 1} (insert {2, 3} trivial₄)
local notation "ac_bd" => insert {0, 2} (insert {1, 3} trivial₄)
local notation "ad_bc" => insert {0, 3} (insert {1, 2} trivial₄)

local notation "QuartetLaw(" σ ", " x ")" =>
    SpeciesTree.unrootedDist σ id ab_cd = 1 - 2 / 3 * x ∧
    SpeciesTree.unrootedDist σ id ac_bd = 1 / 3 * x ∧ SpeciesTree.unrootedDist σ id ad_bc = 1 / 3 * x

private theorem quartet_probabilities (σ : SpeciesTree (Fin 4)) {x : ℝ}
    (h : quartetScale σ 0 = x ∧ quartetScale σ 1 = 1 ∧ quartetScale σ 2 = 1) : QuartetLaw(σ, x) := by
  rw [← (show quartet 0 = ab_cd by decide), ← (show quartet 1 = ac_bd by decide), ← (show quartet 2 = ad_bc by decide)]
  simp only [quartet_values σ, scaleAvg, h.1, h.2.1, h.2.2]
  ring_nf; simp

/-- Quartet probabilities for a balanced four-taxon species tree. -/
theorem fourTaxa_balanced (σ : SpeciesTree (Fin 4))
    (hσ : σ.clusters = {univ, {0, 1}, {2, 3}, {0}, {1}, {2}, {3}}) :
    QuartetLaw(σ, exp (-(σ.length {0, 1} + σ.length {2, 3}))) := by
  apply quartet_probabilities
  simp (config := {decide := true}) [quartetScale, quartetCode, edgeFactor, hσ, exp_add, mul_comm,
    show decC 4 3 = {0, 1} by decide, show decC 4 12 = {2, 3} by decide]

/-- Quartet probabilities for a rooted caterpillar on four taxa. -/
theorem fourTaxa_caterpillar (σ : SpeciesTree (Fin 4))
    (hσ : σ.clusters = {univ, {0, 1}, {0, 1, 2}, {0}, {1}, {2}, {3}}) :
    QuartetLaw(σ, exp (-σ.length {0, 1})) := by
  apply quartet_probabilities
  simp (config := {decide := true}) [quartetScale, quartetCode, edgeFactor, hσ,
    show decC 4 3 = {0, 1} by decide]

/-- **Theorem 9** (`|X| ≥ 5`): the unrooted topological gene tree distribution arising from the
multispecies coalescent for samples of one lineage per taxon determines the binary metric species
tree. -/
theorem theorem9 (hX : 5 ≤ Fintype.card X) (σ σ' : SpeciesTree X) (_hσ : σ.IsBinary)
    (_hσ' : σ'.IsBinary) (h : σ.unrootedDist id = σ'.unrootedDist id) :
    σ.SameRootedMetricTree σ' := rooted_identifiability hX σ σ' h

/-- **Theorem 9** (`|X| = 4`): the unrooted gene tree distribution determines only the unrooted
metric species tree. -/
theorem theorem9_four (hX : Fintype.card X = 4) (σ σ' : SpeciesTree X) (_hσ : σ.IsBinary)
    (_hσ' : σ'.IsBinary) :
    σ.unrootedDist id = σ'.unrootedDist id ↔ σ.SameUnrootedMetricTree σ' := quartet_identifiability hX σ σ'

/-- **Proposition 3**: for `|X| = 4` taxa, `σ⁻` is identifiable from the unrooted gene tree
distribution, but `σ⁺` is not. -/
theorem proposition3 (hX : Fintype.card X = 4) :
    (∀ σ σ' : SpeciesTree X, σ.IsBinary → σ'.IsBinary →
        σ.unrootedDist id = σ'.unrootedDist id → σ.SameUnrootedMetricTree σ') ∧
      ∃ σ σ' : SpeciesTree X, σ.IsBinary ∧ σ'.IsBinary ∧
        σ.unrootedDist id = σ'.unrootedDist id ∧ ¬ σ.SameRootedMetricTree σ' := ⟨fun σ σ' _ _ => (quartet_identifiability hX σ σ').1, quartet_ambiguity hX⟩

/-- **Corollary 10**: with `ℓ x > 0` lineages `(x, k)`, `k < ℓ x`, sampled from each taxon `x`, if
`|X| ≥ 4` and some `ℓ x ≥ 2`, or `|X| = 3` and two of the `ℓ x` are `≥ 2`, the unrooted gene tree
distribution determines the binary rooted species tree, its internal edge lengths, and the
pendant edge length of every taxon `x` with `ℓ x ≥ 2`. -/
theorem corollary10 (ℓ : X → ℕ) (hℓ : ∀ x, 0 < ℓ x)
    (hcond : (4 ≤ Fintype.card X ∧ ∃ x, 2 ≤ ℓ x) ∨
      (Fintype.card X = 3 ∧ ∃ x y, x ≠ y ∧ 2 ≤ ℓ x ∧ 2 ≤ ℓ y))
    (σ σ' : SpeciesTree X) (_hσ : σ.IsBinary) (_hσ' : σ'.IsBinary)
    (h : σ.unrootedDist (Sigma.fst : (Σ x, Fin (ℓ x)) → X) =
      σ'.unrootedDist Sigma.fst) :
    σ.SameRootedMetricTree σ' ∧ ∀ x, 2 ≤ ℓ x → σ.length {x} = σ'.length {x} := identifiability_of_samples ℓ hℓ hcond σ σ' h

/-- **Proposition 11** (Theorem 9, `|X| ≥ 5`, for species trees that need not be binary). -/
alias proposition11_theorem9 := rooted_identifiability

/-- **Proposition 11** (Theorem 9, `|X| = 4`, for species trees that need not be binary). -/
alias proposition11_theorem9_four := quartet_identifiability

/-- **Proposition 11** (Corollary 10 for species trees that need not be binary). -/
alias proposition11_corollary10 := identifiability_of_samples

end ADR11.Challenge
