module

public import ADR11.MSC.Contract
public import ADR11.Introduction
public import ADR11.FourTaxa

/-!
# Section 5: nonbinary species trees

The paper obtains the probabilities of binary gene trees under a nonbinary species tree as the
limits of the formulas for binary species trees, as one or more branch lengths go to `0`
(l.697–699).

* `section5_limit`: the distributions of a nonbinary species tree are limits of those of a binary
  resolution as the added branch lengths tend to `0`. Hence (`lim_rootedDist_eq`,
  `lim_unrootedDist_eq`) a formula for the gene tree probabilities of the binary resolution,
  continuous in the added lengths, gives those of the nonbinary tree with the added lengths set
  to `0`.
* `section5_threeTaxa`: for the unresolved 3-taxon species tree the three rooted gene trees are
  equiprobable: letting `t → 0` in equation (1) for `((a,b):t,c)` gives `1/3` each
  (`lim_threeTaxa_unresolved`). For a resolved one exactly one has probability greater than `1/3`
  (equation (1)).
* `section5_triples`, `section5_proposition1`, `section5_corollary2` are in
  `ADR11.Nonbinary.Triples`.
* `section5_fourTaxa`: `(a,b,c,d)` and `((a,b,c):y,d)` give the same unrooted distribution, and so
  do `(((a,b):x,c):y,d)` and `((a,b):x,c,d)`, with `ℙ(T_{AB|CD}) = 1 - (2/3) e^{-x}`. The three
  nonbinary trees are limits of the caterpillar `(((a,b):x,c):y,d)` of Section 4.1, as `y → 0`,
  `x → 0`, or both (`lim_fourTaxa_quartets`).
-/

@[expose] public section

namespace ADR11

open Finset Real

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Limits of the formulas for binary species trees -/

/-- Section 5: the gene tree probabilities of a nonbinary species tree are the limits of those of a
binary resolution `H` of it as the lengths of the added edges tend to `0`. -/
theorem section5_limit (σ : SpeciesTree X) {H : Finset (Finset X)} (hH : IsHierarchy H)
    (hsub : σ.clusters ⊆ H) (T : Finset (Finset X)) :
    Filter.Tendsto
      (fun ε : ℝ => unrootedDistOf H (fun A => if A ∈ σ.clusters then σ.length A else ε) id T)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (σ.unrootedDist id T)) :=
  -- the distribution is continuous in `ε`, and at `ε = 0` the added edges contract
  (σ.tendsto_unrootedDistOf hH hsub id T).mono_left nhdsWithin_le_nhds

/-- For `ε > 0`, the species tree with the clusters of a hierarchy `H`, the lengths of `σ` on the
clusters of `σ` and the length `ε` on the other clusters. -/
theorem lim_exists_resolution (σ : SpeciesTree X) {H : Finset (Finset X)} (hH : IsHierarchy H)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : SpeciesTree X, τ.clusters = H ∧
      τ.length = fun A => if A ∈ σ.clusters then σ.length A else ε :=
  ⟨{ clusters := H
     univ_mem := hH.1
     singleton_mem := hH.2.1
     nonempty_of_mem := hH.2.2.1
     laminar := hH.2.2.2
     length := fun A => if A ∈ σ.clusters then σ.length A else ε
     length_pos := fun A _ hA => by
       split_ifs with h
       exacts [σ.length_pos A h hA, hε] }, rfl, rfl⟩

/-- The lengths of `σ` on its edges and `ε` on the added edges depend continuously on `ε`. -/
theorem lim_continuous_length (σ : SpeciesTree X) (A : Finset X) :
    Continuous fun ε : ℝ => if A ∈ σ.clusters then σ.length A else ε :=
  continuous_if_const _ (fun _ => continuous_const) fun _ => continuous_id

/-- **The formulas for a binary resolution, with the added lengths set to `0`**, for unrooted gene
trees: as `lim_rootedDist_eq`, with `section5_limit`. -/
theorem lim_unrootedDist_eq (σ : SpeciesTree X) {H : Finset (Finset X)} (hH : IsHierarchy H)
    (hsub : σ.clusters ⊆ H) (T : Finset (Finset X)) (φ : (Finset X → ℝ) → ℝ)
    (hφ : ∀ τ : SpeciesTree X, τ.clusters = H → τ.unrootedDist id T = φ τ.length)
    (hcont : ContinuousAt (fun ε : ℝ => φ fun A => if A ∈ σ.clusters then σ.length A else ε) 0) :
    σ.unrootedDist id T = φ fun A => if A ∈ σ.clusters then σ.length A else 0 := by
  refine tendsto_nhds_unique_of_eventuallyEq (section5_limit σ hH hsub T)
    (hcont.tendsto.mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => ?_)
  -- for `ε > 0` the formula applies to the species tree with the length `ε` on the added edges
  obtain ⟨τ, hτ, hlen⟩ := lim_exists_resolution σ hH hε
  dsimp only
  rw [← hlen, ← hφ τ hτ, ← hτ]
  rfl

/-! ### Three taxa -/

/-! ### Four taxa -/

/-- **Four taxa as limits of the caterpillar** (l.709–711). The species trees `((a,b):x,c,d)`,
`((a,b,c):y,d)` and `(a,b,c,d)` are the limits of the caterpillar `(((a,b):x,c):y,d)` as `y → 0`,
`x → 0`, or both. So their quartet probabilities are those of Section 4.1 for the caterpillar,
`1 - (2/3) e^{-x}`, `(1/3) e^{-x}`, `(1/3) e^{-x}`, which do not depend on `y`, with `x = 0` when
the edge above `{a, b}` is contracted. -/
theorem lim_fourTaxa_quartets (σ : SpeciesTree (Fin 4)) (hσ : σ.clusters ⊆ caterpillar4) :
    σ.unrootedDist id (treeOfClusters {{0, 1}}) =
        1 - 2 / 3 * exp (-if ({0, 1} : Finset (Fin 4)) ∈ σ.clusters then σ.length {0, 1} else 0) ∧
      σ.unrootedDist id (treeOfClusters {{0, 2}}) =
        1 / 3 * exp (-if ({0, 1} : Finset (Fin 4)) ∈ σ.clusters then σ.length {0, 1} else 0) ∧
      σ.unrootedDist id (treeOfClusters {{0, 3}}) =
        1 / 3 * exp (-if ({0, 1} : Finset (Fin 4)) ∈ σ.clusters then σ.length {0, 1} else 0) := by
  have hH : IsHierarchy caterpillar4 := ⟨by decide, by decide, by decide, by decide⟩
  -- `e^{-x}` is continuous in the length `x`
  have hc : Continuous fun ε : ℝ =>
      exp (-if ({0, 1} : Finset (Fin 4)) ∈ σ.clusters then σ.length {0, 1} else ε) :=
    (lim_continuous_length σ {0, 1}).neg.rexp
  exact ⟨lim_unrootedDist_eq σ hH hσ _ (fun ℓ => 1 - 2 / 3 * exp (-ℓ {0, 1}))
      (fun τ hτ => (fourTaxa_caterpillar τ hτ).1)
      (continuous_const.sub (continuous_const.mul hc)).continuousAt,
    lim_unrootedDist_eq σ hH hσ _ (fun ℓ => 1 / 3 * exp (-ℓ {0, 1}))
      (fun τ hτ => (fourTaxa_caterpillar τ hτ).2.1) (continuous_const.mul hc).continuousAt,
    lim_unrootedDist_eq σ hH hσ _ (fun ℓ => 1 / 3 * exp (-ℓ {0, 1}))
      (fun τ hτ => (fourTaxa_caterpillar τ hτ).2.2) (continuous_const.mul hc).continuousAt⟩

end ADR11
