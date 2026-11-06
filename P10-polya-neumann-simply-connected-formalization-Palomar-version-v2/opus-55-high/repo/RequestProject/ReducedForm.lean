module

public import RequestProject.RankBound
public import RequestProject.FiniteRankCompletion
public import RequestProject.SobolevMultiplier

/-!
# Reduced forms of Section 7 (Lemmas 7.4, 7.5, 7.8 and the chart reduction of Lemma 7.9)

This file formalizes the functional-analytic deductions of Lemmas 7.4–7.9 of the paper
(numbered as in `RankBound.lean`) that sit between the chart of Lemma 7.3 (`exists_fixed_complement`) and the boundary lower bound.
The analytic inputs (the nullspace identities of Lemma 6.12, the pole structure of Lemma 6.5,
the regular part of Lemma 6.7, and the injectivity of Lemma 7.5) are hypotheses here.

Throughout, `H = H₀ ⊕ H₀ᗮ` is a Hilbert space (in the paper `L²(𝕋)` with `H₀` the nonpositive
modes), `J E : H₀ → H` is the normalized conormal transmutation `Ĵ_E`, `R : H₀ᗮ → H` is the
fixed complement and `𝔅_E = J E ∘ Π₀ + R ∘ Π₁` is the chart of Lemma 7.3.

* **Lemma 7.4 (regularity and dimension of the reduction), dimension part**
  (`linearIndependent_adjoint_of_surjective`): if `𝔅_{E₀}` is surjective and `w₁, …, w_m` are linearly independent vectors annihilating `ran Ĵ_{E₀}`, then
  `η_j = R^* w_j` are linearly independent.
* **Lemma 7.4, pole part** (`inner_pole_add_eq_of_orthogonal`): the reduced pole
  `-2/(E-E₀) ∑ η_j ⟨η_j, ·⟩` vanishes identically on `Z = {z : ⟨η_j, z⟩ = 0}`.
* **Lemma 7.5 (injectivity after reduction), last step** (`chart_range_inter_eq_zero`): if
  `𝔅_{E₀}` is injective and `R z ∈ ran Ĵ_{E₀}`, then `z = 0`.
* **Lemma 7.5, Sobolev bootstrap** (`sobolev_bootstrap`): a fixed point of a map gaining `δ`
  derivatives lies in every `H^{nδ}`.
* **Lemma 7.8 (reduced lower bound) on `Z`** (`reduced_lower_bound_subspace`): the coercivity
  argument applied on a closed subspace `Z`.
* **Lemma 7.9, chart reduction** (`chart_reduced_boundary_bound`): from the chart, the nullspace
  identities and the pole structure, `Re ⟨y, P̂_E y⟩ ≥ -A₀ ‖Ŝ_E y‖²` on the kernel of a linear
  map `ℓ_E : H → ℂ^m`, uniformly for `E ≠ E₀` near `E₀`; with the splitting
  `𝒜_E = P̂_E - O_E B_E O_E^*` and `Ŝ_E = Π_E O_E^*` this gives
  `Re ⟨y, 𝒜_E y⟩ ≥ -A₁ ‖O_E^* y‖²` on `ker ℓ_E` (`chart_boundary_lower_bound`).
-/

@[expose] public section

noncomputable section

namespace PolyaNeumann

open InnerProductSpace ContinuousLinearMap Filter Topology Module
open scoped InnerProductSpace

/-! ### Lemma 7.4, dimension part -/

section Dimension

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

end Dimension

/-! ### Lemma 7.4, pole part, and Lemma 7.5 -/

section Pole

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

/-- **Lemma 7.4 (the reduced pole vanishes on `Z`).** If `⟨η_j, z⟩ = 0` for all `j`, then for
every scalar `c` (in the paper `c = -2/(E - E₀)`) and every operator `T`,
`⟨z, (c ∑ η_j ⟨η_j, ·⟩ + T) z⟩ = ⟨z, T z⟩`. -/
theorem inner_pole_add_eq_of_orthogonal {m : ℕ} (η : Fin m → W) (c : ℂ) (T : W →L[ℂ] W)
    (z : W) (hz : ∀ j, ⟪η j, z⟫_ℂ = 0) :
    ⟪z, (c • ∑ j, rankOne ℂ (η j) (η j) + T) z⟫_ℂ = ⟪z, T z⟫_ℂ := by
  simp_all

end Pole

section Chart

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (H₀ : Submodule ℂ H) [H₀.HasOrthogonalProjection]

omit [CompleteSpace H] in
/-- **Lemma 7.5, last step.** If the chart `𝔅 = Ĵ Π₀ + R Π₁` is injective and `R z = Ĵ a`
for some `z ∈ H₀ᗮ`, `a ∈ H₀`, then `z = 0` (and `a = 0`). -/
theorem chart_range_inter_eq_zero (J₀ : H₀ →L[ℂ] H) (R : H₀ᗮ →L[ℂ] H)
    (hinj : Function.Injective (J₀ ∘L H₀.orthogonalProjection + R ∘L H₀ᗮ.orthogonalProjection))
    (a : H₀) (z : H₀ᗮ) (h : R z = J₀ a) : z = 0 ∧ a = 0 := by
  set x : H := z - a with hx
  have hP0 : H₀.orthogonalProjection x = -a := by
    simp_all
  have hP1 : H₀ᗮ.orthogonalProjection x = z := by
    simp_all
  have hBx : (J₀ ∘L H₀.orthogonalProjection + R ∘L H₀ᗮ.orthogonalProjection) x = 0 := by
    grind
  grind

end Chart

/-! ### Lemma 7.5, Sobolev bootstrap -/

/-! ### Lemma 7.8 on a closed subspace -/

section Reduced

variable {W Y : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

omit [CompleteSpace W] in
/-- **Lemma 7.8 (reduced lower bound) on the fixed space `Z`.** Let `Z ⊆ W` be a closed
subspace. Let `E ↦ R_E : W → W` and `E ↦ S_E : W → Y` be operator-norm continuous at `E₀`,
with `R_{E₀} = α I + C` (`α > 0`, `C` compact) and `S_{E₀}` injective on `Z`. Then there is
`A₀ > 0` such that for all `E` near `E₀`, `Re ⟨z, R_E z⟩ ≥ -A₀ ‖S_E z‖²` for every `z ∈ Z`.
(The compression `Π_Z R_{E₀}|_Z` is `α I` plus a compact operator on `Z`.) -/
theorem reduced_lower_bound_subspace (Z : Submodule ℂ W) [CompleteSpace Z] (α : ℝ) (hα : 0 < α)
    (C : W →L[ℂ] W) (hC : IsCompactOperator C) (R : ℝ → W →L[ℂ] W) (S : ℝ → W →L[ℂ] Y)
    (E₀ : ℝ) (hR : ContinuousAt R E₀) (hS : ContinuousAt S E₀)
    (hR₀ : R E₀ = (α : ℂ) • ContinuousLinearMap.id ℂ W + C)
    (hinj : ∀ z ∈ Z, S E₀ z = 0 → z = 0) :
    ∃ A₀ > 0, ∀ᶠ E in 𝓝 E₀, ∀ z ∈ Z, -(A₀ * ‖S E z‖ ^ 2) ≤ (⟪z, R E z⟫_ℂ).re := by
  set ι := Z.subtypeL
  set Pz := Z.orthogonalProjection
  set R' : ℝ → Z →L[ℂ] Z := fun E => Pz ∘L R E ∘L ι with hR'
  set S' : ℝ → Z →L[ℂ] Y := fun E => S E ∘L ι with hS'
  have hPzι : Pz ∘L ι = ContinuousLinearMap.id ℂ Z := by
    ext1 z
    exact Submodule.orthogonalProjection_mem_subspace_eq_self z
  have hR'c : ContinuousAt R' E₀ :=
    continuousAt_const.clm_comp (hR.clm_comp continuousAt_const)
  obtain ⟨A₀, hA₀, hev⟩ := reduced_lower_bound α hα (Pz ∘L C ∘L ι) ((hC.comp_clm ι).clm_comp Pz) R' S' E₀ hR'c (hS.clm_comp continuousAt_const) (by
    simp_all) (by
    intro z₁ z₂ h12
    exact Subtype.ext (sub_eq_zero.1 (hinj _ (Z.sub_mem z₁.2 z₂.2) (by
      rw [map_sub, sub_eq_zero]; assumption))))
  refine ⟨A₀, hA₀, ?_⟩
  filter_upwards [hev] with E hE z hz
  have := hE ⟨z, hz⟩
  have e1 : (⟪⟨z, hz⟩, R' E ⟨z, hz⟩⟫_ℂ) = ⟪z, R E z⟫_ℂ := by
    simp [hR', Pz, ι]
  rwa [e1] at this

end Reduced

/-! ### Lemma 7.9, chart reduction -/

section Boundary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (H₀ : Submodule ℂ H) [H₀.HasOrthogonalProjection]
  {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [CompleteSpace Y]

end Boundary

end PolyaNeumann
