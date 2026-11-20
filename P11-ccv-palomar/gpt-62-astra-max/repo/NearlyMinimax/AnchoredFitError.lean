module

public import NearlyMinimax.AnchoredFit


@[expose] public section

/-! Population projection error derived from the actual normal equations. -/

noncomputable section
open MeasureTheory Set Matrix
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax

section
variable {d ℓ : ℕ} (u : Covariate d) {p g : Covariate d → ℝ} (hpmeas : Measurable p) {a b : ℝ}

include hpmeas in
theorem anchoredVectorMoment_integrable
    (hp : ∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b)
    (hg : ContinuousOn g (unitCube d)) (γ : AnchoredIndex d ℓ) :
    Integrable (fun w => p w * anchoredFeature u w γ * g w) (cubeVolume d) := by
  have hc : ContinuousOn (fun w => anchoredFeature u w γ * g w) (unitCube d) :=
    (((anchoredMonomial_continuous γ).comp (continuous_id.sub continuous_const)).continuousOn).mul hg
  have hpi := (ContinuousOn.integrableOn_compact (μ := volume) (unitCube_isCompact d) hc).bdd_mul hpmeas.aestronglyMeasurable
    (hp.mono (fun w hw => by rw [Real.norm_eq_abs, abs_of_nonneg hw.1]; exact hw.2))
  convert hpi using 1
  · ring
  · rfl

theorem anchoredVectorMoment_sub
    (p g h : Covariate d → ℝ) (hpmeas : Measurable p) {b : ℝ}
    (hp : ∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b)
    (hg : ContinuousOn g (unitCube d)) (hh : ContinuousOn h (unitCube d)) :
    anchoredVectorMoment (ℓ := ℓ) u p (g - h) =
      anchoredVectorMoment u p g - anchoredVectorMoment u p h := by
  ext γ
  change (∫ w, p w * anchoredFeature u w γ * (g w - h w) ∂cubeVolume d) = _
  simp [mul_sub]
  exact integral_sub (anchoredVectorMoment_integrable u hpmeas hp hg γ)
    (anchoredVectorMoment_integrable u hpmeas hp hh γ)

include hpmeas in
theorem anchoredPopulationFit_error_equation (ha : 0 < a)
    (hp : ∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b)
    (hg : ContinuousOn g (unitCube d)) (c : AnchoredIndex d ℓ → ℝ) :
    anchoredDensityGram u p *ᵥ (anchoredPopulationFit u p g - c) =
      anchoredVectorMoment u p (g - anchoredFitPolynomial u c) := by
  rw [Matrix.mulVec_sub, (by have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (anchoredDensityGram_posDef (ℓ := ℓ) u hpmeas ha hp).isUnit; rw [anchoredPopulationFit, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec] : anchoredDensityGram u p *ᵥ anchoredPopulationFit u p g = anchoredVectorMoment u p g),
    anchoredVectorMoment_sub u p g _ hpmeas
      (hp.mono (fun w hw => ⟨ha.le.trans hw.1, hw.2⟩)) hg
      ((by apply continuous_finsetSum; intro γ _; exact ((anchoredMonomial_continuous γ).comp (continuous_id.sub continuous_const)).const_mul _ : Continuous (anchoredFitPolynomial u c))).continuousOn,
    anchoredVectorMoment_polynomial u hpmeas
      (hp.mono (fun w hw => ⟨ha.le.trans hw.1, hw.2⟩))]

end

variable {d ℓ : ℕ}

theorem anchoredDensityGram_solve_norm_bound {u : Covariate d}
    {p : Covariate d → ℝ} (hpmeas : Measurable p) {a b cB : ℝ}
    (ha : 0 < a) (hcB : 0 < cB)
    (hp : ∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b)
    (hB : ∀ c : AnchoredCoefficientSpace d ℓ,
      cB * ‖c‖ ^ 2 ≤ anchoredQuadratic u c)
    {e r : AnchoredIndex d ℓ → ℝ} (her : anchoredDensityGram u p *ᵥ e = r) :
    ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm e‖ ≤
      ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm r‖ / (a * cB) := by
  let E := (EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm e
  let R := (EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm r
  have hq := (anchoredDensityGram_quadratic_bounds u hpmeas ha.le hp e).1
  have hinner : e ⬝ᵥ r ≤ ‖E‖ * ‖R‖ := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm, E, R,
      EuclideanSpace.equiv]
      using real_inner_le_norm E R
  have hcoer : a * cB * ‖E‖ ^ 2 ≤ e ⬝ᵥ r := by
    calc
      _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hB E) ha.le
      _ ≤ _ := by bound
  by_cases he : ‖E‖ = 0
  · rw [he]; positivity
  · have hpos  := lt_of_le_of_ne (norm_nonneg _) (Ne.symm he)
    apply (le_div_iff₀ (mul_pos ha hcB)).2
    nlinarith

/-- A uniform coefficient-error constant derived from density bounds and the
known Gram. The approximation premise is solely a genuine polynomial residual. -/
theorem anchoredPopulationFit_coefficient_error [Nonempty (AnchoredIndex d ℓ)]
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ D : ℝ, 0 < D ∧ ∀ u ∈ unitCube d, ∀ p g,
      Measurable p → (∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b) →
      ContinuousOn g (unitCube d) → ∀ c,
      ∀ R, 0 ≤ R → (∀ w ∈ unitCube d, |g w - anchoredFitPolynomial u c w| ≤ R) →
      ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm (anchoredPopulationFit u p g - c)‖ ≤ D * R := by
  obtain ⟨cB, CB, hcB, hCB, hGram⟩ := anchoredGram_uniform_bounds (d := d) (ℓ := ℓ)
  let root := Real.sqrt (Fintype.card (AnchoredIndex d ℓ)) * b / (a * cB)
  let D := max 1 (root)
  refine ⟨D, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro u hu p g hpmeas hp hg c R hR hres
  have he := anchoredDensityGram_solve_norm_bound hpmeas ha hcB hp
    (fun v => (hGram u hu v).1) (anchoredPopulationFit_error_equation u hpmeas ha hp hg c)
  have hr := anchoredVectorMoment_norm_bound (ℓ := ℓ) hu hb hR (hp.mono (fun w hw => ⟨ha.le.trans hw.1, hw.2⟩)) hres
  apply he.trans
  calc
    _ ≤ _ :=
      div_le_div_of_nonneg_right hr (mul_pos ha hcB).le
    _ = (root) * R := by ring
    _ ≤ _ := by bound

theorem anchoredFitPolynomial_abs_le_distance {u w : Covariate d}
    (hu : u ∈ unitCube d) (hw : w ∈ unitCube d) (c : AnchoredIndex d ℓ → ℝ) :
    |anchoredFitPolynomial u c w| ≤ (Fintype.card (AnchoredIndex d ℓ)) *
      ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm c‖ * euclideanNorm (w - u) := by
  calc
    _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _γ,
        ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm c‖ * euclideanNorm (w - u) := by
      apply Finset.sum_le_sum
      intro γ _
      rw [abs_mul]
      apply mul_le_mul _ (anchoredFeature_abs_le_euclideanNorm hu hw γ)
        (abs_nonneg _) (norm_nonneg _)
      exact PiLp.norm_apply_le ((EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm c) γ
    _ = _ := by simp; ring

theorem anchoredFitPolynomial_sub (u w : Covariate d)
    (c e : AnchoredIndex d ℓ → ℝ) :
    anchoredFitPolynomial u (c - e) w = anchoredFitPolynomial u c w - anchoredFitPolynomial u e w := by
  simp only [anchoredFitPolynomial, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- The coefficient estimate yields the spatial Lipschitz-at-anchor error term
needed by the actual population fit, without an assumed fitted-coefficient bound. -/
theorem anchoredPopulationFit_pointwise_error [Nonempty (AnchoredIndex d ℓ)]
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) :
    ∃ D : ℝ, 0 < D ∧ ∀ u ∈ unitCube d, ∀ p g,
      Measurable p → (∀ᵐ v ∂cubeVolume d, a ≤ p v ∧ p v ≤ b) →
      ContinuousOn g (unitCube d) → ∀ c : AnchoredIndex d ℓ → ℝ,
      ∀ R, 0 ≤ R → (∀ v ∈ unitCube d, |g v - anchoredFitPolynomial u c v| ≤ R) →
      ∀ w ∈ unitCube d,
      |g w - anchoredFitPolynomial u (anchoredPopulationFit (ℓ := ℓ) u p g) w| ≤
        |g w - anchoredFitPolynomial u c w| + D * R * euclideanNorm (w - u) := by
  obtain ⟨D, hD, hfit⟩ := anchoredPopulationFit_coefficient_error (d := d) (ℓ := ℓ) a b ha hb
  let E := max 1 ((Fintype.card (AnchoredIndex d ℓ)) * D)
  refine ⟨E, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro u hu p g hpmeas hp hg c R hR hres w hw
  have hcoeff := hfit u hu p g hpmeas hp hg c R hR hres
  have hnonneg : 0 ≤ euclideanNorm (w - u) := by unfold euclideanNorm; positivity
  have habs : |anchoredFitPolynomial u (anchoredPopulationFit u p g - c) w| ≤
      E * R * euclideanNorm (w - u) := by
    apply (anchoredFitPolynomial_abs_le_distance hu hw (anchoredPopulationFit u p g - c)).trans
    calc
      _ ≤ (Fintype.card (AnchoredIndex d ℓ)) * (D * R) * euclideanNorm (w - u) := by
        gcongr
      _ = ((Fintype.card (AnchoredIndex d ℓ)) * D) * R * euclideanNorm (w - u) := by ring
      _ ≤ _ := by
        bound
  have heq : g w - anchoredFitPolynomial u (anchoredPopulationFit (ℓ := ℓ) u p g) w =
      (g w - anchoredFitPolynomial u c w) -
        anchoredFitPolynomial u (anchoredPopulationFit u p g - c) w := by
    rw [anchoredFitPolynomial_sub]
    ring
  rw [heq]
  exact (abs_sub _ _).trans (add_le_add le_rfl habs)

end NearlyMinimax
