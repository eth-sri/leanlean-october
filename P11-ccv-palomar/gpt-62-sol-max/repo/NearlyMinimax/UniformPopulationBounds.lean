module

public import NearlyMinimax.PopulationPairBounds
public import NearlyMinimax.UniformPilotDerivatives


@[expose] public section

/-! Uniform extension-domain constants for the actual population upper proof.
Numerical witnesses are chosen before the open domain; no extension theorem
or fixed-domain admissibility transfer is assumed. -/
noncomputable section
open MeasureTheory Set Matrix
open scoped BigOperators RealInnerProductSpace Matrix.Norms.L2Operator
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

section
variable {d : ℕ} (C : ModelConstants d)

/-- The same normalized Gram estimate applies to any polynomial comparator, including zero. -/
private theorem uniform_dyadic_fit_coefficients [Nonempty (AnchoredIndex d C.order)] :
    ∃ D : ℝ, 0 < D ∧ UniformOnExtensions C fun _ θ =>
      ∀ x ∈ unitCube d, ∀ j (c : AnchoredIndex d C.order → ℝ) (R : ℝ), 0 ≤ R →
      (∀ w ∈ unitCube d, |dyadicRegressionDifference θ j x w -
        anchoredFitPolynomial (dyadicNormalizedAnchor j x) c w| ≤ R) →
      ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (dyadicPopulationFit θ j x - c)‖ ≤ D * R := by
  obtain ⟨D, hD, hfit⟩ := anchoredPopulationFit_coefficient_error (d := d) (ℓ := C.order)
    C.densityLower C.densityUpper C.densityLower_pos (by linarith [C.one_lt_densityUpper])
  refine ⟨D, hD, ?_⟩
  intro Udom θ hθ x hx j c R hR herr
  rw [dyadicPopulationFit_eq_normalized (C.withDomain Udom) θ hθ]
  exact hfit _ (gridNormalizedAnchor_mem_cube _ (by positivity) x hx) _ _
    (dyadicNormalizedDensity_measurable (C.withDomain Udom) θ hθ j x)
    (dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ j x)
    (dyadicRegressionDifference_continuousOn (C.withDomain Udom) θ hθ j x) c R hR herr

local notation "taylorConstant" => (d : ℝ) ^ C.order * (2 * C.holderBound) / C.order.factorial

section
variable [Nonempty (AnchoredIndex d C.order)]

private theorem uniform_dyadic_taylor_bounds :
    ∃ D : ℝ, 0 < D ∧ UniformOnExtensions C fun _ θ =>
      ∀ x ∈ unitCube d, ∃ c : AnchoredIndex d C.order → ℝ, ∀ j : ℕ,
      ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm
        (dyadicPopulationFit θ j x - dyadicTaylorCoefficients c j)‖ ≤ D * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness ∧
      (∀ w ∈ unitCube d, |dyadicRegressionDifference θ j x w -
        anchoredFitPolynomial (dyadicNormalizedAnchor j x) (dyadicTaylorCoefficients c j) w| ≤
        taylorConstant * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness *
          euclideanNorm (w - dyadicNormalizedAnchor j x) ^ C.smoothness) := by
  obtain ⟨D, hD, hfit⟩ := uniform_dyadic_fit_coefficients C
  have hT := taylorErrorFactor_pos C
  have hH := C.holderBound_pos
  refine ⟨D * (taylorErrorFactor C * C.holderBound), by positivity, ?_⟩
  intro Udom θ hθ x hx
  obtain ⟨c, hc⟩ := admissible_dyadic_taylor_family (C.withDomain Udom) θ hθ x hx
  refine ⟨c, fun j => ⟨?_, fun w hw => (hc j w hw).2⟩⟩
  rw [mul_assoc]
  exact hfit Udom θ hθ x hx j _ _ (by positivity) (fun w hw => (hc j w hw).1)

theorem uniform_domain_admissible_dyadicPopulationFit_spatial_error :
    ∃ E : ℝ, 0 < E ∧ UniformOnExtensions C fun _ θ =>
      ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ w ∈ unitCube d,
      |dyadicRegressionDifference θ j x w - anchoredFitPolynomial (dyadicNormalizedAnchor j x)
        (dyadicPopulationFit (ℓ := C.order) θ j x) w| ≤
          E * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness * euclideanNorm (w - dyadicNormalizedAnchor j x) := by
  obtain ⟨D, hD, hfit⟩ := uniform_dyadic_taylor_bounds C
  let K := taylorConstant * max 1 ((Real.sqrt (d : ℝ)) ^ C.smoothness) + Fintype.card (AnchoredIndex d C.order) * D
  refine ⟨max 1 K, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro Udom θ hθ j x hx w hw
  obtain ⟨c, hc⟩ := hfit Udom θ hθ x hx
  let u := dyadicNormalizedAnchor j x
  have hu : u ∈ unitCube d := gridNormalizedAnchor_mem_cube _ (by positivity) x hx
  have hs : 1 ≤ C.smoothness := by
    obtain ⟨γ⟩ := (inferInstance : Nonempty (AnchoredIndex d C.order))
    exact (show (1 : ℝ) ≤ C.order by exact_mod_cast γ.property.1.trans_le γ.property.2).trans C.order_lt.le
  have hrad : euclideanNorm (w - u) ≤ Real.sqrt (d : ℝ) := by
    simpa using euclideanNorm_le_coordinate_radius (w - u) 1 zero_le_one (unitCube_coord_sub_abs_le_one hw hu)
  have hnorm : 0 ≤ euclideanNorm (w - u) := by unfold euclideanNorm; positivity
  have hholder := C.holderBound_pos
  apply (anchoredFitPolynomial_residual_le u w hu hw _ (dyadicTaylorCoefficients c j) _).trans
  apply (add_le_add ((hc j).2 w hw)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hc j).1 (Nat.cast_nonneg _)) hnorm)).trans
  have hpow := bounded_rpow_le_linear _ _ _ hnorm hrad hs
  calc
    _ ≤ (taylorConstant * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness) *
        (max 1 ((Real.sqrt (d : ℝ)) ^ C.smoothness) * euclideanNorm (w - u)) +
      (Fintype.card (AnchoredIndex d C.order) : ℝ) * (D * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness) * euclideanNorm (w - u) := by
      gcongr
    _ = K * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness * euclideanNorm (w - u) := by dsimp [K]; ring
    _ ≤ _ := by gcongr; exact le_max_right _ _

theorem uniform_domain_admissible_dyadicPopulationIncrement_successor_bound :
    ∃ E : ℝ, 0 < E ∧ UniformOnExtensions C fun _ θ =>
      ∀ x ∈ unitCube d, ∀ j : ℕ,
      ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (dyadicPopulationIncrement θ x (j + 1))‖ ≤
        E * (((2 : ℝ) ^ (j + 1))⁻¹) ^ C.smoothness := by
  obtain ⟨D, hD, hcoeff⟩ := uniform_dyadic_taylor_bounds C
  let E := D * (1 + (1 / 2) * (2 : ℝ) ^ C.smoothness)
  refine ⟨E, mul_pos hD (by positivity), ?_⟩
  intro Udom θ hθ x hx j
  obtain ⟨c, hc⟩ := hcoeff Udom θ hθ x hx
  let e := fun i => dyadicPopulationFit θ i x - dyadicTaylorCoefficients c i
  rw [dyadicPopulationIncrement_error_identity θ x c j]
  have hsub : ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm
      (e (j + 1) - anchoredTransport d C.order *ᵥ e j)‖ ≤
      ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (e (j + 1))‖ +
      ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (anchoredTransport d C.order *ᵥ e j)‖ := by
    simpa [EuclideanSpace.equiv] using norm_sub_le
      ((EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (e (j + 1)))
      ((EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (anchoredTransport d C.order *ᵥ e j))
  apply hsub.trans
  have ht := anchoredTransport_euclidean_norm (e j)
  have ht' := ht.trans (mul_le_mul_of_nonneg_left (hc j).1 (by norm_num : (0 : ℝ) ≤ 1 / 2))
  apply (add_le_add (hc (j + 1)).1 ht').trans_eq
  rw [dyadic_inverse_scale_succ j, Real.mul_rpow (by norm_num) (by positivity)]
  ring

theorem uniform_domain_admissible_dyadicPopulationIncrement_root_bound :
    ∃ E : ℝ, 0 < E ∧ UniformOnExtensions C fun _ θ =>
      ∀ x ∈ unitCube d,
      ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (dyadicPopulationIncrement θ x 0)‖ ≤ E := by
  obtain ⟨D, hD, hfit⟩ := uniform_dyadic_fit_coefficients C
  let E := max 1 (D * (2 * C.holderBound))
  refine ⟨E, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro Udom θ hθ x hx
  have hres : ∀ w ∈ unitCube d, |dyadicRegressionDifference θ 0 x w -
      anchoredFitPolynomial (dyadicNormalizedAnchor 0 x) (0 : AnchoredIndex d C.order → ℝ) w| ≤
        2 * C.holderBound := by
    intro w hw
    simp only [anchoredFitPolynomial, Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero]
    exact (abs_sub _ _).trans (by
      have ha := admissible_regression_value_bound (C.withDomain Udom) θ hθ _ (dyadicCellAffine_mem_cube 0 x w hw)
      have hb := admissible_regression_value_bound (C.withDomain Udom) θ hθ x hx
      change |θ.regression (dyadicCellAffine 0 x w)| + |θ.regression x| ≤ _
      dsimp [ModelConstants.withDomain] at ha hb
      linarith)
  have h := hfit Udom θ hθ x hx 0 0 (2 * C.holderBound)
    (mul_nonneg (by norm_num) C.holderBound_pos.le) hres
  change ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (dyadicPopulationFit θ 0 x)‖ ≤ E
  simpa only [sub_zero] using h.trans (le_max_right 1 _)


theorem uniform_domain_admissible_dyadicPopulationIncrement_bound :
    ∃ E : ℝ, 0 < E ∧ UniformOnExtensions C fun _ θ =>
      ∀ x ∈ unitCube d, ∀ j : ℕ,
      ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (dyadicPopulationIncrement θ x j)‖ ≤
        E * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness := by
  obtain ⟨E0, hE0, hroot⟩ := uniform_domain_admissible_dyadicPopulationIncrement_root_bound C
  obtain ⟨E1, hE1, hsucc⟩ := uniform_domain_admissible_dyadicPopulationIncrement_successor_bound C
  refine ⟨max E0 E1, hE0.trans_le (le_max_left _ _), ?_⟩
  intro Udom θ hθ x hx j
  cases j with
  | zero => simpa using (hroot Udom θ hθ x hx).trans (le_max_left E0 E1)
  | succ j =>
    exact (hsucc Udom θ hθ x hx j).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _))

theorem uniform_domain_admissible_dyadicPopulationFit_physical_error :
    ∃ E : ℝ, 0 < E ∧ UniformOnExtensions C fun _ θ =>
      ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d, y ∈ dyadicPilotCell j x →
      |θ.regression y - θ.regression x - dyadicAnchoredFeature j x y ⬝ᵥ dyadicPopulationFit (ℓ := C.order) θ j x| ≤
        E * euclideanNorm (y - x) * (((2 : ℝ) ^ j)⁻¹) ^ (C.smoothness - 1) := by
  obtain ⟨E, hE, hfit⟩ := uniform_domain_admissible_dyadicPopulationFit_spatial_error C
  refine ⟨E, hE, ?_⟩
  intro Udom θ hθ j x hx y hy hcell
  have hw : dyadicNormalizedAnchor j y ∈ unitCube d := gridNormalizedAnchor_mem_cube _ (by positivity) y hy
  have he := dyadicCellAffine_same_cell j x y hcell
  have h := hfit Udom θ hθ j x hx _ hw
  rw [dyadicPopulationFit_physical_evaluation j x y hcell] at h
  unfold dyadicRegressionDifference at h
  rw [he] at h
  apply h.trans_eq
  have hd := dyadicCellAffine_euclidean_distance j x (dyadicNormalizedAnchor j y)
  rw [he] at hd
  rw [mul_assoc, positive_rpow_times_distance _ _ _ (by positivity), ← hd]
  ring


theorem uniform_domain_admissible_dyadic_increment_polynomial_error :
    ∃ E : ℝ, 0 < E ∧ UniformOnExtensions C fun _ θ =>
      ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ m : ℕ,
      ‖(EuclideanSpace.equiv (Fin (anchoredDimension d C.order)) ℝ).symm
        (dyadicPopulationPolynomial C θ j x (θ.regression x) m -
          anchoredFinVector (dyadicPopulationIncrement θ x j))‖ ≤
        E * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness * dyadicPolynomialDecay C m := by
  obtain ⟨χ, hχ, hcond⟩ := anchoredFinSimilarityUnit_uniform_condition (d := d) (ℓ := C.order)
  obtain ⟨D, hD, hinc⟩ := uniform_domain_admissible_dyadicPopulationIncrement_bound C
  let E₀ := χ ^ 2 * C.densityUpper ^ (anchoredDimension d C.order + 1) *
    parentInverseErrorConstant C.densityLower C.densityUpper (anchoredDimension d C.order)
  have hab := C.densityLower_lt_one.trans C.one_lt_densityUpper
  have hb := zero_lt_one.trans C.one_lt_densityUpper
  have hE₀ : 0 < E₀ := by
    dsimp [E₀]
    have := parentInverseErrorConstant_pos C.densityLower C.densityUpper C.densityLower_pos hab
      (anchoredDimension d C.order)
    positivity
  refine ⟨E₀ * D, mul_pos hE₀ hD, ?_⟩
  intro Udom θ hθ j x hx m
  let u := dyadicNormalizedAnchor j x
  let v := dyadicNormalizedAnchor (j - 1) x
  let p := dyadicNormalizedDensity θ j x
  let q := dyadicParent (fun _ => 1) (fun i => dyadicNormalizedDensity θ i x) j
  let U := dyadicFinPilotMoments (ℓ := C.order) θ j x
  let V := dyadicParent 0 (fun i => dyadicFinPilotMoments (ℓ := C.order) θ i x) j
  have hactual : (anchoredFinNormalizedGram (ℓ := C.order) u p)⁻¹ *ᵥ
      (U false - θ.regression x • U true) - anchoredFinTransport d C.order *ᵥ
        ((anchoredFinNormalizedGram v q)⁻¹ *ᵥ (V false - θ.regression x • V true)) =
        anchoredFinVector (dyadicPopulationIncrement θ x j) := by
    rw [anchoredFinNormalizedGram_dyadicParent (C.withDomain Udom) θ hθ j x,
      ← dyadicFinPilotGram_eq_normalized (C.withDomain Udom) θ hθ j x]
    exact dyadicFinite_increment_eq_actual (C.withDomain Udom) θ hθ j x hx
  have hsmall := hinc Udom θ hθ x hx j
  rw [← anchoredFinVector_norm, ← hactual] at hsmall
  have he := anchoredNormalized_increment_error u v p q
    (dyadicNormalizedDensity_measurable (C.withDomain Udom) θ hθ j x)
    (dyadicParentDensity_measurable (C.withDomain Udom) θ hθ j x)
    C.densityLower C.densityUpper χ (D * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness)
    C.densityLower_pos hab
    (dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ j x)
    (dyadicParentDensity_bounds (C.withDomain Udom) θ hθ j x)
    (hcond u (gridNormalizedAnchor_mem_cube _ (by positivity) x hx))
    U V (θ.regression x) (anchoredFinTransport d C.order) hsmall m
  rw [hactual, exteriorTau_sqrt_ratio _ _ C.densityLower_pos hab] at he
  unfold dyadicPopulationPolynomial dyadicPolynomialDecay paperTau
  rw [dyadicIncrementRawMean_eq_with_virtual_parent (C.withDomain Udom) θ hθ j x hx]
  change ‖_‖ ≤ _
  rw [incrementFinVector_eval_population]
  convert he using 1
  dsimp [E₀]
  ring

theorem uniform_domain_admissible_dyadic_polynomial_row_error :
    ∃ E : ℝ, 0 < E ∧ UniformOnExtensions C fun _ θ =>
      ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d, y ∈ dyadicPilotCell j x → ∀ m : ℕ,
      |dyadicPilotRow j x y ⬝ᵥ dyadicPopulationPolynomial C θ j x (θ.regression x) m -
        dyadicAnchoredFeature j x y ⬝ᵥ dyadicPopulationIncrement (ℓ := C.order) θ x j| ≤
      E * euclideanNorm (y - x) * ((((2 : ℝ) ^ j)⁻¹) ^ (C.smoothness - 1) * dyadicPolynomialDecay C m) := by
  obtain ⟨B, hB, herror⟩ := uniform_domain_admissible_dyadic_increment_polynomial_error C
  have hdim : 0 < (anchoredDimension d C.order : ℝ) := by exact_mod_cast Fintype.card_pos
  refine ⟨B * anchoredDimension d C.order, mul_pos hB hdim, ?_⟩
  intro Udom θ hθ j x hx y hy hcell m
  rw [← dyadicPilotRow_dot_coefficients, ← dotProduct_sub]
  apply (finite_row_abs_dot_le_euclidean_norm _ _).trans
  have hr := dyadicPilotRow_sum_abs_le_distance (ℓ := C.order) j x y hx hy hcell
  have hd : 0 ≤ euclideanNorm (y - x) := by unfold euclideanNorm; positivity
  calc
    _ ≤ ((anchoredDimension d C.order : ℝ) * (2 : ℝ) ^ j * euclideanNorm (y - x)) *
        (B * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness * dyadicPolynomialDecay C m) := by
      gcongr
      exact herror Udom θ hθ j x hx m
    _ = _ := by rw [← dyadic_scale_rpow_cancel]; ring

end

theorem uniform_domain_admissible_dyadicPopulationResidual_bound
    (hs : 1 < C.smoothness) :
    ∃ E : ℝ, 0 < E ∧ UniformOnExtensions C fun _ θ =>
      ∀ J : ℕ, ∀ m : ℕ → ℕ, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d,
      y ∈ dyadicPilotCell J x →
        |dyadicPopulationResidual C θ J m x y| ≤
          E * euclideanNorm (y - x) * dyadicPopulationBiasBudget C J m := by
  let := anchoredIndex_nonempty_of_one_lt_smoothness C hs
  obtain ⟨A, hA, hfit⟩ := uniform_domain_admissible_dyadicPopulationFit_physical_error C
  obtain ⟨B, hB, hpoly⟩ := uniform_domain_admissible_dyadic_polynomial_row_error C
  let E := max A B
  refine ⟨E, hA.trans_le (le_max_left _ _), ?_⟩
  intro Udom θ hθ J m x hx y hy hcell
  have hd : 0 ≤ euclideanNorm (y - x) := by unfold euclideanNorm; positivity
  have heq : dyadicPopulationResidual C θ J m x y =
      (θ.regression y - θ.regression x - dyadicAnchoredFeature J x y ⬝ᵥ dyadicPopulationFit (ℓ := C.order) θ J x) +
      ∑ j ∈ Finset.range (J + 1), (dyadicAnchoredFeature j x y ⬝ᵥ dyadicPopulationIncrement (ℓ := C.order) θ x j -
        dyadicPilotRow j x y ⬝ᵥ dyadicPopulationPolynomial C θ j x (θ.regression x) (m j)) := by
    rw [dyadicPopulationIncrement_telescope, Finset.sum_sub_distrib]
    unfold dyadicPopulationResidual
    ring
  rw [heq, dyadicPopulationBiasBudget, mul_add, Finset.mul_sum]
  apply (abs_add_le _ _).trans
  refine add_le_add ((hfit Udom θ hθ J x hx y hy hcell).trans ?_)
    ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_))
  · gcongr
    exact le_max_left _ _
  · intro j hj
    rw [abs_sub_comm]
    apply (hpoly Udom θ hθ j x hx y hy
      (dyadicPilotCell_subset_coarser j J (by simpa using hj) x hcell) (m j)).trans
    have := dyadicPolynomialDecay_nonneg C (m j)
    gcongr
    exact le_max_right _ _

section
variable (hs : 1 < C.smoothness)
include hs

theorem uniform_domain_admissible_dyadicPopulationRawPolynomial_uniform_bound :
    ∃ B : ℝ, 0 < B ∧ UniformOnExtensions C fun _ θ =>
      ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ t : Bool, ∀ m : ℕ,
        ‖dyadicPopulationRawPolynomial C θ j x t m‖ ≤ B := by
  let := anchoredIndex_nonempty_of_one_lt_smoothness C hs
  obtain ⟨B, A, hB, _, hder⟩ := uniform_domain_dyadic_increment_vector_derivative_bound C 1 zero_le_one
  refine ⟨2 * B, mul_pos (by norm_num) hB, ?_⟩
  intro Udom θ hθ j x hx t m
  have hb (y : ℝ) (hy : |y| ≤ 1) : ‖dyadicPopulationPolynomial C θ j x y m‖ ≤ B := by
    simpa [dyadicPopulationPolynomial] using hder Udom θ hθ j x hx y hy m 0 Fin.elim0
  have h0 := hb 0 (by norm_num)
  have h1 := hb 1 (by norm_num)
  have he0 : dyadicPopulationRawPolynomial C θ j x false m = dyadicPopulationPolynomial C θ j x 0 m := by
    rw [dyadicPopulationPolynomial_affine, zero_smul, sub_zero]
  cases t
  · grind
  · have he : dyadicPopulationRawPolynomial C θ j x true m =
        dyadicPopulationPolynomial C θ j x 0 m - dyadicPopulationPolynomial C θ j x 1 m := by
      simp [dyadicPopulationPolynomial_affine]
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith)

theorem uniform_domain_admissible_dyadicPopulationPilotSum_uniform_bound :
    ∃ R : ℝ, 0 ≤ R ∧ UniformOnExtensions C fun _ θ =>
      ∀ J : ℕ, ∀ m : ℕ → ℕ, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d,
      y ∈ dyadicPilotCell J x → ∀ t : Bool, |dyadicPopulationPilotSum C θ J m t (x, y)| ≤ R := by
  obtain ⟨B, hB, hb⟩ := uniform_domain_admissible_dyadicPopulationRawPolynomial_uniform_bound C hs
  let R := (2 * (anchoredDimension d C.order : ℝ) * Real.sqrt (d : ℝ)) * B
  refine ⟨R, by dsimp [R]; positivity, ?_⟩
  intro Udom θ hθ J m x hx y hy hcell t
  unfold dyadicPopulationPilotSum
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ j ∈ Finset.range (J + 1), (∑ i, |dyadicPilotRow (ℓ := C.order) j x y i|) * B := by
      apply Finset.sum_le_sum
      intro j hj
      exact (finite_row_abs_dot_le_pi_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hb Udom θ hθ j x hx t (m j)) (Finset.sum_nonneg (fun _ _ => abs_nonneg _)))
    _ = (∑ j ∈ Finset.range (J + 1), ∑ i, |dyadicPilotRow (ℓ := C.order) j x y i|) * B := by
      rw [Finset.sum_mul]
    _ ≤ R := mul_le_mul_of_nonneg_right (dyadicPilotRow_total_abs_le J x y hx hy hcell) hB.le

theorem uniform_domain_admissible_dyadicPopulationCoefficients_uniform_bound :
    ∃ Cp : ℝ, 0 < Cp ∧ UniformOnExtensions C fun _ θ =>
      ∀ J : ℕ, ∀ m : ℕ → ℕ, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d,
      y ∈ dyadicPilotCell J x → ‖dyadicPopulationCoefficients C θ J m (x, y)‖ ≤ Cp := by
  obtain ⟨R, hR, hb⟩ := uniform_domain_admissible_dyadicPopulationPilotSum_uniform_bound C hs
  refine ⟨Real.sqrt 3 * (1 + R), mul_pos (by positivity) (by positivity), ?_⟩
  intro Udom θ hθ J m x hx y hy hc
  have ht := hb Udom θ hθ J m x hx y hy hc true
  have hf := hb Udom θ hθ J m x hx y hy hc false
  have hcoord (i : Fin 3) : |dyadicPopulationCoefficients C θ J m (x, y) i| ≤ 1 + R := by
    fin_cases i
    · simpa [dyadicPopulationCoefficients] using hR
    · exact (abs_add_le _ _).trans (by simpa using add_le_add_left ht 1)
    · change |-dyadicPopulationPilotSum C θ J m false (x, y)| ≤ 1 + R
      grind
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  calc
    (∑ i : Fin 3, ‖dyadicPopulationCoefficients C θ J m (x, y) i‖ ^ 2) ≤ ∑ _i : Fin 3, (1 + R) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [Real.norm_eq_abs] using hcoord i) 2
    _ = 3 * (1 + R) ^ 2 := by simp
    _ = (Real.sqrt 3 * (1 + R)) ^ 2 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]

end

end

end NearlyMinimax
