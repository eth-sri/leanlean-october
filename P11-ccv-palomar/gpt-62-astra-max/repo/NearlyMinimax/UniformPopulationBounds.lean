module

public import NearlyMinimax.UniformPilotDerivatives

public import NearlyMinimax.PopulationPairBounds


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
variable {d : ℕ} (C : ModelConstants d) [Nonempty (AnchoredIndex d C.order)]

theorem uniform_domain_admissible_dyadicPopulationFit_taylor_coefficients :
    ∃ D : ℝ, 0 < D ∧ ∀ Udom, ∀ θ, Admissible (C.withDomain Udom) θ →
      ∀ x ∈ unitCube d, ∃ c : AnchoredIndex d C.order → ℝ, ∀ j,
      ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm
        (dyadicPopulationFit θ j x - dyadicTaylorCoefficients c j)‖ ≤
          D * ((2 ^ j)⁻¹) ^ C.smoothness := by
  obtain ⟨D, hD, hfit⟩ := anchoredPopulationFit_coefficient_error (d := d) (ℓ := C.order)
    C.densityLower C.densityUpper C.densityLower_pos (by linarith [C.one_lt_densityUpper])
  refine ⟨(max 1 (D * (taylorErrorFactor C * C.holderBound))), zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro Udom θ hθ x hx
  obtain ⟨c, hc⟩ := admissible_dyadic_taylor_family hθ hx
  refine ⟨c, ?_⟩
  intro j
  rw [dyadicPopulationFit_eq_normalized hθ]
  have h := hfit _ (gridNormalizedAnchor_mem_cube _ (by positivity) hx)
    _ _ (dyadicNormalizedDensity_measurable hθ j x) (dyadicNormalizedDensity_bounds hθ j x)
    (dyadicRegressionDifference_continuousOn hθ j x) (dyadicTaylorCoefficients c j)
    (taylorErrorFactor C * C.holderBound * ((2 ^ j)⁻¹) ^ C.smoothness) (mul_nonneg (mul_nonneg (taylorErrorFactor_pos C).le C.holderBound_pos.le) (by positivity)) (fun w hw => (hc j w hw).1)
  apply h.trans
  calc
    _ = (D * (taylorErrorFactor C * C.holderBound)) * ((2 ^ j)⁻¹) ^ C.smoothness := by ring
    _ ≤ _ :=
      by bound


theorem uniform_domain_admissible_dyadicPopulationFit_spatial_error :
    ∃ E : ℝ, 0 < E ∧ ∀ Udom, ∀ θ, Admissible (C.withDomain Udom) θ →
      ∀ j, ∀ x ∈ unitCube d, ∀ w ∈ unitCube d,
      |dyadicRegressionDifference θ j x w - anchoredFitPolynomial (dyadicNormalizedAnchor j x)
        (dyadicPopulationFit (ℓ := C.order) θ j x) w| ≤
          E * ((2 ^ j)⁻¹) ^ C.smoothness * euclideanNorm (w - dyadicNormalizedAnchor j x) := by
  obtain ⟨D, hD, hpoint⟩ := anchoredPopulationFit_pointwise_error (d := d) (ℓ := C.order)
    C.densityLower C.densityUpper C.densityLower_pos (by linarith [C.one_lt_densityUpper])
  let T := d ^ C.order * (2 * C.holderBound) / C.order.factorial
  have hT : 0 ≤ T := div_nonneg (mul_nonneg (by positivity)
    (mul_nonneg (by norm_num) C.holderBound_pos.le)) (Nat.cast_nonneg _)
  let scale := T * max 1 ((Real.sqrt d) ^ C.smoothness) + D * (taylorErrorFactor C * C.holderBound)
  let E := max 1 (scale)
  refine ⟨E, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro Udom θ hθ j x hx w hw
  obtain ⟨c, hc⟩ := admissible_dyadic_taylor_family hθ hx
  let R := taylorErrorFactor C * C.holderBound * ((2 ^ j)⁻¹) ^ C.smoothness
  have hu : dyadicNormalizedAnchor j x ∈ unitCube d := gridNormalizedAnchor_mem_cube _ (by positivity) hx
  have hp := hpoint _ hu _ _ (dyadicNormalizedDensity_measurable hθ j x) (dyadicNormalizedDensity_bounds hθ j x) (dyadicRegressionDifference_continuousOn hθ j x) _ R (mul_nonneg (mul_nonneg (taylorErrorFactor_pos C).le C.holderBound_pos.le) (by positivity)) (fun v hv => (hc j v hv).1) w hw
  rw [dyadicPopulationFit_eq_normalized hθ]
  apply hp.trans
  have hrad : euclideanNorm (w - dyadicNormalizedAnchor j x) ≤ Real.sqrt d := by
    have h := euclideanNorm_le_coordinate_radius (x := (w - dyadicNormalizedAnchor j x)) (h := 1) (by norm_num)
      (fun i => by
        change |w i - dyadicNormalizedAnchor j x i| ≤ 1
        exact abs_le.mpr ⟨by linarith [(hw i).1, (hu i).2], by linarith [(hw i).2, (hu i).1]⟩)
    bound
  have hs : 1 ≤ C.smoothness := by
    obtain ⟨γ⟩ := (inferInstance : Nonempty (AnchoredIndex d C.order))
    have ho  := γ.property.1.trans_le γ.property.2
    have hor : (1 : ℝ) ≤ C.order := by exact_mod_cast ho
    exact hor.trans C.order_lt.le
  have hr0 : 0 ≤ euclideanNorm (w - dyadicNormalizedAnchor j x) := by unfold euclideanNorm; positivity
  have hpow := bounded_rpow_le_linear hr0 hrad hs
  calc
    _ ≤ T * ((2 ^ j)⁻¹) ^ C.smoothness *
        euclideanNorm (w - dyadicNormalizedAnchor j x) ^ C.smoothness +
        D * R * euclideanNorm (w - dyadicNormalizedAnchor j x) := add_le_add (hc j w hw).2 le_rfl
    _ ≤ T * ((2 ^ j)⁻¹) ^ C.smoothness *
        (max 1 ((Real.sqrt d) ^ C.smoothness) * euclideanNorm (w - dyadicNormalizedAnchor j x)) +
        D * R * euclideanNorm (w - dyadicNormalizedAnchor j x) := by gcongr
    _ = (scale) *
        ((2 ^ j)⁻¹) ^ C.smoothness * euclideanNorm (w - dyadicNormalizedAnchor j x) := by ring
    _ ≤ _ := by
      bound

theorem uniform_domain_admissible_dyadicPopulationIncrement_successor_bound :
    ∃ E : ℝ, 0 < E ∧ ∀ Udom, ∀ θ, Admissible (C.withDomain Udom) θ →
      ∀ x ∈ unitCube d, ∀ j,
      ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (dyadicPopulationIncrement θ x (j + 1))‖ ≤
        E * ((2 ^ (j + 1))⁻¹) ^ C.smoothness := by
  obtain ⟨D, hD, hcoeff⟩ := uniform_domain_admissible_dyadicPopulationFit_taylor_coefficients C
  refine ⟨(D * (1 + (1 / 2) * 2 ^ C.smoothness)), mul_pos hD (by positivity), ?_⟩
  intro Udom θ hθ x hx j
  obtain ⟨c, hc⟩ := hcoeff Udom θ hθ x hx
  let e := fun i => dyadicPopulationFit θ i x - dyadicTaylorCoefficients c i
  rw [(by rw [dyadicTaylorCoefficients_succ, Matrix.mulVec_sub]; unfold dyadicPopulationIncrement anchoredIncrement; abel : dyadicPopulationIncrement θ x (j + 1) = dyadicPopulationFit θ (j + 1) x - dyadicTaylorCoefficients c (j + 1) - anchoredTransport d C.order *ᵥ (dyadicPopulationFit θ j x - dyadicTaylorCoefficients c j))]
  have hsub  := norm_sub_le
      ((EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (e (j + 1)))
      ((EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (anchoredTransport d C.order *ᵥ e j))
  apply hsub.trans
  apply (add_le_add (hc (j + 1)) ((anchoredTransport_euclidean_norm (e j)).trans (mul_le_mul_of_nonneg_left (hc j) (by norm_num)))).trans_eq
  rw [dyadic_inverse_scale_succ j, Real.mul_rpow (by norm_num) (by positivity)]
  ring

theorem uniform_domain_admissible_dyadicPopulationIncrement_root_bound :
    ∃ E : ℝ, 0 < E ∧ ∀ Udom, ∀ θ, Admissible (C.withDomain Udom) θ →
      ∀ x ∈ unitCube d,
      ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (dyadicPopulationIncrement θ x 0)‖ ≤ E := by
  obtain ⟨D, hD, hfit⟩ := anchoredPopulationFit_coefficient_error (d := d) (ℓ := C.order)
    C.densityLower C.densityUpper C.densityLower_pos (by linarith [C.one_lt_densityUpper])
  let E := max 1 (D * (2 * C.holderBound))
  refine ⟨E, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro Udom θ hθ x hx
  have hres : ∀ w ∈ unitCube d, |dyadicRegressionDifference θ 0 x w -
      anchoredFitPolynomial (dyadicNormalizedAnchor 0 x) (0 : AnchoredIndex d C.order → ℝ) w| ≤
        2 * C.holderBound := by
    intro w hw
    simp [anchoredFitPolynomial]
    exact (abs_sub _ _).trans (by
      have ha := admissible_regression_value_bound hθ (dyadicCellAffine_mem_cube 0 x w hw)
      have hb := admissible_regression_value_bound hθ hx
      dsimp [ModelConstants.withDomain] at ha hb
      linarith)
  have h := hfit _ (gridNormalizedAnchor_mem_cube _ (by positivity) hx) _ _
    (dyadicNormalizedDensity_measurable hθ 0 x) (dyadicNormalizedDensity_bounds hθ 0 x)
    (dyadicRegressionDifference_continuousOn hθ 0 x) 0 (2 * C.holderBound)
    (mul_nonneg (by norm_num) C.holderBound_pos.le) hres
  change ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (dyadicPopulationFit θ 0 x)‖ ≤ E
  rw [dyadicPopulationFit_eq_normalized hθ]
  simpa only [sub_zero, dyadicNormalizedAnchor] using h.trans (le_max_right 1 _)


theorem uniform_domain_admissible_dyadicPopulationIncrement_bound :
    ∃ E : ℝ, 0 < E ∧ ∀ Udom, ∀ θ, Admissible (C.withDomain Udom) θ →
      ∀ x ∈ unitCube d, ∀ j,
      ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (dyadicPopulationIncrement θ x j)‖ ≤
        E * ((2 ^ j)⁻¹) ^ C.smoothness := by
  obtain ⟨E0, hE0, hroot⟩ := uniform_domain_admissible_dyadicPopulationIncrement_root_bound C
  obtain ⟨E1, hE1, hsucc⟩ := uniform_domain_admissible_dyadicPopulationIncrement_successor_bound C
  refine ⟨max E0 E1, hE0.trans_le (le_max_left _ _), ?_⟩
  intro Udom θ hθ x hx j
  cases j with
  | zero => simpa using (hroot Udom θ hθ x hx).trans (le_max_left E0 E1)
  | succ j =>
    exact (hsucc Udom θ hθ x hx j).trans
      (by bound)

theorem uniform_domain_admissible_dyadicPopulationFit_physical_error :
    ∃ E : ℝ, 0 < E ∧ ∀ Udom, ∀ θ, Admissible (C.withDomain Udom) θ →
      ∀ j, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d, y ∈ dyadicPilotCell j x →
      |θ.regression y - θ.regression x - dyadicAnchoredFeature j x y ⬝ᵥ dyadicPopulationFit (ℓ := C.order) θ j x| ≤
        E * euclideanNorm (y - x) * ((2 ^ j)⁻¹) ^ (C.smoothness - 1) := by
  obtain ⟨E, hE, hfit⟩ := uniform_domain_admissible_dyadicPopulationFit_spatial_error C
  refine ⟨E, hE, ?_⟩
  intro Udom θ hθ j x hx y hy hcell
  have hw : dyadicNormalizedAnchor j y ∈ unitCube d := gridNormalizedAnchor_mem_cube _ (by positivity) hy
  have he := dyadicCellAffine_same_cell hcell
  have h := hfit Udom θ hθ j x hx _ hw
  rw [dyadicPopulationFit_physical_evaluation hcell] at h
  unfold dyadicRegressionDifference at h
  rw [he] at h
  apply h.trans_eq
  have hd := dyadicCellAffine_euclidean_distance j x (dyadicNormalizedAnchor j y)
  rw [he] at hd
  rw [mul_assoc, positive_rpow_times_distance _ _ _ (by positivity), ← hd]
  ring


theorem uniform_domain_admissible_dyadic_increment_polynomial_error :
    ∃ E : ℝ, 0 < E ∧ ∀ Udom, ∀ θ, Admissible (C.withDomain Udom) θ →
      ∀ j, ∀ x ∈ unitCube d, ∀ m,
      ‖(EuclideanSpace.equiv (Fin (anchoredDimension d C.order)) ℝ).symm
        (incrementFinVector (anchoredDimension d C.order) C.densityLower C.densityUpper
          (anchoredFinTransport d C.order) (θ.regression x) m (dyadicIncrementRawMean θ j x) -
            anchoredFinVector (dyadicPopulationIncrement θ x j))‖ ≤
        E * ((2 ^ j)⁻¹) ^ C.smoothness * (m + 1 : ℕ) ^ anchoredDimension d C.order *
          Real.exp (-m * intervalExteriorTau C.densityLower C.densityUpper) := by
  obtain ⟨χ, hχ, hcond⟩ := anchoredFinSimilarityUnit_uniform_condition (d := d) (ℓ := C.order)
  obtain ⟨D, hD, hinc⟩ := uniform_domain_admissible_dyadicPopulationIncrement_bound C
  let E₀ := χ ^ 2 * C.densityUpper ^ (anchoredDimension d C.order + 1) *
    parentInverseErrorConstant C.densityLower C.densityUpper (anchoredDimension d C.order)
  refine ⟨(max 1 (E₀ * D)), zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro Udom θ hθ j x hx m
  let u := dyadicNormalizedAnchor j x
  let v := dyadicNormalizedAnchor (j - 1) x
  let p := dyadicNormalizedDensity θ j x
  let q := if j = 0 then (fun _ => 1) else dyadicNormalizedDensity θ (j - 1) x
  let U := dyadicFinPilotMoments (ℓ := C.order) θ j x
  let V := if j = 0 then 0 else dyadicFinPilotMoments (ℓ := C.order) θ (j - 1) x
  have hqmeas : Measurable q := by
    by_cases hj : j = 0
    · aesop
    · simpa [q, hj] using dyadicNormalizedDensity_measurable hθ (j - 1) x
  have hqb : ∀ᵐ w ∂cubeVolume d, C.densityLower ≤ q w ∧ q w ≤ C.densityUpper := by
    by_cases hj : j = 0
    · exact Filter.Eventually.of_forall (fun _ => by
        simpa [q, hj] using And.intro C.densityLower_lt_one.le C.one_lt_densityUpper.le)
    · simpa [q, hj, ModelConstants.withDomain] using dyadicNormalizedDensity_bounds hθ (j - 1) x
  have hparent : anchoredFinNormalizedGram (ℓ := C.order) v q =
      if j = 0 then 1 else dyadicFinPilotGram θ (j - 1) x := by
    by_cases hj : j = 0
    · simp [q, hj, anchoredFinNormalizedGram_one]
    · simp only [q, hj, ite_false]
      exact (dyadicFinPilotGram_eq_normalized hθ (j - 1) x).symm
  have hactual : (anchoredFinNormalizedGram u p)⁻¹ *ᵥ
      (U false - θ.regression x • U true) - anchoredFinTransport d C.order *ᵥ
        ((anchoredFinNormalizedGram v q)⁻¹ *ᵥ (V false - θ.regression x • V true)) =
        anchoredFinVector (dyadicPopulationIncrement θ x j) := by
    rw [hparent, ← dyadicFinPilotGram_eq_normalized hθ j x]
    solve_by_elim [dyadicFinite_increment_eq_actual]
  have hsmall : ‖(EuclideanSpace.equiv (Fin (anchoredDimension d C.order)) ℝ).symm
      ((anchoredFinNormalizedGram u p)⁻¹ *ᵥ (U false - θ.regression x • U true) -
        anchoredFinTransport d C.order *ᵥ
          ((anchoredFinNormalizedGram v q)⁻¹ *ᵥ (V false - θ.regression x • V true)))‖ ≤
      D * ((2 ^ j)⁻¹) ^ C.smoothness := by
    rw [hactual, anchoredFinVector_norm]
    exact hinc Udom θ hθ x hx j
  have he := anchoredNormalized_increment_error
    (dyadicNormalizedDensity_measurable hθ j x) hqmeas
    C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper)
    (dyadicNormalizedDensity_bounds hθ j x) hqb
    (hcond u (gridNormalizedAnchor_mem_cube _ (by positivity) hx)) hsmall m
  rw [hactual] at he
  have hval : dyadicIncrementRawMean θ j x = fun a =>
      incrementValuation (anchoredFinNormalizedGram u p) (anchoredFinNormalizedGram v q) U V
        ((Fintype.equivFin (incrementVariables (anchoredDimension d C.order))).symm a) := by
    rw [dyadicIncrementRawMean_eq_population hθ j hx]
    have hcurrent : anchoredFinNormalizedGram (ℓ := C.order) u p = dyadicFinPilotGram θ j x :=
      (dyadicFinPilotGram_eq_normalized hθ j x).symm
    simp [dyadicIncrementPopulation, hparent, hcurrent]
    rfl
  rw [hval, incrementFinVector_eval_population]
  calc
    _ ≤ _ := he
    _ = (E₀ * D) * ((2 ^ j)⁻¹) ^ C.smoothness * (m + 1 : ℕ) ^ anchoredDimension d C.order *
        Real.exp (-m * intervalExteriorTau C.densityLower C.densityUpper) := by ring
    _ ≤ _ := by
      gcongr
      exact le_max_right _ _

theorem uniform_domain_admissible_dyadic_polynomial_row_error :
    ∃ E : ℝ, 0 < E ∧ ∀ Udom, ∀ θ, Admissible (C.withDomain Udom) θ →
      ∀ j, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d, y ∈ dyadicPilotCell j x → ∀ m,
      |dyadicPilotRow j x y ⬝ᵥ dyadicPopulationPolynomial C θ j x (θ.regression x) m -
        dyadicAnchoredFeature j x y ⬝ᵥ dyadicPopulationIncrement (ℓ := C.order) θ x j| ≤
      E * euclideanNorm (y - x) * ((2 ^ j)⁻¹) ^ (C.smoothness - 1) *
        (m + 1 : ℕ) ^ anchoredDimension d C.order * Real.exp (-m * paperTau C) := by
  obtain ⟨B, hB, herror⟩ := uniform_domain_admissible_dyadic_increment_polynomial_error C
  refine ⟨(max 1 (B * (anchoredDimension d C.order))), zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro Udom θ hθ j x hx y hy hcell m
  have hnorm := herror Udom θ hθ j x hx m
  rw [exteriorTau_sqrt_ratio C.densityLower_pos
    (C.densityLower_lt_one.trans C.one_lt_densityUpper)] at hnorm
  rw [← dyadicPilotRow_dot_coefficients, ← dotProduct_sub]
  apply (finite_row_abs_dot_le_euclidean_norm _ _).trans
  have hd : 0 ≤ euclideanNorm (y - x) := by unfold euclideanNorm; positivity
  calc
    _ ≤ ((anchoredDimension d C.order) * 2 ^ j * euclideanNorm (y - x)) *
        (B * ((2 ^ j)⁻¹) ^ C.smoothness * (m + 1 : ℕ) ^ anchoredDimension d C.order *
          Real.exp (-m * paperTau C)) := mul_le_mul (dyadicPilotRow_sum_abs_le_distance (ℓ := C.order) hx hy hcell) hnorm (norm_nonneg _) (by positivity)
    _ = (B * (anchoredDimension d C.order)) * euclideanNorm (y - x) *
        (2 ^ j * ((2 ^ j)⁻¹) ^ C.smoothness) *
          (m + 1 : ℕ) ^ anchoredDimension d C.order * Real.exp (-m * paperTau C) := by ring
    _ = _ := by
      rw [dyadic_scale_rpow_cancel]
    _ ≤ _ := by
      gcongr
      exact le_max_right _ _

end

variable {d : ℕ} {C : ModelConstants d} (hs : 1 < C.smoothness)

include hs in
theorem uniform_domain_admissible_dyadicPopulationResidual_bound :
    ∃ E : ℝ, 0 < E ∧ ∀ Udom, ∀ θ, Admissible (C.withDomain Udom) θ →
      ∀ J, ∀ m, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d,
      y ∈ dyadicPilotCell J x →
        |dyadicPopulationResidual C θ J m x y| ≤
          E * euclideanNorm (y - x) * dyadicPopulationBiasBudget C J m := by
  let := anchoredIndex_nonempty_of_one_lt_smoothness hs
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
    simp [dyadicPopulationIncrement_telescope, dyadicPopulationResidual]
  rw [heq]
  apply (abs_add_le _ _).trans
  apply (add_le_add (hfit Udom θ hθ J x hx y hy hcell) (Finset.abs_sum_le_sum_abs _ _)).trans
  calc
    _ ≤ A * euclideanNorm (y - x) * ((2 ^ J)⁻¹) ^ (C.smoothness - 1) +
        ∑ j ∈ Finset.range (J + 1), B * euclideanNorm (y - x) *
          ((2 ^ j)⁻¹) ^ (C.smoothness - 1) * (m j + 1 : ℕ) ^ anchoredDimension d C.order *
            Real.exp (-(m j) * paperTau C) := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_sub_comm]
      grind [dyadicPilotCell_subset_coarser (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) x hcell]
    _ ≤ E * euclideanNorm (y - x) * ((2 ^ J)⁻¹) ^ (C.smoothness - 1) +
        ∑ j ∈ Finset.range (J + 1), E * euclideanNorm (y - x) *
          ((2 ^ j)⁻¹) ^ (C.smoothness - 1) * (m j + 1 : ℕ) ^ anchoredDimension d C.order *
            Real.exp (-(m j) * paperTau C) := by
      bound
    _ = _ := by
      unfold dyadicPopulationBiasBudget
      rw [mul_add, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem uniform_domain_admissible_dyadicPopulationPolynomial_uniform_bound (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] {Y : ℝ} (hY : 0 ≤ Y) :
    ∃ B : ℝ, 0 < B ∧ ∀ Udom, ∀ θ, Admissible (C.withDomain Udom) θ →
      ∀ j, ∀ x ∈ unitCube d, ∀ y, |y| ≤ Y → ∀ m,
        ‖dyadicPopulationPolynomial C θ j x y m‖ ≤ B := by
  obtain ⟨B, A, hB, _, hd⟩ := uniform_domain_dyadic_increment_vector_derivative_bound C hY
  refine ⟨B, hB, ?_⟩
  intro U θ hθ j x hx y hy m
  simpa [dyadicPopulationPolynomial] using hd U θ hθ j x hx y hy m 0 (fun i => Fin.elim0 i)

include hs in
theorem uniform_domain_admissible_dyadicPopulationRawPolynomial_uniform_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ Udom, ∀ θ, Admissible (C.withDomain Udom) θ →
      ∀ j, ∀ x ∈ unitCube d, ∀ t, ∀ m,
        ‖dyadicPopulationRawPolynomial C θ j x t m‖ ≤ B := by
  let := anchoredIndex_nonempty_of_one_lt_smoothness hs
  obtain ⟨B, hB, hb⟩ := uniform_domain_admissible_dyadicPopulationPolynomial_uniform_bound C zero_le_one
  refine ⟨2 * B, mul_pos (by norm_num) hB, ?_⟩
  intro Udom θ hθ j x hx t m
  have h0 := hb Udom θ hθ j x hx 0 (by norm_num) m
  have h1 := hb Udom θ hθ j x hx 1 (by norm_num) m
  have he0 : dyadicPopulationRawPolynomial C θ j x false m = dyadicPopulationPolynomial C θ j x 0 m := by
    simp [dyadicPopulationPolynomial_affine]
  cases t
  · grind
  · have he : dyadicPopulationRawPolynomial C θ j x true m =
        dyadicPopulationPolynomial C θ j x 0 m - dyadicPopulationPolynomial C θ j x 1 m := by
      simp [dyadicPopulationPolynomial_affine]
    rw [he]
    exact (norm_sub_le _ _).trans (by linarith)

include hs in
theorem uniform_domain_admissible_dyadicPopulationPilotSum_uniform_bound :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ Udom, ∀ θ, Admissible (C.withDomain Udom) θ →
      ∀ J, ∀ m, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d,
      y ∈ dyadicPilotCell J x → ∀ t, |dyadicPopulationPilotSum C θ J m t (x, y)| ≤ R := by
  obtain ⟨B, hB, hb⟩ := uniform_domain_admissible_dyadicPopulationRawPolynomial_uniform_bound hs
  let R := (2 * (anchoredDimension d C.order) * Real.sqrt d) * B
  refine ⟨R, by positivity, ?_⟩
  intro Udom θ hθ J m x hx y hy hcell t
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      exact (finite_row_abs_dot_le_pi_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hb Udom θ hθ j x hx ..) (Finset.sum_nonneg (fun _ _ => abs_nonneg _)))
    _ = _ := by
      rw [Finset.sum_mul]
    _ ≤ R := mul_le_mul_of_nonneg_right (dyadicPilotRow_total_abs_le hx hy hcell) hB.le

include hs in
theorem uniform_domain_admissible_dyadicPopulationCoefficients_uniform_bound :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ Udom, ∀ θ, Admissible (C.withDomain Udom) θ →
      ∀ J, ∀ m, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d,
      y ∈ dyadicPilotCell J x → ‖dyadicPopulationCoefficients C θ J m (x, y)‖ ≤ Cp := by
  obtain ⟨R, hR, hb⟩ := uniform_domain_admissible_dyadicPopulationPilotSum_uniform_bound hs
  refine ⟨Real.sqrt 3 * (1 + R), mul_pos (by positivity) (by positivity), ?_⟩
  intro Udom θ hθ J m x hx y hy hc
  have ht := hb Udom θ hθ J m x hx y hy hc true
  have hf := hb Udom θ hθ J m x hx y hy hc false
  have hcoord i : |dyadicPopulationCoefficients C θ J m (x, y) i| ≤ 1 + R := by
    fin_cases i
    · simpa [dyadicPopulationCoefficients] using hR
    · exact (abs_add_le _ _).trans (by simpa using add_le_add_left ht 1)
    · change |-dyadicPopulationPilotSum C θ J m false (x, y)| ≤ _
      rw [abs_neg]
      nlinarith
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ ∑ _i : Fin 3, (1 + R) ^ 2 := by
      bound
    _ = 3 * (1 + R) ^ 2 := by simp
    _ = _ := by rw [mul_pow, Real.sq_sqrt (by norm_num)]

end NearlyMinimax
