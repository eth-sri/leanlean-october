module

public import NearlyMinimax.CoefficientPairEstimator
public import NearlyMinimax.DyadicPilotMultilevel
public import NearlyMinimax.UpperMasterRate

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Matrix MvPolynomial
open scoped Topology ENNReal BigOperators RealInnerProductSpace Matrix.Norms.L2Operator
namespace NearlyMinimax

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

-- 1. Pilot model envelope & virtual parent helper

private def pilotModelConstants {d : ℕ} (C : ModelConstants d) : ModelConstants d :=
  { C with
    holderBound := max C.holderBound 1
    holderBound_pos := C.holderBound_pos.trans_le (le_max_left _ _) }

private theorem admissible_pilotModelConstants {d : ℕ} (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ) :
    Admissible (pilotModelConstants C) θ := by
  obtain ⟨hpd, hpf, hpb, hpone, ⟨F, hFeq, hFdiff, hFnorm⟩, hVlo, hVhi, herr⟩ := hθ
  exact ⟨hpd, hpf, hpb, hpone, ⟨F, hFeq, hFdiff, hFnorm.trans (ENNReal.ofReal_mono (le_max_left _ _))⟩,
    hVlo, hVhi, herr⟩

private theorem virtualParentDensity_facts {d : ℕ} (C : ModelConstants d) (Udom : ExtensionDomain d)
    (θ : RegressionParameter d) (hθ : Admissible (C.withDomain Udom) θ) (j : ℕ) (x : Covariate d) :
    let q := if j = 0 then fun _ : Covariate d => (1 : ℝ) else dyadicNormalizedDensity θ (j - 1) x
    Measurable q ∧ (∀ᵐ w ∂cubeVolume d, C.densityLower ≤ q w ∧ q w ≤ C.densityUpper) := by
  dsimp only
  by_cases hj : j = 0
  · simp only [hj, ↓reduceIte]
    exact ⟨measurable_const, Eventually.of_forall fun _ => ⟨C.densityLower_lt_one.le, C.one_lt_densityUpper.le⟩⟩
  · simp only [hj, ↓reduceIte]
    exact ⟨dyadicNormalizedDensity_measurable (C.withDomain Udom) θ hθ (j - 1) x,
      dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ (j - 1) x⟩

-- 2. Uniform-domain moment & inverse-derivative bounds

private theorem uniform_domain_finPilotMoments_bound {d : ℕ} (C : ModelConstants d) :
    ∃ W : ℝ, 0 < W ∧ ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
      ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ t : Bool, ‖dyadicFinPilotMoments (ℓ := C.order) θ j x t‖ ≤ W := by
  obtain ⟨W, hW, hb⟩ := anchoredFinMomentFamilies_uniform_bound (d := d) (ℓ := C.order)
    C.densityUpper C.holderBound (zero_le_one.trans C.one_lt_densityUpper.le) C.holderBound_pos.le
  refine ⟨W, hW, fun Udom θ hθ j x hx t => ?_⟩
  rw [dyadicFinPilotMoments_eq_anchored (C.withDomain Udom) θ hθ j x hx]
  exact hb _ (gridNormalizedAnchor_mem_cube _ (by positivity) x hx) _ _
    ((dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ j x).mono fun _ hw => ⟨C.densityLower_pos.le.trans hw.1, hw.2⟩)
    (fun w hw => admissible_regression_value_bound (C.withDomain Udom) θ hθ _ (dyadicCellAffine_mem_cube j x w hw)) t

private theorem uniform_domain_increment_vector_derivative_bound {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] (Y : ℝ) (hY : 0 ≤ Y) :
    ∃ D A : ℝ, 0 < D ∧ 0 < A ∧
      ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
      ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ y : ℝ, |y| ≤ Y → ∀ m k : ℕ,
      ∀ directions : Fin k → Fin (Fintype.card (incrementVariables (anchoredDimension d C.order))) → ℝ,
        ‖iteratedFDeriv ℝ k
          (incrementFinVector (anchoredDimension d C.order) C.densityLower C.densityUpper
            (anchoredFinTransport d C.order) y m)
          (dyadicIncrementRawMean θ j x) directions‖ ≤
          D * (k.factorial : ℝ) * A ^ k * ∏ i, ‖directions i‖ := by
  obtain ⟨W, hW, hmom⟩ := uniform_domain_finPilotMoments_bound C
  obtain ⟨B, A, hB, hA, hder⟩ := anchored_population_inverse_derivatives
    (d := d) (ℓ := C.order) C.densityLower C.densityUpper W Y C.densityLower_pos
    (C.densityLower_lt_one.trans C.one_lt_densityUpper) hW.le hY
  refine ⟨B, A, hB, hA, fun Udom θ hθ j x hx y hy m k directions => ?_⟩
  obtain ⟨hqm, hqb⟩ := virtualParentDensity_facts C Udom θ hθ j x
  have hV (t : Bool) : ‖(if j = 0 then (0 : Bool → Fin (anchoredDimension d C.order) → ℝ)
      else dyadicFinPilotMoments θ (j - 1) x) t‖ ≤ W := by
    by_cases hj : j = 0 <;> simp [hj, hW.le, hmom Udom θ hθ (j - 1) x hx t]
  have hd := hder (dyadicNormalizedAnchor j x) (dyadicNormalizedAnchor (j - 1) x)
    (gridNormalizedAnchor_mem_cube ((2 : ℕ) ^ j) (by positivity) x hx)
    (gridNormalizedAnchor_mem_cube ((2 : ℕ) ^ (j - 1)) (by positivity) x hx)
    (dyadicNormalizedDensity θ j x) _
    (dyadicNormalizedDensity_measurable (C.withDomain Udom) θ hθ j x) hqm
    (dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ j x) hqb
    (dyadicFinPilotMoments θ j x) (if j = 0 then 0 else dyadicFinPilotMoments θ (j - 1) x)
    (hmom Udom θ hθ j x hx) hV y hy m k directions
  rwa [← dyadicIncrementRawMean_eq_with_virtual_parent (C.withDomain Udom) θ hθ j x hx] at hd

-- 3. Uniform-domain population residual & supported coefficient bounds

private theorem uniform_domain_population_bounds {d : ℕ} (C : ModelConstants d)
    (hs : 1 < C.smoothness) :
    ∃ Cp E_res : ℝ, 0 < Cp ∧ 0 < E_res ∧
      (∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
        ∀ J Jh : ℕ, J ≤ Jh → ∀ m : ℕ → ℕ,
        ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
          sameLabelKernel (regularGridCell ((2 : ℕ) ^ Jh) (by positivity)) w ≠ 0 →
            ‖dyadicPopulationCoefficients C θ J m w‖ ≤ Cp) ∧
      (∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
        ∀ J : ℕ, ∀ m : ℕ → ℕ, ∀ x ∈ unitCube d, ∀ y ∈ unitCube d,
        y ∈ dyadicPilotCell J x →
          |dyadicPopulationResidual C θ J m x y| ≤
            E_res * euclideanNorm (y - x) * dyadicPopulationBiasBudget C J m) := by
  letI : Nonempty (AnchoredIndex d C.order) := anchoredIndex_nonempty_of_one_lt_smoothness C hs
  -- Part A: Supported bound on `dyadicPopulationCoefficients` via `k = 0` of `uniform_domain_increment_vector_derivative_bound`
  obtain ⟨B_pol, _, hB_pol, _, hder0⟩ := uniform_domain_increment_vector_derivative_bound C 1 zero_le_one
  let R_sum := (2 * (anchoredDimension d C.order : ℝ) * Real.sqrt (d : ℝ)) * (2 * B_pol)
  let Cp := Real.sqrt 3 * (1 + R_sum)
  have hCp_pos : 0 < Cp := by dsimp [Cp, R_sum]; positivity
  have hsupp : ∀ Udom : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain Udom) θ →
      ∀ J Jh : ℕ, J ≤ Jh → ∀ m : ℕ → ℕ,
      ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
        sameLabelKernel (regularGridCell ((2 : ℕ) ^ Jh) (by positivity)) w ≠ 0 →
          ‖dyadicPopulationCoefficients C θ J m w‖ ≤ Cp := by
    intro Udom θ hθ J Jh hJJh m
    let _ := designLaw_isProbability (C.withDomain Udom) θ hθ
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := designLaw θ) (ν := designLaw θ)).ae (designLaw_cube_ae θ),
      (Measure.quasiMeasurePreserving_snd (μ := designLaw θ) (ν := designLaw θ)).ae (designLaw_cube_ae θ)] with w hx hy hw
    have hc_Jh : w.2 ∈ dyadicPilotCell Jh w.1 := by
      change regularGridCell ((2 : ℕ) ^ Jh) (by positivity) w.2 = regularGridCell ((2 : ℕ) ^ Jh) (by positivity) w.1
      by_contra h; exact hw (by simp [sameLabelKernel, Ne.symm h])
    have hc := dyadicPilotCell_subset_coarser J Jh hJJh w.1 hc_Jh
    have hraw (j : ℕ) (t : Bool) : ‖dyadicPopulationRawPolynomial C θ j w.1 t (m j)‖ ≤ 2 * B_pol := by
      have hp_y (y : ℝ) (hy_b : |y| ≤ 1) : ‖dyadicPopulationPolynomial C θ j w.1 y (m j)‖ ≤ B_pol := by
        simpa only [dyadicPopulationPolynomial, iteratedFDeriv_zero_apply, Nat.factorial_zero, Nat.cast_one,
          pow_zero, mul_one, Fin.prod_univ_zero] using hder0 Udom θ hθ j w.1 hx y hy_b (m j) 0 Fin.elim0
      have h0 := hp_y 0 (by norm_num)
      have h1 := hp_y 1 (by norm_num)
      cases t
      · rw [show dyadicPopulationRawPolynomial C θ j w.1 false (m j) = dyadicPopulationPolynomial C θ j w.1 0 (m j) by
          rw [dyadicPopulationPolynomial_affine, zero_smul, sub_zero]]
        linarith
      · rw [show dyadicPopulationRawPolynomial C θ j w.1 true (m j) =
            dyadicPopulationPolynomial C θ j w.1 0 (m j) - dyadicPopulationPolynomial C θ j w.1 1 (m j) by
          rw [dyadicPopulationPolynomial_affine, dyadicPopulationPolynomial_affine]; simp only [zero_smul, sub_zero, one_smul]; abel]
        exact (norm_sub_le _ _).trans (by linarith)
    have hpsum (t : Bool) : |dyadicPopulationPilotSum C θ J m t w| ≤ R_sum := by
      rcases w with ⟨x1, x2⟩
      unfold dyadicPopulationPilotSum
      refine (Finset.abs_sum_le_sum_abs ..).trans
        ((Finset.sum_le_sum fun j _ => (finite_row_abs_dot_le_pi_norm _ _).trans
          (mul_le_mul_of_nonneg_left (hraw j t) (Finset.sum_nonneg fun _ _ => abs_nonneg _))).trans ?_)
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (dyadicPilotRow_total_abs_le J x1 x2 hx hy hc) (by positivity)
    have hcoord (i : Fin 3) : |dyadicPopulationCoefficients C θ J m w i| ≤ 1 + R_sum := by
      rcases w with ⟨x1, x2⟩
      fin_cases i
      · have : 0 ≤ R_sum := by dsimp [R_sum]; positivity
        simpa [dyadicPopulationCoefficients]
      · change |-1 + dyadicPopulationPilotSum C θ J m true (x1, x2)| ≤ 1 + R_sum
        exact (abs_add_le _ _).trans (by simpa using add_le_add_left (hpsum true) 1)
      · change |-dyadicPopulationPilotSum C θ J m false (x1, x2)| ≤ 1 + R_sum
        rw [abs_neg]; linarith [hpsum false]
    rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    calc (∑ i : Fin 3, ‖dyadicPopulationCoefficients C θ J m w i‖ ^ 2)
      _ ≤ ∑ _i : Fin 3, (1 + R_sum) ^ 2 := Finset.sum_le_sum fun i _ =>
          pow_le_pow_left₀ (norm_nonneg _) (by simpa only [Real.norm_eq_abs] using hcoord i) 2
      _ = Cp ^ 2 := by simp [Cp, mul_pow]
  -- Part B: Residual bound
  obtain ⟨D_fit, _, hfit⟩ := anchoredPopulationFit_coefficient_error (d := d) (ℓ := C.order)
    C.densityLower C.densityUpper C.densityLower_pos (by linarith [C.one_lt_densityUpper])
  obtain ⟨D_pt, _, hpoint⟩ := anchoredPopulationFit_pointwise_error (d := d) (ℓ := C.order)
    C.densityLower C.densityUpper C.densityLower_pos (by linarith [C.one_lt_densityUpper])
  obtain ⟨χ, _, hcond⟩ := anchoredFinSimilarityUnit_uniform_condition (d := d) (ℓ := C.order)
  let T_tay := (d : ℝ) ^ C.order * (2 * C.holderBound) / C.order.factorial
  let E_fit := max 1 (T_tay * max 1 ((Real.sqrt (d : ℝ)) ^ C.smoothness) + D_pt * (taylorErrorFactor C * C.holderBound))
  let E_tay := max 1 (D_fit * (taylorErrorFactor C * C.holderBound))
  let E_inc := max (max 1 (D_fit * (2 * C.holderBound))) (E_tay * (1 + (1 / 2) * (2 : ℝ) ^ C.smoothness))
  let E_inv0 := χ ^ 2 * C.densityUpper ^ (anchoredDimension d C.order + 1) *
    parentInverseErrorConstant C.densityLower C.densityUpper (anchoredDimension d C.order)
  let E_pol := max 1 (max 1 (E_inv0 * E_inc) * (anchoredDimension d C.order : ℝ))
  let E_res := max E_fit E_pol
  have hE_res : 0 < E_res := (zero_lt_one.trans_le (le_max_left _ _)).trans_le (le_max_left _ _)
  refine ⟨Cp, E_res, hCp_pos, hE_res, hsupp, fun Udom θ hθ J m x hx y hy hcell => ?_⟩
  -- Physical fit error at level `J`
  have hphys : |θ.regression y - θ.regression x - dyadicAnchoredFeature J x y ⬝ᵥ dyadicPopulationFit (ℓ := C.order) θ J x| ≤
      E_fit * euclideanNorm (y - x) * (((2 : ℝ) ^ J)⁻¹) ^ (C.smoothness - 1) := by
    obtain ⟨c, hc⟩ := admissible_dyadic_taylor_family (C.withDomain Udom) θ hθ x hx
    let R := taylorErrorFactor C * C.holderBound * (((2 : ℝ) ^ J)⁻¹) ^ C.smoothness
    have hR : 0 ≤ R := mul_nonneg (mul_nonneg (taylorErrorFactor_pos C).le C.holderBound_pos.le) (Real.rpow_nonneg (by positivity) _)
    have hu : dyadicNormalizedAnchor J x ∈ unitCube d := gridNormalizedAnchor_mem_cube _ (by positivity) x hx
    have hw : dyadicNormalizedAnchor J y ∈ unitCube d := gridNormalizedAnchor_mem_cube _ (by positivity) y hy
    have hp := hpoint _ hu _ _ (dyadicNormalizedDensity_measurable (C.withDomain Udom) θ hθ J x)
      (dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ J x) (dyadicRegressionDifference_continuousOn (C.withDomain Udom) θ hθ J x)
      (dyadicTaylorCoefficients c J) R hR (fun v hv => (hc J v hv).1) _ hw
    rw [← dyadicPopulationFit_eq_normalized (C.withDomain Udom) θ hθ] at hp
    have he := dyadicCellAffine_same_cell J x y hcell
    have hrad : euclideanNorm (dyadicNormalizedAnchor J y - dyadicNormalizedAnchor J x) ≤ Real.sqrt (d : ℝ) := by
      simpa only [mul_one] using euclideanNorm_le_coordinate_radius (dyadicNormalizedAnchor J y - dyadicNormalizedAnchor J x) 1 zero_le_one
        fun i => by
          change |dyadicNormalizedAnchor J y i - dyadicNormalizedAnchor J x i| ≤ 1
          exact abs_le.mpr ⟨by linarith [(hw i).1, (hu i).2], by linarith [(hw i).2, (hu i).1]⟩
    have hr0 : 0 ≤ euclideanNorm (dyadicNormalizedAnchor J y - dyadicNormalizedAnchor J x) := Real.sqrt_nonneg _
    have hpow := bounded_rpow_le_linear _ _ _ hr0 hrad hs.le
    have hTtay : 0 ≤ T_tay := div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg d) _) (mul_nonneg (by norm_num) C.holderBound_pos.le)) (Nat.cast_nonneg _)
    have hsp : |θ.regression y - θ.regression x - dyadicAnchoredFeature J x y ⬝ᵥ dyadicPopulationFit (ℓ := C.order) θ J x| ≤
        E_fit * (((2 : ℝ) ^ J)⁻¹) ^ C.smoothness * euclideanNorm (dyadicNormalizedAnchor J y - dyadicNormalizedAnchor J x) := by
      have hp' : |θ.regression y - θ.regression x - dyadicAnchoredFeature J x y ⬝ᵥ dyadicPopulationFit (ℓ := C.order) θ J x| ≤
          T_tay * (((2 : ℝ) ^ J)⁻¹) ^ C.smoothness * euclideanNorm (dyadicNormalizedAnchor J y - dyadicNormalizedAnchor J x) ^ C.smoothness +
            D_pt * R * euclideanNorm (dyadicNormalizedAnchor J y - dyadicNormalizedAnchor J x) := by
        have h1 := hp.trans (add_le_add (hc J _ hw).2 le_rfl)
        rw [dyadicPopulationFit_physical_evaluation J x y hcell] at h1
        unfold dyadicRegressionDifference at h1; rw [he] at h1
        exact h1
      refine hp'.trans ?_
      calc T_tay * (((2 : ℝ) ^ J)⁻¹) ^ C.smoothness * euclideanNorm (dyadicNormalizedAnchor J y - dyadicNormalizedAnchor J x) ^ C.smoothness +
              D_pt * R * euclideanNorm (dyadicNormalizedAnchor J y - dyadicNormalizedAnchor J x)
        _ ≤ T_tay * (((2 : ℝ) ^ J)⁻¹) ^ C.smoothness * (max 1 ((Real.sqrt (d : ℝ)) ^ C.smoothness) * euclideanNorm (dyadicNormalizedAnchor J y - dyadicNormalizedAnchor J x)) +
              D_pt * R * euclideanNorm (dyadicNormalizedAnchor J y - dyadicNormalizedAnchor J x) := by gcongr
        _ = (T_tay * max 1 ((Real.sqrt (d : ℝ)) ^ C.smoothness) + D_pt * (taylorErrorFactor C * C.holderBound)) *
              (((2 : ℝ) ^ J)⁻¹) ^ C.smoothness * euclideanNorm (dyadicNormalizedAnchor J y - dyadicNormalizedAnchor J x) := by dsimp [R]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)) hr0
    refine hsp.trans_eq ?_
    have hd_aff := dyadicCellAffine_euclidean_distance J x (dyadicNormalizedAnchor J y)
    rw [he] at hd_aff
    rw [mul_assoc, positive_rpow_times_distance _ _ _ (by positivity), ← hd_aff]; ring
  -- Increment norm bound for all `j`
  have hinc_bound (j : ℕ) :
      ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (dyadicPopulationIncrement θ x j)‖ ≤
        E_inc * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness := by
    cases j with
    | zero =>
      have hres0 : ∀ w ∈ unitCube d, |dyadicRegressionDifference θ 0 x w -
          anchoredFitPolynomial (dyadicNormalizedAnchor 0 x) (0 : AnchoredIndex d C.order → ℝ) w| ≤ 2 * C.holderBound := fun w hw => by
        simp only [anchoredFitPolynomial, Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero]
        have ha := admissible_regression_value_bound (C.withDomain Udom) θ hθ _ (dyadicCellAffine_mem_cube 0 x w hw)
        have hb := admissible_regression_value_bound (C.withDomain Udom) θ hθ x hx
        exact (abs_sub _ _).trans (by change |θ.regression (dyadicCellAffine 0 x w)| + |θ.regression x| ≤ _; dsimp [ModelConstants.withDomain] at ha hb; linarith)
      have h0 := hfit _ (gridNormalizedAnchor_mem_cube _ (by positivity) x hx) _ _
        (dyadicNormalizedDensity_measurable (C.withDomain Udom) θ hθ 0 x) (dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ 0 x)
        (dyadicRegressionDifference_continuousOn (C.withDomain Udom) θ hθ 0 x) 0 (2 * C.holderBound)
        (mul_nonneg (by norm_num) C.holderBound_pos.le) hres0
      change ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (dyadicPopulationFit θ 0 x)‖ ≤ _
      rw [dyadicPopulationFit_eq_normalized (C.withDomain Udom) θ hθ]
      simpa only [sub_zero, dyadicNormalizedAnchor, pow_zero, inv_one, Real.one_rpow, mul_one, E_inc] using
        h0.trans ((le_max_right 1 _).trans (le_max_left _ _))
    | succ j =>
      obtain ⟨c0, hc0⟩ := admissible_dyadic_taylor_family (C.withDomain Udom) θ hθ x hx
      let c : AnchoredIndex d C.order → ℝ := c0
      have hc (i : ℕ) (w : Covariate d) (hw : w ∈ unitCube d) :
          |dyadicRegressionDifference θ i x w - anchoredFitPolynomial (dyadicNormalizedAnchor i x) (dyadicTaylorCoefficients c i) w| ≤
            taylorErrorFactor C * C.holderBound * (((2 : ℝ) ^ i)⁻¹) ^ C.smoothness := (hc0 i w hw).1
      have hc_err (i : ℕ) : ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm
          (dyadicPopulationFit θ i x - dyadicTaylorCoefficients c i)‖ ≤ E_tay * (((2 : ℝ) ^ i)⁻¹) ^ C.smoothness := by
        let Ri := taylorErrorFactor C * C.holderBound * (((2 : ℝ) ^ i)⁻¹) ^ C.smoothness
        rw [dyadicPopulationFit_eq_normalized (C.withDomain Udom) θ hθ]
        refine (hfit _ (gridNormalizedAnchor_mem_cube _ (by positivity) x hx) _ _
          (dyadicNormalizedDensity_measurable (C.withDomain Udom) θ hθ i x) (dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ i x)
          (dyadicRegressionDifference_continuousOn (C.withDomain Udom) θ hθ i x) (dyadicTaylorCoefficients c i) Ri
          (mul_nonneg (mul_nonneg (taylorErrorFactor_pos C).le C.holderBound_pos.le) (Real.rpow_nonneg (by positivity) _))
          fun w hw => hc i w hw).trans ?_
        dsimp [Ri]; rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)
      let e_c (i : ℕ) := dyadicPopulationFit θ i x - dyadicTaylorCoefficients c i
      rw [dyadicPopulationIncrement_error_identity θ x c j]
      have hsub : ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (e_c (j + 1) - anchoredTransport d C.order *ᵥ e_c j)‖ ≤
          ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (e_c (j + 1))‖ +
            ‖(EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (anchoredTransport d C.order *ᵥ e_c j)‖ := by
        simpa [EuclideanSpace.equiv] using norm_sub_le
          ((EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (e_c (j + 1)))
          ((EuclideanSpace.equiv (AnchoredIndex d C.order) ℝ).symm (anchoredTransport d C.order *ᵥ e_c j))
      refine (hsub.trans (add_le_add (hc_err (j + 1))
        ((anchoredTransport_euclidean_norm (e_c j)).trans (mul_le_mul_of_nonneg_left (hc_err j) (by norm_num))))).trans ?_
      rw [dyadic_inverse_scale_succ j, Real.mul_rpow (by norm_num) (by positivity)]
      calc _ = (E_tay * (1 + (1 / 2) * (2 : ℝ) ^ C.smoothness)) * (((2 : ℝ) ^ (j + 1))⁻¹) ^ C.smoothness := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by positivity) _)
  -- Row polynomial error for each `j ≤ J`
  have hrow_err (j : ℕ) (hjJ : j ≤ J) :
      |dyadicAnchoredFeature j x y ⬝ᵥ dyadicPopulationIncrement (ℓ := C.order) θ x j -
        dyadicPilotRow j x y ⬝ᵥ dyadicPopulationPolynomial C θ j x (θ.regression x) (m j)| ≤
      E_pol * euclideanNorm (y - x) * (((2 : ℝ) ^ j)⁻¹) ^ (C.smoothness - 1) *
        ((m j + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order * Real.exp (-(m j : ℝ) * paperTau C) := by
    have hcell_j := dyadicPilotCell_subset_coarser j J hjJ x hcell
    let u := dyadicNormalizedAnchor j x
    let v := dyadicNormalizedAnchor (j - 1) x
    let p := dyadicNormalizedDensity θ j x
    let q := if j = 0 then fun _ : Covariate d => (1 : ℝ) else dyadicNormalizedDensity θ (j - 1) x
    let U := dyadicFinPilotMoments (ℓ := C.order) θ j x
    let V := if j = 0 then 0 else dyadicFinPilotMoments (ℓ := C.order) θ (j - 1) x
    obtain ⟨hqmeas, hqb⟩ := virtualParentDensity_facts C Udom θ hθ j x
    have hparent : anchoredFinNormalizedGram (ℓ := C.order) v q = if j = 0 then 1 else dyadicFinPilotGram θ (j - 1) x := by
      by_cases hj : j = 0
      · simp [q, hj, anchoredFinNormalizedGram_one]
      · simp only [q, hj, ite_false]; exact (dyadicFinPilotGram_eq_normalized (C.withDomain Udom) θ hθ (j - 1) x).symm
    have hactual : (anchoredFinNormalizedGram (ℓ := C.order) u p)⁻¹ *ᵥ (U false - θ.regression x • U true) -
        anchoredFinTransport d C.order *ᵥ ((anchoredFinNormalizedGram v q)⁻¹ *ᵥ (V false - θ.regression x • V true)) =
        anchoredFinVector (dyadicPopulationIncrement θ x j) := by
      rw [hparent, ← dyadicFinPilotGram_eq_normalized (C.withDomain Udom) θ hθ j x]
      exact dyadicFinite_increment_eq_actual (C.withDomain Udom) θ hθ j x hx
    have hsmall : ‖(EuclideanSpace.equiv (Fin (anchoredDimension d C.order)) ℝ).symm
        ((anchoredFinNormalizedGram u p)⁻¹ *ᵥ (U false - θ.regression x • U true) -
          anchoredFinTransport d C.order *ᵥ ((anchoredFinNormalizedGram v q)⁻¹ *ᵥ (V false - θ.regression x • V true)))‖ ≤
        E_inc * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness := by
      rw [hactual, anchoredFinVector_norm]; exact hinc_bound j
    have he := anchoredNormalized_increment_error u v p q
      (dyadicNormalizedDensity_measurable (C.withDomain Udom) θ hθ j x) hqmeas
      C.densityLower C.densityUpper χ (E_inc * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness)
      C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper)
      (dyadicNormalizedDensity_bounds (C.withDomain Udom) θ hθ j x) hqb
      (hcond u (gridNormalizedAnchor_mem_cube _ (by positivity) x hx))
      U V (θ.regression x) (anchoredFinTransport d C.order) hsmall (m j)
    rw [hactual] at he
    have hval : dyadicIncrementRawMean (ℓ := C.order) θ j x = fun a =>
        incrementValuation (anchoredFinNormalizedGram u p) (anchoredFinNormalizedGram v q) U V
          ((Fintype.equivFin (incrementVariables (anchoredDimension d C.order))).symm a) := by
      rw [dyadicIncrementRawMean_eq_population (C.withDomain Udom) θ hθ j x hx]
      have hcur : anchoredFinNormalizedGram (ℓ := C.order) u p = dyadicFinPilotGram θ j x :=
        (dyadicFinPilotGram_eq_normalized (C.withDomain Udom) θ hθ j x).symm
      simp only [dyadicIncrementPopulation, hparent, hcur]; rfl
    have hnorm : ‖(EuclideanSpace.equiv (Fin (anchoredDimension d C.order)) ℝ).symm
        (dyadicPopulationPolynomial C θ j x (θ.regression x) (m j) - anchoredFinVector (dyadicPopulationIncrement θ x j))‖ ≤
        max 1 (E_inv0 * E_inc) * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness * ((m j + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order *
          Real.exp (-(m j : ℝ) * paperTau C) := by
      have htau_eq : paperTau C = exteriorTau ((C.densityLower + C.densityUpper) / (C.densityUpper - C.densityLower)) :=
        (exteriorTau_sqrt_ratio C.densityLower C.densityUpper C.densityLower_pos (C.densityLower_lt_one.trans C.one_lt_densityUpper)).symm
      rw [htau_eq]
      change ‖(EuclideanSpace.equiv (Fin (anchoredDimension d C.order)) ℝ).symm
        (incrementFinVector (anchoredDimension d C.order) C.densityLower C.densityUpper (anchoredFinTransport d C.order)
          (θ.regression x) (m j) (dyadicIncrementRawMean θ j x) - anchoredFinVector (dyadicPopulationIncrement θ x j))‖ ≤ _
      rw [hval, incrementFinVector_eval_population]
      refine he.trans ?_
      rw [← mul_assoc]
      gcongr; exact le_max_right _ _
    rw [abs_sub_comm, ← dyadicPilotRow_dot_coefficients, ← dotProduct_sub]
    refine (finite_row_abs_dot_le_euclidean_norm _ _).trans ?_
    have hr := dyadicPilotRow_sum_abs_le_distance (ℓ := C.order) j x y hx hy hcell_j
    have hd0 : 0 ≤ euclideanNorm (y - x) := Real.sqrt_nonneg _
    calc _ ≤ ((anchoredDimension d C.order : ℝ) * (2 : ℝ) ^ j * euclideanNorm (y - x)) *
            (max 1 (E_inv0 * E_inc) * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness * ((m j + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order *
              Real.exp (-(m j : ℝ) * paperTau C)) := mul_le_mul hr hnorm (norm_nonneg _) (by positivity)
      _ = (max 1 (E_inv0 * E_inc) * (anchoredDimension d C.order : ℝ)) * euclideanNorm (y - x) *
            ((2 : ℝ) ^ j * (((2 : ℝ) ^ j)⁻¹) ^ C.smoothness) *
              ((m j + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order * Real.exp (-(m j : ℝ) * paperTau C) := by ring
      _ = (max 1 (E_inv0 * E_inc) * (anchoredDimension d C.order : ℝ)) * euclideanNorm (y - x) *
            (((2 : ℝ) ^ j)⁻¹) ^ (C.smoothness - 1) *
              ((m j + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order * Real.exp (-(m j : ℝ) * paperTau C) := by
            rw [dyadic_scale_rpow_cancel]
      _ ≤ _ := by gcongr; exact le_max_right _ _
  -- Combine telescoping residual
  have heq : dyadicPopulationResidual C θ J m x y =
      (θ.regression y - θ.regression x - dyadicAnchoredFeature J x y ⬝ᵥ dyadicPopulationFit (ℓ := C.order) θ J x) +
      ∑ j ∈ Finset.range (J + 1), (dyadicAnchoredFeature j x y ⬝ᵥ dyadicPopulationIncrement (ℓ := C.order) θ x j -
        dyadicPilotRow j x y ⬝ᵥ dyadicPopulationPolynomial C θ j x (θ.regression x) (m j)) := by
    rw [dyadicPopulationIncrement_telescope, Finset.sum_sub_distrib]; unfold dyadicPopulationResidual; ring
  rw [heq]
  have hd0 : 0 ≤ euclideanNorm (y - x) := Real.sqrt_nonneg _
  refine ((abs_add_le _ _).trans (add_le_add hphys ((Finset.abs_sum_le_sum_abs ..).trans
    (Finset.sum_le_sum fun j hj => hrow_err j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))))).trans ?_
  calc _ ≤ E_res * euclideanNorm (y - x) * (((2 : ℝ) ^ J)⁻¹) ^ (C.smoothness - 1) +
          ∑ j ∈ Finset.range (J + 1), E_res * euclideanNorm (y - x) *
            (((2 : ℝ) ^ j)⁻¹) ^ (C.smoothness - 1) * ((m j + 1 : ℕ) : ℝ) ^ anchoredDimension d C.order *
              Real.exp (-(m j : ℝ) * paperTau C) := by
          refine add_le_add (by gcongr; exact le_max_left _ _) (Finset.sum_le_sum fun j _ => by gcongr; exact le_max_right _ _)
    _ = E_res * euclideanNorm (y - x) * dyadicPopulationBiasBudget C J m := by
          unfold dyadicPopulationBiasBudget; rw [mul_add, Finset.mul_sum]
          congr 1; exact Finset.sum_congr rfl fun _ _ => by ring

-- 4. Multilevel statistical pilot bounds

private theorem multilevel_bounds_of_deriv {d : ℕ} (CE : ModelConstants d)
    [Nonempty (AnchoredIndex d CE.order)] (θ : RegressionParameter d) (hθe : Admissible CE θ)
    (D A : ℝ) (hD : 0 < D) (hA : 0 < A) (n J L : ℕ) (hJL : J ≤ L)
    (y : ℝ) (hy : |y| ≤ CE.holderBound) (m : ℕ → ℕ)
    (hdegree : ∀ j : Fin (J + 1), m j.val + anchoredDimension d CE.order + 1 ≤ n)
    (Λ : ℝ) (hΛ : 0 < Λ)
    (hΛn : ∀ j : Fin (J + 1), Λ ≤ (n : ℝ) - (m j.val + anchoredDimension d CE.order + 1) + 1)
    (hder : ∀ j : ℕ, ∀ x ∈ unitCube d, ∀ m_j k : ℕ, ∀ row : Fin (anchoredDimension d CE.order) → ℝ,
      ‖iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d CE.order) CE.densityLower CE.densityUpper
        (anchoredFinTransport d CE.order) y m_j row) (dyadicIncrementRawMean θ j x)‖ ≤
        (∑ i, |row i|) * D * (k.factorial : ℝ) * A ^ k) :
    (∀ x ∈ unitCube d, ∀ z ∈ unitCube d,
      regularGridCell ((2 : ℕ) ^ L) (by positivity) x = regularGridCell ((2 : ℕ) ^ L) (by positivity) z →
      (∫ t, dyadicMultilevelErrorField CE θ n J y m t (x, z) ^ 2 ∂sampleLaw θ n) ≤
        4 * ((anchoredDimension d CE.order : ℝ) * D) ^ 2 * (d : ℝ) *
          dyadicMultilevelBudget (dyadicSeriesEnvelope CE A Λ J m) J L) ∧
    (∀ ν : Covariate d × Covariate d → ℝ,
      MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)) →
      (∫ t, (∫ w, ν w * dyadicMultilevelErrorField CE θ n J y m t w
        ∂regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)) ^ 2 ∂sampleLaw θ n) ≤
        (4 * CE.densityUpper ^ 2 * (2 : ℝ) ^ d *
          ((anchoredDimension d CE.order : ℝ) * D) ^ 2 * (d : ℝ) *
            dyadicMultilevelBudget (dyadicSeriesEnvelope CE A Λ J m) J L / Λ) *
          (∫ w, ν w ^ 2 ∂regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity))) := by
  let _ := sampleLaw_isProbability CE θ hθe n
  have hraw (j : ℕ) (x : Covariate d) (hx : x ∈ unitCube d) (m_j k : ℕ)
      (row : Fin (anchoredDimension d CE.order) → ℝ) (hk : k ≤ n) :
      (((k.factorial : ℝ) * Λ ^ k)⁻¹) *
        (∫ z : Fin n → Observation d, dyadicIncrementKernel CE θ j x y m_j row k
          (fun i => incrementGlobalVector j (z (Fin.castLEEmb hk i))) ^ 2 ∂sampleLaw θ n) ≤
        ((∑ i, |row i|) * D) ^ 2 * (k.factorial : ℝ) *
          (A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d CE.order)) *
            preconditionedPilotMomentConstant CE CE.order * dyadicPilotScale d j) / Λ) ^ k := by
    obtain ⟨hind, hmeas, _, hL2, _⟩ := dyadicIncrementRawVector_sample_facts CE θ hθe j x hx
    let X (i : Fin n) (z : Fin n → Observation d) := dyadicIncrementRawVector (ℓ := CE.order) j x (z i)
    let e := Fin.castLEEmb hk
    let E := (Fintype.card (incrementVariables (anchoredDimension d CE.order)) : ℝ) *
      preconditionedPilotMomentConstant CE CE.order * dyadicPilotScale d j
    have hE : 0 ≤ E := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (preconditionedPilotMomentConstant_pos CE _).le) (dyadicPilotScale_pos _ _).le
    have hb := KernelMomentBounds.factorial_kernel_budget
      (iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d CE.order) CE.densityLower CE.densityUpper
        (anchoredFinTransport d CE.order) y m_j row) (dyadicIncrementRawMean θ j x))
      (fun i => X (e i)) (hind.precomp e.injective) (fun i => hmeas (e i)) (fun i a => hL2 (e i) a)
      E ((∑ i, |row i|) * D) A Λ hE (mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) hD.le) hA.le hΛ
      (fun i => dyadicIncrementRawVector_sample_second_le CE θ hθe j x hx (e i)) (hder j x hx m_j k row)
    have heq : (fun z : Fin n → Observation d => dyadicIncrementKernel CE θ j x y m_j row k
        (fun i => incrementGlobalVector j (z (Fin.castLEEmb hk i))) ^ 2) =
        fun z => iteratedFDeriv ℝ k (incrementFinScalar (anchoredDimension d CE.order) CE.densityLower CE.densityUpper
          (anchoredFinTransport d CE.order) y m_j row) (dyadicIncrementRawMean θ j x) (fun i => X (e i) z) ^ 2 := by
      funext z; rw [dyadicIncrementKernel_raw]
    rwa [heq]
  let H_env := dyadicSeriesEnvelope CE A Λ J m
  have hH_env : 0 ≤ H_env := dyadicSeriesEnvelope_nonneg CE A Λ hΛ.le J m
  constructor
  · intro x hx z hz hc
    let B_pt := ((anchoredDimension d CE.order : ℝ) * D) ^ 2 * (d : ℝ) * (((2 : ℝ) ^ L)⁻¹) ^ 2 * H_env
    have hB_pt : 0 ≤ B_pt := by dsimp [B_pt]; positivity
    let X_ml (j : Fin (J + 1)) (t : Fin n → Observation d) := dyadicPilotErrorField CE θ n j.val y (m j.val) t (x, z)
    have hX_ml (j : Fin (J + 1)) : MemLp (X_ml j) 2 (sampleLaw θ n) :=
      (dyadicPilotErrorField_point_moment_facts CE θ hθe n j.val x hx z y (m j.val) (hdegree j)).1
    have hE_ml (j : Fin (J + 1)) : (∫ t, X_ml j t ^ 2 ∂sampleLaw θ n) ≤ B_pt * ((2 : ℝ) ^ j.val) ^ 2 := by
      obtain ⟨hL2_p, hmean_p⟩ := dyadicPolynomialPilot_moment_facts CE θ hθe n j.val x hx y (m j.val) (dyadicPilotRow j.val x z) (hdegree j)
      let F := rowIncrementPolynomial (anchoredDimension d CE.order) CE.densityLower CE.densityUpper
        (anchoredFinTransport d CE.order) y (m j.val) (dyadicPilotRow j.val x z)
      let X_raw (i : Fin n) (t : Fin n → Observation d) := dyadicIncrementRawVector (ℓ := CE.order) j.val x (t i)
      obtain ⟨hind, hmeas, hid, hL2, hmean⟩ := dyadicIncrementRawVector_sample_facts CE θ hθe j.val x hx
      have hv := LiftL2.polynomialLift_variance_le_raw_power_l2 F X_raw (dyadicIncrementRawMean θ j.val x)
        (rowIncrementPolynomial_degree ..) (hdegree j) hind hmeas hid hL2 hmean Λ hΛ
        (by simpa only [Nat.cast_add, Nat.cast_one] using hΛn j)
      change variance (dyadicPolynomialPilot CE n j.val x y (m j.val) (dyadicPilotRow j.val x z)) (sampleLaw θ n) ≤ _ at hv
      rw [variance_eq_integral hL2_p.aemeasurable, hmean_p] at hv
      have hv' : (∫ t, X_ml j t ^ 2 ∂sampleLaw θ n) ≤
          ((∑ i, |dyadicPilotRow (ℓ := CE.order) j.val x z i|) * D) ^ 2 * dyadicPilotSeries CE A Λ j.val (m j.val) := by
        refine hv.trans ?_
        unfold dyadicPilotSeries; rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun r _ => ?_
        let e := Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans (hdegree j))
        have hFeval : (fun u => eval u F) = incrementFinScalar (anchoredDimension d CE.order) CE.densityLower CE.densityUpper
            (anchoredFinTransport d CE.order) y (m j.val) (dyadicPilotRow j.val x z) :=
          funext fun _ => rowIncrementPolynomial_eval ..
        have hb := KernelMomentBounds.factorial_kernel_budget
          (iteratedFDeriv ℝ (r.val + 1) (fun u => eval u F) (dyadicIncrementRawMean θ j.val x))
          (fun i => X_raw (e i)) (hind.precomp e.injective) (fun i => hmeas (e i)) (fun i a => hL2 (e i) a)
          ((Fintype.card (incrementVariables (anchoredDimension d CE.order)) : ℝ) * preconditionedPilotMomentConstant CE CE.order * dyadicPilotScale d j.val)
          ((∑ i, |dyadicPilotRow j.val x z i|) * D) A Λ
          (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (preconditionedPilotMomentConstant_pos CE _).le) (dyadicPilotScale_pos _ _).le)
          (mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) hD.le) hA.le hΛ
          (fun i => dyadicIncrementRawVector_sample_second_le CE θ hθe j.val x hx (e i))
          (hFeval ▸ hder j.val x hx (m j.val) (r.val + 1) _)
        simpa only [mul_assoc] using hb
      have hr := dyadicPilotRow_sum_abs_le_fine_cell (ℓ := CE.order) j.val L ((Nat.le_of_lt_succ j.isLt).trans hJL) x z hx hz hc.symm
      refine (hv'.trans (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) hD.le) (mul_le_mul_of_nonneg_right hr hD.le) 2)
        (dyadicPilotSeries_nonneg CE A Λ hΛ.le _ _))).trans ?_
      calc _ = (((anchoredDimension d CE.order : ℝ) * D) ^ 2 * (d : ℝ) * (((2 : ℝ) ^ L)⁻¹) ^ 2 * ((2 : ℝ) ^ j.val) ^ 2) *
              dyadicPilotSeries CE A Λ j.val (m j.val) := by
            simp only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]; ring
        _ ≤ (((anchoredDimension d CE.order : ℝ) * D) ^ 2 * (d : ℝ) * (((2 : ℝ) ^ L)⁻¹) ^ 2 * ((2 : ℝ) ^ j.val) ^ 2) * H_env :=
            mul_le_mul_of_nonneg_left (dyadicPilotSeries_le_envelope CE A Λ hΛ.le J m j) (by positivity)
        _ = _ := by dsimp [B_pt]; ring
    exact (secondMoment_dyadic_sum_le (sampleLaw θ n) J X_ml hX_ml B_pt hB_pt hE_ml).trans_eq
      (by dsimp [B_pt, dyadicMultilevelBudget]; ring)
  · intro ν hν
    let M := regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)
    let _ := regularPairDesignMeasure_isFinite CE θ hθe ((2 : ℕ) ^ L) (by positivity)
    let I := ∫ w, ν w ^ 2 ∂M
    have hI : 0 ≤ I := integral_nonneg fun _ => sq_nonneg _
    let B_ts := CE.densityUpper ^ 2 * (2 : ℝ) ^ d * ((anchoredDimension d CE.order : ℝ) * D) ^ 2 *
      (d : ℝ) * (((2 : ℝ) ^ L)⁻¹) ^ 2 * (H_env / Λ) * I
    have hB_ts : 0 ≤ B_ts := by dsimp [B_ts]; positivity
    let X_ts (j : Fin (J + 1)) (t : Fin n → Observation d) := ∫ w, ν w * dyadicPilotErrorField CE θ n j.val y (m j.val) t w ∂M
    have hf (j : Fin (J + 1)) := dyadicPilotErrorField_test_moment_facts CE θ hθe n j.val L
      ((Nat.le_of_lt_succ j.isLt).trans hJL) y hy (m j.val) (hdegree j) ν hν
    have hE_ts (j : Fin (J + 1)) : (∫ t, X_ts j t ^ 2 ∂sampleLaw θ n) ≤ B_ts * ((2 : ℝ) ^ j.val) ^ 2 := by
      have hjL : j.val ≤ L := (Nat.le_of_lt_succ j.isLt).trans hJL
      let R := m j.val + anchoredDimension d CE.order + 1
      let X_gl (i : Fin n) (z : Fin n → Observation d) := incrementGlobalVector (ℓ := CE.order) j.val (z i)
      let H (w : Covariate d × Covariate d) (r : Fin R) :=
        dyadicIncrementKernel CE θ j.val w.1 y (m j.val) (dyadicPilotRow j.val w.1 w.2) (r.val + 1)
      let rowcap := dyadicPilotRowCap d CE.order j.val L
      have hrowcap : 0 ≤ rowcap := dyadicPilotRowCap_nonneg ..
      have hcube : ∀ᵐ w ∂M, w.1 ∈ unitCube d :=
        (regularPairDesignMeasure_cube_ae CE θ hθe ((2 : ℕ) ^ L) (by positivity)).mono fun _ hw => hw.1
      have hrow := dyadicPilotRow_pair_cap (ℓ := CE.order) CE θ hθe j.val L hjL
      have hHmeas (r : Fin R) : AEStronglyMeasurable (fun w => H w r) M :=
        (dyadicIncrementKernel_field_measurable CE θ hθe j.val y (m j.val) (r.val + 1) _ (dyadicPilotRow_field_measurable j.val)).aestronglyMeasurable
      have hH (r : Fin R) : Integrable (fun w => ν w • H w r) M :=
        dyadicIncrementKernel_weighted_integrable CE θ hθe j.val y hy (m j.val) (r.val + 1) _
          (dyadicPilotRow_field_measurable j.val) M rowcap hrowcap hcube hrow ν hν
      obtain ⟨hind, hmeas, hid, hL2, hmean⟩ := incrementGlobalVector_sample_facts (ℓ := CE.order) CE θ hθe j.val
      let e (r : Fin R) := Fin.castLEEmb ((Nat.succ_le_of_lt r.isLt).trans (hdegree j))
      let Op (r : Fin R) := FieldLiftCovariance.rawKernelOperator (e r) X_gl hind hmeas hL2
      have hcaps (r : Fin R) := dyadicIncrementKernel_field_norm_bound CE θ hθe j.val y hy (m j.val) (r.val + 1) _ M rowcap hrowcap hcube hrow
      let B_c (r : Fin R) := Classical.choose (hcaps r)
      have hopcap (r : Fin R) : ∀ᵐ w ∂M, ‖Op r (H w r)‖ ≤ ‖Op r‖ * B_c r :=
        (Classical.choose_spec (hcaps r)).2.mono fun _ hw => ((Op r).le_opNorm _).trans (mul_le_mul_of_nonneg_left hw (norm_nonneg _))
      have hblock (c : Fin (Fintype.card (DyadicPilotLabelIndex d (j.val - 1)))) :
          M.real {w | dyadicPilotLabel (j.val - 1) w.1 = c} ≤ CE.densityUpper ^ 2 / dyadicPilotScale d (j.val - 1) := by
        have hs : {w : Covariate d × Covariate d | dyadicPilotLabel (j.val - 1) w.1 = c} =
            {w | regularGridCell ((2 : ℕ) ^ (j.val - 1)) (by positivity) w.1 = (Fintype.equivFin (DyadicPilotLabelIndex d (j.val - 1))).symm c} := by
          ext w; exact (Fintype.equivFin (DyadicPilotLabelIndex d (j.val - 1))).apply_eq_iff_eq_symm_apply
        rw [hs]; exact regularPairDesignMeasure_parent_block_mass CE θ hθe ((2 : ℕ) ^ L) (by positivity) j.val _
      have hu := FieldLiftCovariance.integrated_centered_lift_variance_localized
        (μ := sampleLaw θ n) (M := M) (n := n)
        (p := Fintype.card (IncrementGlobalIndex d CE.order j.val)) (R := R)
        (q := Fintype.card (DyadicPilotLabelIndex d (j.val - 1))) H ν hν hH hHmeas
        (fun w r σ v => dyadicIncrementKernel_symmetric CE θ j.val w.1 y (m j.val) (dyadicPilotRow j.val w.1 w.2) _ σ v)
        X_gl (incrementGlobalMean θ j.val) (hdegree j) hind hmeas hid hL2 hmean Λ hΛ
        (by simpa only [R, Nat.cast_add, Nat.cast_one] using hΛn j)
        (fun w => dyadicPilotLabel (j.val - 1) w.1) ((dyadicPilotLabel_measurable _).comp measurable_fst)
        (fun r => ‖Op r‖ * B_c r) (fun r => mul_nonneg (norm_nonneg (Op r)) (Classical.choose_spec (hcaps r)).1.le) hopcap
        (fun r w v hv => Eventually.of_forall fun z =>
          dyadicIncrementKernel_disjoint CE θ j.val (r.val + 1) (by omega) w.1 v.1 hv y y (m j.val) (m j.val)
            (dyadicPilotRow j.val w.1 w.2) (dyadicPilotRow j.val v.1 v.2) (fun i => z (e r i)))
        (CE.densityUpper ^ 2 / dyadicPilotScale d (j.val - 1)) hblock
      let δ (r : Fin R) := (((r.val + 1).factorial : ℝ) * Λ ^ (r.val + 1))⁻¹
      let S (w : Covariate d × Covariate d) := ∑ r : Fin R, δ r * ‖Op r (H w r)‖ ^ 2
      let P_bd := (rowcap * D) ^ 2 * dyadicPilotSeries CE A Λ j.val (m j.val)
      have hSmeas : AEStronglyMeasurable S M := by
        convert Finset.aestronglyMeasurable_sum Finset.univ (fun r _ =>
          ((Op r).continuous.comp_aestronglyMeasurable (hHmeas r)).norm.pow 2 |>.const_mul (δ r)) using 1
        funext w; simp only [S, Finset.sum_apply, Pi.pow_apply]
      have hSbound : ∀ᵐ w ∂M, S w ≤ P_bd := by
        filter_upwards [hcube, hrow] with w hw hr
        unfold S P_bd dyadicPilotSeries; rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun r _ => ?_
        have hb := hraw j.val w.1 hw (m j.val) (r.val + 1) (dyadicPilotRow j.val w.1 w.2) ((Nat.succ_le_of_lt r.isLt).trans (hdegree j))
        rw [FieldLiftCovariance.raw_kernel_operator_norm_sq (e r) X_gl hind hmeas hL2 (H w r)]
        refine hb.trans ?_
        have hprod : 0 ≤ A ^ 2 * (Fintype.card (incrementVariables (anchoredDimension d CE.order)) *
            preconditionedPilotMomentConstant CE CE.order * dyadicPilotScale d j.val) / Λ := by
          have := preconditionedPilotMomentConstant_pos CE CE.order; have := dyadicPilotScale_pos d j.val; positivity
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) hD.le) (mul_le_mul_of_nonneg_right hr hD.le) 2)
          (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hprod _))
      have hStop : MemLp S ∞ M := memLp_top_of_bound hSmeas P_bd (hSbound.mono fun w hw => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun r _ => mul_nonneg (by dsimp [δ]; positivity) (sq_nonneg _))]; exact hw)
      have hi : Integrable (fun w => ν w ^ 2 * S w) M := by
        convert hν.integrable_sq.mul_of_top_right hStop using 1; funext w; exact mul_comm _ _
      have hile := integral_mono_ae hi (hν.integrable_sq.const_mul P_bd)
        (hSbound.mono fun w hw => (mul_le_mul_of_nonneg_left hw (sq_nonneg (ν w))).trans_eq (mul_comm _ _))
      rw [integral_const_mul] at hile
      have hrhs : (∫ w, ν w ^ 2 * ∑ r : Fin R, δ r * ∫ z : Fin n → Observation d, H w r (fun i => X_gl (e r i) z) ^ 2 ∂sampleLaw θ n ∂M) =
          ∫ w, ν w ^ 2 * S w ∂M :=
        integral_congr_ae <| Eventually.of_forall fun w => congrArg (ν w ^ 2 * ·) <| Finset.sum_congr rfl fun r _ => by
          rw [← FieldLiftCovariance.raw_kernel_operator_norm_sq (e r) X_gl hind hmeas hL2 (H w r)]
      have herr : (fun z : Fin n → Observation d => ∫ w, ν w *
          LiftL2.centeredKernelExpansion 0 (H w) (fun i z => X_gl i z - incrementGlobalMean θ j.val) z ∂M) = X_ts j := by
        funext z; exact integral_congr_ae <| Eventually.of_forall fun w => congrArg (ν w * ·)
          (dyadicPolynomialPilot_centered_global CE θ hθe n j.val w.1 y (m j.val) (dyadicPilotRow j.val w.1 w.2) (hdegree j) z)
      rw [herr, hrhs] at hu
      have hts_var : variance (X_ts j) (sampleLaw θ n) ≤
          (CE.densityUpper ^ 2 / dyadicPilotScale d (j.val - 1)) * (P_bd * I) :=
        hu.trans (mul_le_mul_of_nonneg_left hile (div_nonneg (sq_nonneg _) (dyadicPilotScale_pos _ _).le))
      rw [variance_of_integral_eq_zero (hf j).1.aemeasurable (hf j).2] at hts_var
      refine hts_var.trans ?_
      change (CE.densityUpper ^ 2 / dyadicPilotScale d (j.val - 1)) *
        ((dyadicPilotRowCap d CE.order j.val L * D) ^ 2 * dyadicPilotSeries CE A Λ j.val (m j.val) * I) ≤ _
      rw [dyadicPilotRowCap_square]
      have hratio : dyadicPilotScale d j.val / dyadicPilotScale d (j.val - 1) ≤ (2 : ℝ) ^ d :=
        (div_le_iff₀ (dyadicPilotScale_pos _ _)).mpr dyadicPilotScale_parent_ratio_le
      have hs := dyadicPilotSeries_div_scale_le_envelope CE A Λ hΛ J m j
      have hsnon := div_nonneg (dyadicPilotSeries_nonneg CE A Λ hΛ.le j.val (m j.val)) (dyadicPilotScale_pos d j.val).le
      calc _ = (CE.densityUpper ^ 2 * ((anchoredDimension d CE.order : ℝ) * D) ^ 2 * (d : ℝ) * (((2 : ℝ) ^ L)⁻¹) ^ 2 * ((2 : ℝ) ^ j.val) ^ 2) *
              (dyadicPilotScale d j.val / dyadicPilotScale d (j.val - 1)) *
              (dyadicPilotSeries CE A Λ j.val (m j.val) / dyadicPilotScale d j.val) * I := by
            field_simp [(dyadicPilotScale_pos d j.val).ne', (dyadicPilotScale_pos d (j.val - 1)).ne']
        _ ≤ (CE.densityUpper ^ 2 * ((anchoredDimension d CE.order : ℝ) * D) ^ 2 * (d : ℝ) * (((2 : ℝ) ^ L)⁻¹) ^ 2 * ((2 : ℝ) ^ j.val) ^ 2) *
              ((2 : ℝ) ^ d) * (H_env / Λ) * I :=
            mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left hratio (by positivity)) hs hsnon (by positivity)) hI
        _ = _ := by dsimp [B_ts]; ring
    have h := secondMoment_dyadic_sum_le (sampleLaw θ n) J X_ts (fun j => (hf j).1) B_ts hB_ts hE_ts
    have heq_sum (t : Fin n → Observation d) : ∑ j, X_ts j t = ∫ w, ν w * dyadicMultilevelErrorField CE θ n J y m t w ∂M :=
      (dyadicMultilevelErrorField_test_integral_sum CE θ hθe n J L hJL y hy m hdegree ν hν t).symm
    simp_rw [heq_sum] at h
    exact h.trans_eq (by dsimp [B_ts, dyadicMultilevelBudget]; ring)

private theorem uniform_domain_multilevel_bounds {d : ℕ} (C : ModelConstants d)
    [Nonempty (AnchoredIndex d C.order)] :
    ∃ D A : ℝ, 0 < D ∧ 0 < A ∧ ∀ U : ExtensionDomain d, ∀ θ : RegressionParameter d, Admissible (C.withDomain U) θ →
      ∀ n J L : ℕ, J ≤ L → ∀ y : ℝ, |y| ≤ max C.holderBound 1 → ∀ m : ℕ → ℕ,
      (∀ j : Fin (J + 1), m j.val + anchoredDimension d C.order + 1 ≤ n) →
      ∀ Λ : ℝ, 0 < Λ →
      (∀ j : Fin (J + 1), Λ ≤ (n : ℝ) - (m j.val + anchoredDimension d C.order + 1) + 1) →
      (∀ x ∈ unitCube d, ∀ z ∈ unitCube d,
        regularGridCell ((2 : ℕ) ^ L) (by positivity) x = regularGridCell ((2 : ℕ) ^ L) (by positivity) z →
        (∫ t, dyadicMultilevelErrorField C θ n J y m t (x, z) ^ 2 ∂sampleLaw θ n) ≤
          4 * ((anchoredDimension d C.order : ℝ) * D) ^ 2 * (d : ℝ) *
            dyadicMultilevelBudget (dyadicSeriesEnvelope (pilotModelConstants C) A Λ J m) J L) ∧
      (∀ ν : Covariate d × Covariate d → ℝ,
        MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)) →
        (∫ t, (∫ w, ν w * dyadicMultilevelErrorField C θ n J y m t w
          ∂regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)) ^ 2 ∂sampleLaw θ n) ≤
          (4 * C.densityUpper ^ 2 * (2 : ℝ) ^ d *
            ((anchoredDimension d C.order : ℝ) * D) ^ 2 * (d : ℝ) *
              dyadicMultilevelBudget (dyadicSeriesEnvelope (pilotModelConstants C) A Λ J m) J L / Λ) *
            (∫ w, ν w ^ 2 ∂regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity))) := by
  letI : Nonempty (AnchoredIndex d (pilotModelConstants C).order) := inferInstanceAs (Nonempty (AnchoredIndex d C.order))
  obtain ⟨D, A, hD, hA, hder_vec⟩ := uniform_domain_increment_vector_derivative_bound
    (pilotModelConstants C) (pilotModelConstants C).holderBound (pilotModelConstants C).holderBound_pos.le
  refine ⟨D, A, hD, hA, fun U θ hθ n J L hJL y hy m hdegree Λ hΛ hΛn => ?_⟩
  letI : Nonempty (AnchoredIndex d ((pilotModelConstants C).withDomain U).order) :=
    inferInstanceAs (Nonempty (AnchoredIndex d C.order))
  have hθe : Admissible ((pilotModelConstants C).withDomain U) θ := admissible_pilotModelConstants (C.withDomain U) θ hθ
  exact multilevel_bounds_of_deriv ((pilotModelConstants C).withDomain U) θ hθe D A hD hA n J L hJL y hy m hdegree Λ hΛ hΛn
    fun j x hx m_j k row => by
      have hrow0 : 0 ≤ ∑ i, |row i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun dirs => ?_
      rw [incrementFinScalar_iteratedFDeriv]
      calc _ ≤ ‖rowFunctional row‖ * ‖iteratedFDeriv ℝ k
              (incrementFinVector (anchoredDimension d C.order) C.densityLower C.densityUpper
                (anchoredFinTransport d C.order) y m_j) (dyadicIncrementRawMean θ j x) dirs‖ := (rowFunctional row).le_opNorm _
        _ ≤ (∑ i, |row i|) * (D * (k.factorial : ℝ) * A ^ k * ∏ i, ‖dirs i‖) :=
            mul_le_mul (rowFunctional_norm_le row) (hder_vec U θ hθe j x hx y hy m_j k dirs) (norm_nonneg _) hrow0
        _ = _ := by ring

-- 5. Borel observable raw coefficients & main sharp upper theorem

private def dyadicRawPilotSum {d : ℕ} (C : ModelConstants d) (n J : ℕ) (m : ℕ → ℕ)
    (y : ℝ) (z : Fin n → Observation d) (w : Covariate d × Covariate d) : ℝ :=
  ∑ j : Fin (J + 1), dyadicPolynomialPilot C n j.val w.1 y (m j.val) (dyadicPilotRow j.val w.1 w.2) z

private def dyadicRawCoefficients {d : ℕ} (C : ModelConstants d) (n J : ℕ) (m : ℕ → ℕ)
    (z : Fin n → Observation d) (w : Covariate d × Covariate d) : PairVector :=
  WithLp.toLp 2 ![1, -1 + (dyadicRawPilotSum C n J m 0 z w - dyadicRawPilotSum C n J m 1 z w),
    -dyadicRawPilotSum C n J m 0 z w]

private def polynomialLiftLinearMap {Ω : Type*} {n p : ℕ}
    (X : Fin n → Ω → Fin p → ℝ) (z : Ω) : MvPolynomial (Fin p) ℝ →ₗ[ℝ] ℝ where
  toFun P := Finsupp.linearCombination ℝ (fun α =>
    RoughRegime.Upper.monomialLift (RoughRegime.Upper.exponentCoordinates α) X z) P.coeff
  map_add' _ _ := by simp only [AddMonoidAlgebra.coeff_add, map_add]
  map_smul' _ _ := by simp only [AddMonoidAlgebra.coeff_smul, map_smul, RingHom.id_apply]

private theorem rowIncrementPolynomial_lift {Ω : Type*} {n r : ℕ}
    (a b : ℝ) (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m : ℕ) (row : Fin r → ℝ)
    (X : Fin n → Ω → Fin (Fintype.card (incrementVariables r)) → ℝ) (z : Ω) :
    RoughRegime.Upper.polynomialLift (rowIncrementPolynomial r a b T y m row) X z =
      ∑ i, row i * RoughRegime.Upper.polynomialLift (incrementFinPolynomial r a b T y m i) X z := by
  have hlin (P) : RoughRegime.Upper.polynomialLift P X z = polynomialLiftLinearMap X z P := rfl
  simp only [hlin, rowIncrementPolynomial, ← MvPolynomial.smul_eq_C_mul, map_sum, map_smul, smul_eq_mul]

attribute [local irreducible] dyadicIncrementRawVector in
set_option backward.isDefEq.respectTransparency true in
private theorem dyadicRawCoefficients_joint_measurable {d : ℕ} (C : ModelConstants d) (n J : ℕ) (m : ℕ → ℕ) :
    Measurable fun t : (Fin n → Observation d) × (Covariate d × Covariate d) => dyadicRawCoefficients C n J m t.1 t.2 := by
  have hp_meas (y : ℝ) : Measurable fun t : (Fin n → Observation d) × (Covariate d × Covariate d) => dyadicRawPilotSum C n J m y t.1 t.2 := by
    refine Finset.measurable_sum Finset.univ fun j _ => ?_
    let X : Fin n → (Fin n → Observation d) × (Covariate d × Covariate d) →
        Fin (Fintype.card (incrementVariables (anchoredDimension d C.order))) → ℝ :=
      fun i t => dyadicIncrementRawVector (d := d) (ℓ := C.order) j.val t.2.1 (t.1 i)
    have hX (i : Fin n) : Measurable (X i) :=
      (dyadicIncrementRawVector_joint_measurable (d := d) (ℓ := C.order) j.val).comp
        ((measurable_fst.comp measurable_snd).prodMk ((measurable_pi_apply i).comp measurable_fst))
    have hrow : Measurable fun w : Covariate d × Covariate d => dyadicPilotRow (ℓ := C.order) j.val w.1 w.2 :=
      dyadicPilotRow_field_measurable j.val
    have heq : (fun t : (Fin n → Observation d) × (Covariate d × Covariate d) =>
        dyadicPolynomialPilot C n j.val t.2.1 y (m j.val) (dyadicPilotRow j.val t.2.1 t.2.2) t.1) =
        fun t => ∑ i, dyadicPilotRow j.val t.2.1 t.2.2 i * RoughRegime.Upper.polynomialLift
          (incrementFinPolynomial (anchoredDimension d C.order) C.densityLower C.densityUpper
            (anchoredFinTransport d C.order) y (m j.val) i) X t := by
      funext t
      simp only [dyadicPolynomialPilot, rowIncrementPolynomial_lift]
      rfl
    rw [heq]
    refine Finset.measurable_sum _ fun i _ => ((hrow.eval (a := i)).comp measurable_snd).mul ?_
    classical
    unfold RoughRegime.Upper.polynomialLift RoughRegime.Upper.monomialLift
    exact Finset.measurable_sum _ fun _ _ => Measurable.const_mul (Measurable.const_mul
      (Finset.measurable_sum _ fun e _ => Finset.measurable_prod Finset.univ fun l _ => (hX (e l)).eval) _) _
  refine (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).measurable.comp (measurable_pi_iff.mpr fun i => ?_)
  fin_cases i
  · exact measurable_const
  · exact measurable_const.add ((hp_meas 0).sub (hp_meas 1))
  · exact (hp_meas 0).neg

theorem paper_upper_sharp {d : ℕ} (C : ModelConstants d) : UpperSharpClaim C := by
  intro hreg
  letI : Nonempty (AnchoredIndex d C.order) := anchoredIndex_nonempty_of_one_lt_smoothness C hreg.1
  let CP := pilotModelConstants C
  obtain ⟨Cp₀, E_res, hCp₀, hE_res, hbar, hres_bd⟩ := uniform_domain_population_bounds C hreg.1
  obtain ⟨D_ml, A, hD_ml, hA, hb_ml⟩ := uniform_domain_multilevel_bounds C
  let point : ℝ := 4 * ((anchoredDimension d C.order : ℝ) * D_ml) ^ 2 * (d : ℝ)
  let test : ℝ := 4 * C.densityUpper ^ 2 * (2 : ℝ) ^ d * ((anchoredDimension d C.order : ℝ) * D_ml) ^ 2 * (d : ℝ)
  let Cp : ℝ := max Cp₀ (max 1 (5 * point + 72 * test + 1))
  have hp0 : 0 ≤ point := by dsimp [point]; positivity
  have ht0 : 0 ≤ test := by dsimp [test]; positivity
  have hCp₀le : Cp₀ ≤ Cp := le_max_left _ _
  have hC1 : 1 ≤ Cp := (le_max_left _ _).trans (le_max_right _ _)
  have hCall : 5 * point + 72 * test + 1 ≤ Cp := (le_max_right _ _).trans (le_max_right _ _)
  have hCp : 0 < Cp := zero_lt_one.trans_le hC1
  have hpoint : 5 * point ≤ Cp := by linarith only [hCall, ht0]
  have htest : 72 * test ≤ Cp ^ 2 := (show 72 * test ≤ Cp by linarith only [hCall, hp0]).trans (by nlinarith only [hC1])
  let C₀ := max 1 (12 * paperPilotMomentFactor CP A)
  let C_D := max 1 (4 * paperDegreeSlope C)
  have hC : 1 ≤ C₀ := le_max_left _ _
  have hD : 1 ≤ C_D := le_max_left _ _
  have hH : 0 < C₀ * C_D := mul_pos (zero_lt_one.trans_le hC) (zero_lt_one.trans_le hD)
  let H := C₀ * C_D
  obtain ⟨B_bias, hB_bias, hbias_bud⟩ := eventually_paper_dyadic_bias_budget C hreg.1
    (paperUpperSaddle C) (paperUpperShift C) H (paperUpperSaddle_pos C hreg) hH
  let B := E_res * B_bias
  have hB : 0 < B := mul_pos hE_res hB_bias
  obtain ⟨S, hS, hscale⟩ := paper_allocated_risk_scale_upper C hreg hH
  let K := Real.sqrt (pairRateSquaredConstant C Cp (1 / 4) (1 / 4)) * paperAllocatedMasterConstant C B * S
  have hK : 0 < K := mul_pos (mul_pos
    (Real.sqrt_pos.mpr (pairRateSquaredConstant_pos C hCp.le (by norm_num) (by norm_num)))
    (paperAllocatedMasterConstant_pos C B)) hS
  have hall : ∀ᶠ n : ℕ in atTop, ∀ U : ExtensionDomain d,
      minimaxRMS (C.withDomain U) n ≤ ENNReal.ofReal (K * paperUpperScale C n) := by
    filter_upwards [
      tendsto_natCast_atTop_atTop.eventually ((eventually_paper_allocated_grid_guard C hreg hH).mono fun _ h => h.2),
      eventually_paper_degree_three_block_guards C hreg.1 (paperUpperSaddle C) (paperUpperShift C) H (paperUpperSaddle_pos C hreg) hH,
      tendsto_natCast_atTop_atTop.eventually hbias_bud,
      hscale,
      eventually_paperAllocatedPilotBudget_le_one CP hreg A C₀ C_D hC hD (le_max_right _ _) (le_max_right _ _),
      eventually_paper_allocated_master_rate C hreg hH B,
      eventually_ge_atTop (6 : ℕ)] with n hg hdeg hbn hscalen hWn hmastern hn6
    intro U
    let J := paperDyadicTerminalLevel C (paperUpperSaddle C) (paperUpperShift C) H n
    let m := paperDyadicApproximationDegree C (paperUpperSaddle C) (paperUpperShift C) H n
    let L := paperAllocatedFinestLevel C H n
    let k := (2 : ℕ) ^ L
    let N := threeBlockSize n
    let W := paperAllocatedPilotBudget CP A C₀ C_D n
    let c := dyadicRawCoefficients C N J m
    have hmc := dyadicRawCoefficients_joint_measurable C N J m
    let T := coefficientPairEstimator (C.withDomain U) k (by dsimp only [k]; positivity) c hmc
    refine minimaxRMS_le_of_estimator_rms (C.withDomain U) T fun θ hθ => ?_
    let CU := C.withDomain U
    let CE := CP.withDomain U
    letI : Nonempty (AnchoredIndex d CU.order) := inferInstanceAs (Nonempty (AnchoredIndex d C.order))
    letI : Nonempty (AnchoredIndex d CE.order) := inferInstanceAs (Nonempty (AnchoredIndex d C.order))
    have hθe : Admissible CE θ := admissible_pilotModelConstants CU θ hθ
    let _ := sampleLaw_isProbability CU θ hθ N
    let _ := designLaw_isProbability CU θ hθ
    let bar := dyadicPopulationCoefficients C θ J m
    let η : (Fin N → Observation d) → Covariate d × Covariate d → PairVector :=
      fun z w => twoScalarPilotVector (dyadicMultilevelErrorField C θ N J 0 m z w)
        (dyadicMultilevelErrorField C θ N J 1 m z w)
    have heq : c = pairPilotCoefficient bar η := by
      funext z w
      have herr_eq (y : ℝ) : dyadicMultilevelErrorField C θ N J y m z w = dyadicRawPilotSum C N J m y z w -
          (dyadicPopulationPilotSum C θ J m false w - y * dyadicPopulationPilotSum C θ J m true w) := by
        unfold dyadicMultilevelErrorField dyadicPilotErrorField dyadicRawPilotSum
        rw [Finset.sum_sub_distrib]
        congr 1
        unfold dyadicPopulationPilotSum
        rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range, Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [incrementFinScalar, incrementFinVector_affine]
        simp only [rowFunctional, _root_.sum_apply, _root_.smul_apply, ContinuousLinearMap.proj_apply,
          dotProduct, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, dyadicPopulationRawPolynomial,
          mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
        congr 1; exact Finset.sum_congr rfl fun _ _ => by ring
      ext i; fin_cases i <;>
        simp [c, bar, η, pairPilotCoefficient, dyadicRawCoefficients, dyadicPopulationCoefficients,
          twoScalarPilotVector_coordinates, herr_eq] <;> ring
    -- Build `PairPilotAssumptions`
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    let Λ := (N : ℝ) / 2
    have hΛ : 0 < Λ := (hdeg 0 (Nat.zero_le _)).2.1
    have hΛn : (n : ℝ) / 12 ≤ Λ := by have hf := threeBlockSize_fraction hn6; dsimp [Λ, N]; linarith only [hf, hn_pos]
    have hd_j (j : Fin (J + 1)) : m j.val + anchoredDimension d C.order + 1 ≤ N := (hdeg j.val (Nat.le_of_lt_succ j.isLt)).1
    have hΛd (j : Fin (J + 1)) : Λ ≤ (N : ℝ) - (m j.val + anchoredDimension d C.order + 1) + 1 := by
      simpa only [paperDyadicTotalDegree, Nat.cast_add, Nat.cast_one, m, Λ, N] using (hdeg j.val (Nat.le_of_lt_succ j.isLt)).2.2
    let W_raw := dyadicMultilevelBudget (dyadicSeriesEnvelope CP A Λ J m) J L
    have hW_raw0 : 0 ≤ W_raw := mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (dyadicSeriesEnvelope_nonneg _ _ _ hΛ.le _ _)
    have hy0 : |(0 : ℝ)| ≤ max C.holderBound 1 := by simpa only [abs_zero] using zero_le_one.trans (le_max_right C.holderBound 1)
    have hy1 : |(1 : ℝ)| ≤ max C.holderBound 1 := by simpa only [abs_one] using le_max_right C.holderBound 1
    have hbounds (y : ℝ) (hy : |y| ≤ max C.holderBound 1) := hb_ml U θ hθ N J L hg y hy m hd_j Λ hΛ hΛd
    have hcubes : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ), w.1 ∈ unitCube d ∧ w.2 ∈ unitCube d := by
      filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := designLaw θ) (ν := designLaw θ)).ae (designLaw_cube_ae θ),
        (Measure.quasiMeasurePreserving_snd (μ := designLaw θ) (ν := designLaw θ)).ae (designLaw_cube_ae θ)] with _ hx hz
      exact ⟨hx, hz⟩
    have hf_pt (y : ℝ) (w : Covariate d × Covariate d) (hx : w.1 ∈ unitCube d) :=
      dyadicMultilevelErrorField_point_moment_facts CU θ hθ N J w.1 hx w.2 y m hd_j
    have hsections : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
        sameLabelKernel (regularGridCell k (by dsimp only [k]; positivity)) w ≠ 0 →
          MemLp (fun z => dyadicMultilevelErrorField C θ N J 0 m z w) 2 (sampleLaw θ N) ∧
          MemLp (fun z => dyadicMultilevelErrorField C θ N J 1 m z w) 2 (sampleLaw θ N) :=
      hcubes.mono fun w hw _ => ⟨(hf_pt 0 w hw.1).1, (hf_pt 1 w hw.1).1⟩
    have henergy : ∀ᵐ w ∂(designLaw θ).prod (designLaw θ),
        sameLabelKernel (regularGridCell k (by dsimp only [k]; positivity)) w ≠ 0 →
          (∫ z, dyadicMultilevelErrorField C θ N J 0 m z w ^ 2 ∂sampleLaw θ N) ≤ point * W_raw ∧
          (∫ z, dyadicMultilevelErrorField C θ N J 1 m z w ^ 2 ∂sampleLaw θ N) ≤ point * W_raw := by
      filter_upwards [hcubes] with w hw hs
      have hc : regularGridCell ((2 : ℕ) ^ L) (by positivity) w.1 = regularGridCell ((2 : ℕ) ^ L) (by positivity) w.2 := by
        by_contra h; exact hs (by simp [sameLabelKernel, k, h])
      exact ⟨(hbounds 0 hy0).1 w.1 hw.1 w.2 hw.2 hc, (hbounds 1 hy1).1 w.1 hw.1 w.2 hw.2 hc⟩
    have hcenter : ∀ᵐ w ∂regularPairDesignMeasure θ k (by dsimp only [k]; positivity),
        (∫ z, dyadicMultilevelErrorField C θ N J 0 m z w ∂sampleLaw θ N) = 0 ∧
        (∫ z, dyadicMultilevelErrorField C θ N J 1 m z w ∂sampleLaw θ N) = 0 :=
      (regularPairDesignMeasure_cube_ae CU θ hθ k (by dsimp only [k]; positivity)).mono fun w hw =>
        ⟨(hf_pt 0 w hw.1).2, (hf_pt 1 w hw.1).2⟩
    have hw_int (y : ℝ) (hy : |y| ≤ max C.holderBound 1) (ν) (hν : MemLp ν 2 (regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity))) (t) :
        Integrable (fun w => ν w * dyadicMultilevelErrorField C θ N J y m t w) (regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity)) := by
      convert integrable_finsetSum Finset.univ (fun j _ => dyadicPilotErrorField_weighted_integrable CE θ hθe N j.val L
        ((Nat.le_of_lt_succ j.isLt).trans hg) y hy (m j.val) (hd_j j) ν hν t) using 1
      funext w; simp only [dyadicMultilevelErrorField, Finset.mul_sum]; rfl
    have hpr_raw := (pairPilotAssumptions_of_two_scalars (sampleLaw θ N) θ ((2 : ℕ) ^ L) (by positivity) bar
      (dyadicMultilevelErrorField C θ N J 0 m) (dyadicMultilevelErrorField C θ N J 1 m)
      hCp.le hW_raw0 ht0 hΛ hpoint
      (dyadicPopulationCoefficients_measurable CU θ hθ J m)
      (dyadicMultilevelErrorField_joint_measurable CU θ hθ N J 0 m hd_j)
      (dyadicMultilevelErrorField_joint_measurable CU θ hθ N J 1 m hd_j)
      ((hbar U θ hθ J L hg m).mono fun _ hw hs => (hw hs).trans hCp₀le)
      hsections henergy hcenter
      (hw_int 0 hy0) (hw_int 1 hy1)
      (fun v hv => (dyadicMultilevelErrorField_test_moment_facts CE θ hθe N J L hg 0 hy0 m hd_j v hv).1)
      (fun v hv => (dyadicMultilevelErrorField_test_moment_facts CE θ hθe N J L hg 1 hy1 m hd_j v hv).1)
      (hbounds 0 hy0).2 (hbounds 1 hy1).2).mono_lam
        (scalarPilot_covariance_sample_budget hn_pos hW_raw0 ht0 hΛn htest)
    have hpr : PairPilotAssumptions θ k (by dsimp only [k]; positivity) (sampleLaw θ N) bar η Cp W (Cp ^ 2 * W / (n : ℝ)) :=
      hpr_raw
    have hfirst : ∀ᵐ w ∂regularPairDesignMeasure θ k (by dsimp only [k]; positivity), bar w 0 = 1 :=
      Eventually.of_forall fun _ => rfl
    have hres_ae : ∀ᵐ w ∂regularPairDesignMeasure θ k (by dsimp only [k]; positivity),
        |⟪bar w, pairResponseVector (θ.regression w.1) (θ.regression w.2)⟫| ≤
          B * Real.sqrt (d : ℝ) * paperAllocatedSide C H n * (dyadicPilotScale d J) ^ (-paperSpatialExponent C) := by
      have hcell_ae : ∀ᵐ w ∂regularPairDesignMeasure θ ((2 : ℕ) ^ L) (by positivity), w.2 ∈ dyadicPilotCell L w.1 := by
        apply regularPairDesignMeasure_ae_of_supported
        filter_upwards [] with w hw
        change regularGridCell ((2 : ℕ) ^ L) (by positivity) w.2 = regularGridCell ((2 : ℕ) ^ L) (by positivity) w.1
        by_contra h; exact hw (by simp [sameLabelKernel, Ne.symm h])
      filter_upwards [regularPairDesignMeasure_cube_ae CU θ hθ k (by dsimp only [k]; positivity), hcell_ae] with w hw hc
      dsimp [bar]; rw [dyadicPopulationCoefficients_residual]
      have hr : euclideanNorm (w.2 - w.1) ≤ Real.sqrt (d : ℝ) * ((2 : ℝ) ^ L)⁻¹ := by
        simpa [Nat.cast_pow, one_div] using euclideanNorm_le_coordinate_radius (w.2 - w.1)
          (1 / (((2 : ℕ) ^ L : ℕ) : ℝ)) (by positivity)
          (regular_grid_same_cell_radius ((2 : ℕ) ^ L) (by positivity) w.2 w.1 hw.2 hw.1 hc)
      have h1 := (hres_bd U θ hθ J m w.1 hw.1 w.2 hw.2 (dyadicPilotCell_subset_coarser J L hg w.1 hc)).trans
        (mul_le_mul_of_nonneg_left hbn (mul_nonneg hE_res.le (Real.sqrt_nonneg _)))
      have h2 := h1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr hE_res.le)
        (mul_nonneg hB_bias.le (Real.rpow_nonneg (dyadicPilotScale_pos _ _).le _)))
      rw [paperAllocatedSide, dyadicRoundedSide_eq_inv_pow,
        show dyadicLevelFromLogSide (paperAllocatedLogSide C H n) = L from rfl]
      exact h2.trans_eq (by dsimp [B]; ring)
    refine (coefficientPairEstimator_rms_bound CU θ hθ hn6 k (by dsimp only [k]; positivity) c hmc bar η Cp W
      (B * Real.sqrt (d : ℝ) * paperAllocatedSide C H n * (dyadicPilotScale d J) ^ (-paperSpatialExponent C))
      heq hpr hfirst hres_ae).trans (ENNReal.ofReal_mono ?_)
    have hw0 : 0 ≤ W := paperAllocatedPilotBudget_nonneg CP A C₀ C_D n
    have hPC : 0 ≤ Real.sqrt (pairRateSquaredConstant C Cp (1 / 4) (1 / 4)) := Real.sqrt_nonneg _
    have hMC : 0 ≤ paperAllocatedMasterConstant C B := (paperAllocatedMasterConstant_pos C B).le
    calc _ ≤ Real.sqrt (pairRateSquaredConstant C Cp (1 / 4) (1 / 4)) *
            (paperAllocatedMasterConstant C B * paperAllocatedRiskScale C H n) :=
          mul_le_mul_of_nonneg_left (hmastern W hw0 hWn) hPC
      _ = (Real.sqrt (pairRateSquaredConstant C Cp (1 / 4) (1 / 4)) * paperAllocatedMasterConstant C B) *
            paperAllocatedRiskScale C H n := by ring
      _ ≤ (Real.sqrt (pairRateSquaredConstant C Cp (1 / 4) (1 / 4)) * paperAllocatedMasterConstant C B) *
            (S * paperUpperScale C n) := mul_le_mul_of_nonneg_left hscalen (mul_nonneg hPC hMC)
      _ = K * paperUpperScale C n := by dsimp only [K]; ring
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hall
  exact ⟨K, hK, max 2 n₀, le_max_left _ _, fun U n hn => hn₀ n ((le_max_right _ _).trans hn) U⟩

end NearlyMinimax

