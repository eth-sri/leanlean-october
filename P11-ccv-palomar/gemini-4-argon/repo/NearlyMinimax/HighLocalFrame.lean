module
public import NearlyMinimax.HighWindowGeometry
public import NearlyMinimax.ActualSeparatedPacket
public import NearlyMinimax.HighFrameCoefficientBridge
public import Mathlib.MeasureTheory.Function.Floor
@[expose] public section
noncomputable section
open MeasureTheory Set Polynomial ProbabilityTheory Function MvPolynomial
open scoped BigOperators ContDiff
namespace NearlyMinimax
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section Packet
variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
def highDensityResponseAction (q : ℕ) (C : ℝ) (weights : E → ℝ)
    (A : E → ι → ι → ℝ) (c : ι → ℝ) (b : E → ℝ)
    (Φ : (ι → ℝ) → ℝ) : ℝ :=
  ∑ e, weights e * b e * responseMatrixAction q C (A e) c Φ
def highResponsePacketCost (C : ℝ) (weights : E → ℝ) (A : E → ι → ι → ℝ) : ℝ :=
  ∑ e, |weights e| * (2 * C ^ 2 * ∑ k, ∑ l, |A e k l|)
def highLocalDerivativeConstant (q : ℕ) (a ρ : ℝ) : ℝ :=
  (∑ j : Fin (2 * q + 2), |responseWeight q j|) *
    4 * (((2 * ρ + a) / a ^ 2) ^ 2 + 2 / a ^ 2)
theorem finite_density_product_abs_bound {n : ℕ} (p : Fin n → ℝ) (pPlus : ℝ)
    (_hpPlus : 0 ≤ pPlus) (hp : ∀ i, |p i| ≤ pPlus) :
    |∏ i, p i| ≤ pPlus ^ n := by
  rw [Finset.abs_prod]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    Finset.prod_le_prod₀ (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => abs_nonneg (p i))
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hp i)
theorem high_response_variance_term_abs_bound  (a V η ) (ha : 0 < a)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hp : ∀ i u, 0 ≤ ternaryMass a (coefficientRegression η g w φ c i) V u)
    (y : Fin n → Fin 3) (i : Fin n) :
    |highResponseVarianceTerm a V η g w φ c y i| ≤ 1 / a ^ 2 := by
  have hprod : |∏ l ∈ (Finset.univ : Finset (Fin n)).erase i,
      ternaryMass a (coefficientRegression η g w φ c l) V (y l)| ≤ 1 := by
    rw [Finset.abs_prod]
    apply (Finset.prod_le_prod₀ (fun l _ => abs_nonneg _)
      (fun l _ => show |ternaryMass a (coefficientRegression η g w φ c l) V (y l)| ≤ 1 from by
        rw [abs_of_nonneg (hp l (y l))]
        exact ternary_mass_le_one a _ V ha.ne' (hp l) (y l))).trans_eq
    exact Finset.prod_const_one
  unfold highResponseVarianceTerm
  rw [abs_mul]
  exact (mul_le_mul (ternary_variance_derivative_abs_bound a ha (y i)) hprod
    (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
theorem high_density_response_product_abs_bound  (q ) (hn : 1 ≤ n)
    (C a V η ρ pPlus ) (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η)
    (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ / 2) (hpPlus : 0 ≤ pPlus)
    (weights A) (pReset : E → Fin n → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ)
    (hc : ∑ k, |c k| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ / 2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : ι → ℝ, (∑ k, |v k|) ≤ C⁻¹ → ∀ i, |∑ k, φ i k * v k| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ u, 0 ≤ ternaryMass a f V u)
    (hReset : ∀ e i, |pReset e i| ≤ pPlus) (y : Fin n → Fin 3) :
    |highDensityResponseAction q C weights A c (fun e => ∏ i, pReset e i)
      (fun c => highResponseProduct a V η g w φ c y)| ≤
      pPlus ^ n * highResponsePacketCost C weights A *
        (highLocalDerivativeConstant q a ρ * n ^ 2 * η ^ 2) := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ e, (|weights e| * pPlus ^ n) *
        ((2 * C ^ 2 * ∑ k, ∑ l, |A e k l|) *
          highLocalDerivativeConstant q a ρ * n ^ 2 * η ^ 2) := by
      apply Finset.sum_le_sum
      intro e _
      rw [abs_mul, abs_mul]
      apply mul_le_mul
        (mul_le_mul_of_nonneg_left
          (finite_density_product_abs_bound (pReset e) pPlus hpPlus (hReset e)) (abs_nonneg _))
        _ (abs_nonneg _) (by positivity)
      exact (high_response_matrix_all_count_bound q hn C a V η ρ hC ha hη hρ hηρ
        (A e) g w φ c y hc hg hw hφ hp).trans_eq (by
          unfold highLocalDerivativeConstant
          ring)
    _ = _ := by
      unfold highResponsePacketCost
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      ring
end Packet
section FinitePacket
variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]
theorem high_response_variance_ratio  (a V η g w φ) (c : ι → ℝ)
    (y : Fin n → Fin 3) (i : Fin n)
    (hp : ∀ k, 0 < ternaryMass a (coefficientRegression η g w φ c k) V (y k)) :
    highResponseVarianceTerm a V η g w φ c y i / highResponseProduct a V η g w φ c y =
      ternaryVarianceDerivative a (y i) /
        ternaryMass a (coefficientRegression η g w φ c i) V (y i) := by
  unfold highResponseVarianceTerm highResponseProduct
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  exact mul_div_mul_right _ _ (ne_of_gt (Finset.prod_pos (fun k _ => hp k)))
end FinitePacket
theorem local_response_scores_orthogonal 
    (μ ) [∀ i, IsProbabilityMeasure (μ i)]
    (r s : (Fin n → Fin 3) → ℝ) (S T : Finset (Fin n)) (hST : Disjoint S T)
    (hr : ∀ y y', (∀ i ∈ S, y i = y' i) → r y = r y')
    (hs : ∀ y y', (∀ i ∈ T, y i = y' i) → s y = s y')
    (hc : (∫ y, r y ∂Measure.pi μ) = 0) :
    (∫ y, r y * s y ∂Measure.pi μ) = 0 := by
  let R (y : S → Fin 3) := r (extendPatchResponses n S y)
  let Q (y : T → Fin 3) := s (extendPatchResponses n T y)
  have hR (y : Fin n → Fin 3) : r y = R (fun i : S => y i) := by
    apply hr
    intro i hi
    simp [extendPatchResponses, hi]
  have hQ (y : Fin n → Fin 3) : s y = Q (fun i : T => y i) := by
    apply hs
    intro i hi
    simp [extendPatchResponses, hi]
  simp_rw [hR, hQ]
  exact finite_product_local_scores_orthogonal n μ S T hST R Q (by simpa only [← hR] using hc)
section IntegratedPacket
variable {ι E Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [MeasurableSpace Z]
end IntegratedPacket
section Family
variable {J ι E Z : Type*} [Fintype J] [Fintype ι] [DecidableEq ι]
  [Fintype E] [MeasurableSpace Z]
end Family
def highPatchSampleIndices (d k n ) (j : HighWindowLabels d k)
    (x : Fin n → Covariate d) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i ∈ highTorusPatch d k j)
theorem highPatchSampleIndices_disjoint (d k n ) [NeZero k]
    (x j l)
    (hjl : l ∉ highNeighborLabels d k j) :
    Disjoint (highPatchSampleIndices d k n j x) (highPatchSampleIndices d k n l x) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact Set.disjoint_left.mp (highTorusPatch_disjoint_of_not_neighbor d k j l hjl)
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
theorem highPeriodicTensor_sample_zero_outside_patch (d k n j x i)
    (hi : i ∉ highPatchSampleIndices d k n j x) :
    highPeriodicTensor d k j (x i) = 0 := by
  by_contra h
  exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, highPeriodicTensor_supported_patch d k j h⟩)
def highFrameMonomial  (γ : HighFrameIndex d D) : MvPolynomial (Fin d) ℝ :=
  MvPolynomial.monomial (polynomialBoxExponent γ.val) 1
theorem highPeriodizedFrame_evaluation (d k D j)
    (c : HighFrameIndex d D → ℝ) (x : Covariate d) :
    highPeriodizedChart d k j (highFrameProfile (highFramePolynomial c)) x =
      ∑ γ, c γ * highPeriodizedChart d k j (highFrameProfile (highFrameMonomial γ)) x := by
  have hfinite (γ : HighFrameIndex d D) : HasFiniteSupport (fun z : Fin d → ℤ =>
      c γ * (if (∀ r, (z r : ZMod k) = j r) then
        highFrameProfile (highFrameMonomial γ) (fun r => k * x r - z r) else 0)) := by
    apply HasFiniteSupport.mul_right (fun _ => c γ)
    exact (highPeriodizedChart_locallyFinite d k j _
      (highFrameProfile_zero_of_window_zero (highFrameMonomial γ))).point_finite x
  unfold highPeriodizedChart
  calc
    _ = ∑ᶠ z : Fin d → ℤ, ∑ γ : HighFrameIndex d D,
        c γ * (if (∀ r, (z r : ZMod k) = j r) then
          highFrameProfile (highFrameMonomial γ) (fun r => k * x r - z r) else 0) := by
      apply finsum_congr
      intro z
      by_cases hz : ∀ r, (z r : ZMod k) = j r
      · simp only [ite_eq_left hz]
        have h_highFrameProfile_evaluation (x : Covariate d) : highFrameProfile (highFramePolynomial c) x =
            ∑ γ, c γ * highFrameProfile (highFrameMonomial γ) x := by
          unfold highFrameProfile
          have h_highFramePolynomial_scaled_eval : MvPolynomial.eval x (frameScaledPolynomial (highFramePolynomial c)) =
              ∑ γ, c γ * highFrameFeature x γ := by
            classical
            rw [frameScaledPolynomial_eval]
            simp only [highFramePolynomial, map_sum, MvPolynomial.eval_monomial,
              highFrameFeature]
            apply Finset.sum_congr rfl
            intro γ hγ
            congr 1
            rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
            simp only [polynomial_box_exponent_apply]
          rw [h_highFramePolynomial_scaled_eval, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro γ hγ
          have hm : MvPolynomial.eval x (frameScaledPolynomial (highFrameMonomial γ)) =
              highFrameFeature x γ := by
            rw [frameScaledPolynomial_eval]
            unfold highFrameMonomial highFrameFeature
            rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
            simp only [polynomial_box_exponent_apply]
          rw [hm]
          ring
        exact h_highFrameProfile_evaluation _
      · simp only [ite_eq_right hz, mul_zero, Finset.sum_const_zero]
    _ = ∑ γ : HighFrameIndex d D, ∑ᶠ z : Fin d → ℤ,
        c γ * (if (∀ r, (z r : ZMod k) = j r) then
          highFrameProfile (highFrameMonomial γ) (fun r => k * x r - z r) else 0) :=
      (sum_finsum_comm Finset.univ _ (fun γ _ => hfinite γ)).symm
    _ = _ := by simp_rw [← mul_finsum]
theorem highFrameField_finite_evaluation (d k D : ℕ) [NeZero k] (η : ℝ)
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ) (x : Covariate d) :
    highFrameField d k η (fun j => highFramePolynomial (c j)) x =
      η * ∑ j, ∑ γ, c j γ * highPeriodizedChart d k j (highFrameProfile (highFrameMonomial γ)) x := by
  unfold highFrameField
  simp_rw [highPeriodizedFrame_evaluation]
def highChartLift (k ) (j : ZMod k) (x : ℝ) : ℤ :=
  j.val + k * Int.floor (x - j.val / k + 1 / 2)
theorem highChartLift_residue (k ) [NeZero k] (j ) (x ) :
    (highChartLift k j x : ZMod k) = j := by
  simp [highChartLift]
theorem highChartLift_eq_of_close (k ) [NeZero k] (hk : 4 ≤ k)
    (j : ZMod k) (x : ℝ) (z : ℤ) (hz : (z : ZMod k) = j)
    (hclose : |(k : ℝ) * x - z| < 1) : highChartLift k j x = z := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have : (4 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨t, ht⟩ := (ZMod.intCast_eq_iff k z j).mp hz
  have : (z : ℝ) = (j.val : ℝ) + (k : ℝ) * t := by exact_mod_cast ht
  have : k * (x - j.val / k + 1/2) =
      k * x - j.val + k/2 := by field_simp
  have := abs_lt.mp hclose
  have hf : Int.floor (x - (j.val : ℝ) / k + 1/2) = t := by
    apply Int.floor_eq_iff.mpr
    constructor
    · apply (mul_le_mul_iff_right₀ hkR).mp
      nlinarith
    · apply (mul_lt_mul_iff_right₀ hkR).mp
      nlinarith
  simp only [highChartLift, hf]
  exact ht.symm
def highRawChartCoordinate (k ) (j : ZMod k) (x : ℝ) : ℝ :=
  k * x - highChartLift k j x
def highLocalCoordinate (k ) (j : ZMod k) (x : ℝ) : ℝ :=
  if |highRawChartCoordinate k j x| ≤ 1 then highRawChartCoordinate k j x else 0
def highLocalCoordinates (d k ) (j : HighWindowLabels d k) (x : Covariate d) : Covariate d :=
  fun r => highLocalCoordinate k (j r) (x r)
theorem highRawChartCoordinate_measurable (k : ℕ) (j : ZMod k) :
    Measurable (highRawChartCoordinate k j) := by
  have h_highChartLift_measurable : Measurable (highChartLift k j) := by
    exact measurable_const.add (measurable_const.mul
      (Int.measurable_floor.comp (by fun_prop)))
  exact (measurable_const.mul measurable_id).sub
    ((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp h_highChartLift_measurable)
theorem highLocalCoordinates_measurable (d k ) (j ) :
    Measurable (highLocalCoordinates d k j) := by
  apply measurable_pi_iff.mpr
  intro r
  have h_highLocalCoordinate_measurable (j) : Measurable (highLocalCoordinate k j) := by
    apply Measurable.ite
    · exact measurableSet_le (highRawChartCoordinate_measurable k j).abs measurable_const
    · exact highRawChartCoordinate_measurable k j
    · exact measurable_const
  exact (h_highLocalCoordinate_measurable (j r)).comp (measurable_pi_apply r)
theorem highLocalCoordinates_abs_le_one (d k ) (j )
    (x ) (r ) : |highLocalCoordinates d k j x r| ≤ 1 :=
  have h_highLocalCoordinate_abs_le_one (j) (x) : |highLocalCoordinate k j x| ≤ 1 := by
    unfold highLocalCoordinate
    split_ifs with h
    · exact h
    · norm_num
  (h_highLocalCoordinate_abs_le_one (j r) (x r))
def highRawChartCoordinates (d k ) (j : HighWindowLabels d k) (x : Covariate d) : Covariate d :=
  fun r => highRawChartCoordinate k (j r) (x r)
def highLocalFrameFeature  (k ) (j : HighWindowLabels d k)
    (x : Covariate d) (γ : HighFrameIndex d D) : ℝ :=
  highFrameFeature (highLocalCoordinates d k j x) γ
theorem highLocalFrameFeature_measurable {d D : ℕ} (k : ℕ)
    (j : HighWindowLabels d k) (γ : HighFrameIndex d D) :
    Measurable (fun x => highLocalFrameFeature k j x γ) := by
  unfold highLocalFrameFeature highFrameFeature
  apply Finset.measurable_fun_prod
  intro r _
  exact (((measurable_pi_apply r).comp (highLocalCoordinates_measurable d k j)).div_const 8).pow_const _
def highLocalFieldWithout (d k D ) [NeZero k] (η : ℝ)
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ) (j : HighWindowLabels d k)
    (x : Covariate d) : ℝ :=
  η * ∑ l ∈ (Finset.univ : Finset (HighWindowLabels d k)).erase j,
    highPeriodizedChart d k l (highFrameProfile (highFramePolynomial (c l))) x
theorem highFrameField_local_decomposition (d k D ) [NeZero k] (hk : 4 ≤ k)
    (η ) (c )
    (j ) (x ) :
    highFrameField d k η (fun l => highFramePolynomial (c l)) x =
      highLocalFieldWithout d k D η c j x + η * highPeriodicTensor d k j x *
        ∑ γ, highLocalFrameFeature k j x γ * c j γ := by
  have h_highPeriodicTensor_eq_chart_lift : highPeriodicTensor d k j x = highWindowTensor d (highRawChartCoordinates d k j x) := by
    have h_highPeriodicWindow_eq_chart_lift (j : ZMod k) x : highPeriodicWindow k j x = highWindowProfile (k * x - highChartLift k j x) := by
      unfold highPeriodicWindow
      rw [finsum_eq_single _ (highChartLift k j x)]
      · simp only [ite_eq_left (highChartLift_residue k j x)]
      · intro z hz
        by_cases hj : (z : ZMod k) = j
        · simp only [ite_eq_left hj]
          by_contra hp
          have hclose : |k * x - z| < 1 := by
            have : |k * x - z| < 3/4 := by
              by_contra h
              exact hp (highWindowProfile_eq_zero _ (not_lt.mp h))
            linarith
          exact hz (highChartLift_eq_of_close k hk j x z hj hclose).symm
        · simp only [ite_eq_right hj]
    unfold highPeriodicTensor highWindowTensor highRawChartCoordinates highRawChartCoordinate
    simp_rw [h_highPeriodicWindow_eq_chart_lift]
  have hs := Finset.sum_erase_add (Finset.univ : Finset (HighWindowLabels d k))
    (fun l => highPeriodizedChart d k l (highFrameProfile (highFramePolynomial (c l))) x)
    (Finset.mem_univ j)
  have h_highPeriodizedFrame_local_feature : highPeriodizedChart d k j (highFrameProfile (highFramePolynomial (c j))) x =
      highPeriodicTensor d k j x * ∑ γ, highLocalFrameFeature k j x γ * (c j) γ := by
    rw [highPeriodizedFrame_evaluation, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro γ _
    have h_highPeriodizedFrameMonomial_local_feature : highPeriodizedChart d k j (highFrameProfile (highFrameMonomial γ)) x =
      highPeriodicTensor d k j x * highLocalFrameFeature k j x γ := by
      have h_highPeriodizedChart_eq_chart_lift (G) (hG0 : ∀ u, highWindowTensor d u = 0 → G u = 0) (x) : highPeriodizedChart d k j G x = G (highRawChartCoordinates d k j x) := by
        unfold highPeriodizedChart
        rw [finsum_eq_single _ (fun r => highChartLift k (j r) (x r))]
        · simp only [highChartLift_residue, implies_true, ite_true]
          rfl
        · intro z hz
          by_cases hres : ∀ r, (z r : ZMod k) = j r
          · simp only [ite_eq_left hres]
            by_contra hG
            apply hz
            funext r
            have hpr : highWindowProfile (k * x r - z r) ≠ 0 := by
              intro hp
              exact (fun hp => hG (hG0 _ hp)) (Finset.prod_eq_zero (Finset.mem_univ r) hp)
            have hclose : |k * x r - z r| < 1 := by
              have : |k * x r - z r| < 3/4 := by
                by_contra hp
                exact hpr (highWindowProfile_eq_zero _ (not_lt.mp hp))
              linarith
            exact (highChartLift_eq_of_close k hk (j r) (x r) (z r) (hres r) hclose).symm
          · simp only [ite_eq_right hres]
      rw [h_highPeriodizedChart_eq_chart_lift _ (highFrameProfile_zero_of_window_zero (highFrameMonomial γ))]
      unfold highFrameProfile
      have h_highFrameMonomial_scaled_eval (u : Covariate d) : MvPolynomial.eval u (frameScaledPolynomial (highFrameMonomial γ)) = highFrameFeature u γ := by
        rw [frameScaledPolynomial_eval]
        unfold highFrameMonomial highFrameFeature
        rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
        simp only [polynomial_box_exponent_apply]
      rw [h_highFrameMonomial_scaled_eval, ← h_highPeriodicTensor_eq_chart_lift]
      by_cases hw : highPeriodicTensor d k j x = 0
      · simp only [hw, zero_mul]
      have h_highLocalCoordinates_eq_raw_of_active : highLocalCoordinates d k j x = highRawChartCoordinates d k j x := by
        funext r
        have h_highRawChartCoordinates_abs_lt_of_active : |highRawChartCoordinates d k j x r| < 3/4 := by
          rw [h_highPeriodicTensor_eq_chart_lift] at hw
          have hp : highWindowProfile (highRawChartCoordinates d k j x r) ≠ 0 := by
            intro hp
            exact hw (Finset.prod_eq_zero (Finset.mem_univ r) hp)
          by_contra h
          exact hp (highWindowProfile_eq_zero _ (not_lt.mp h))
        have h := h_highRawChartCoordinates_abs_lt_of_active
        exact if_pos (by change |highRawChartCoordinate k (j r) (x r)| < 3/4 at h; linarith)
      · rw [highLocalFrameFeature, h_highLocalCoordinates_eq_raw_of_active]
    rw [h_highPeriodizedFrameMonomial_local_feature]
    ring
  rw [h_highPeriodizedFrame_local_feature] at hs
  unfold highFrameField highLocalFieldWithout
  rw [← hs]
  ring
theorem highFrameField_coefficientRegression (d k D n ) [NeZero k] (hk : 4 ≤ k)
    (η ) (c )
    (j : HighWindowLabels d k) (x : Fin n → Covariate d) :
    coefficientRegression η (fun i => highLocalFieldWithout d k D η c j (x i))
      (fun i => highPeriodicTensor d k j (x i))
      (fun i => highLocalFrameFeature k j (x i)) (c j) =
      fun i => highFrameField d k η (fun l => highFramePolynomial (c l)) (x i) := by
  funext i
  exact (highFrameField_local_decomposition d k D hk η c j (x i)).symm
theorem highLocalFrameFeature_ball_abs_le_one  (k )
    (j ) (x ) (C ) (hC : 1 ≤ C)
    (c : HighFrameIndex d D → ℝ) (hc : ∑ γ, |c γ| ≤ C⁻¹) :
    |∑ γ, highLocalFrameFeature k j x γ * c γ| ≤ 1 := by
  have h_highLocalFrameFeature_linear_abs_bound : |∑ γ, highLocalFrameFeature k j x γ * c γ| ≤ ∑ γ, |c γ| := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro γ _
    rw [abs_mul]
    have h_highLocalFrameFeature_abs_le_one : |highLocalFrameFeature k j x γ| ≤ 1 := by
      unfold highLocalFrameFeature highFrameFeature
      rw [Finset.abs_prod]
      apply Finset.prod_le_one₀
      · intro r _
        exact abs_nonneg _
      · intro r _
        rw [abs_pow]
        apply pow_le_one₀ (abs_nonneg _)
        rw [abs_div]
        norm_num
        linarith [highLocalCoordinates_abs_le_one d k j x r]
    exact (mul_le_mul_of_nonneg_right h_highLocalFrameFeature_abs_le_one
      (abs_nonneg (c γ))).trans_eq (one_mul _)
  apply h_highLocalFrameFeature_linear_abs_bound.trans
  exact hc.trans ((inv_le_one₀ (by linarith : 0 < C)).mpr hC)
end NearlyMinimax
