module

public import NearlyMinimax.HighFrameEvaluation
public import NearlyMinimax.HighScoreOrthogonality
public import Mathlib.MeasureTheory.Function.Floor


@[expose] public section

/-! Genuine Borel local coordinates and exact local regression decomposition
for the original periodic polynomial frame. Coordinates are bounded globally;
on an active window they are the actual affine torus chart coordinates. -/
noncomputable section
open Set MeasureTheory Function MvPolynomial
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

section
variable {k : ℕ} (j : ZMod k) (x : ℝ)

/-- The nearest representative of the residue j in the scaled coordinate. -/
def highChartLift : ℤ :=
  j.val + k * Int.floor (x - j.val / k + 1 / 2)

theorem highChartLift_residue [NeZero k] (j : ZMod k) (x : ℝ) :
    (highChartLift j x) = j := by
  simp [highChartLift]

/-- Every point inside the source patch selects the unique nearby lift. -/
theorem highChartLift_eq_of_close [NeZero k] (hk : 4 ≤ k)
    {j : ZMod k} {x : ℝ} {z : ℤ} (hz : z = j)
    (hclose : |k * x - z| < 1) : highChartLift j x = z := by
  have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨t, ht⟩ := (ZMod.intCast_eq_iff k z j).mp hz
  have htR : z = j.val + (k : ℝ) * t := by exact_mod_cast ht
  have harg : k * (x - j.val / k + 1/2) =
      k * x - j.val + k/2 := by field_simp
  have hbounds := abs_lt.mp hclose
  have hf : Int.floor (x - j.val / k + 1/2) = t := by
    apply Int.floor_eq_iff.mpr
    constructor <;> nlinarith
  simp only [highChartLift, hf]
  exact ht.symm

theorem highPeriodicWindow_eq_chart_lift [NeZero k] (hk : 4 ≤ k)
    (j : ZMod k) (x : ℝ) :
    highPeriodicWindow j x = highWindowProfile (k * x - highChartLift j x) := by
  unfold highPeriodicWindow
  rw [finsum_eq_single _ (highChartLift j x)]
  · grind [highChartLift_residue]
  · intro z hz
    by_cases hj : z = j
    · by_contra hp
      exact hz (highChartLift_eq_of_close hk hj (by
        grind [highWindowProfile_eq_zero])).symm
    · simp_all

def highRawChartCoordinate : ℝ :=
  k * x - highChartLift j x

def highLocalCoordinate : ℝ :=
  if |highRawChartCoordinate j x| ≤ 1 then highRawChartCoordinate j x else 0

def highLocalCoordinates {d k : ℕ} (j : HighWindowLabels d k) (x : Covariate d) : Covariate d :=
  fun r => highLocalCoordinate (j r) (x r)

theorem highRawChartCoordinate_measurable :
    Measurable (highRawChartCoordinate j) := (measurable_const.mul measurable_id).sub
    ((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp (by unfold highChartLift; exact measurable_const.add (measurable_const.mul (Int.measurable_floor.comp (by fun_prop)))))

theorem highLocalCoordinate_measurable :
    Measurable (highLocalCoordinate j) := by
  apply Measurable.ite
  · exact measurableSet_le (highRawChartCoordinate_measurable j).abs measurable_const
  · exact highRawChartCoordinate_measurable j
  · exact measurable_const

theorem highLocalCoordinate_abs_le_one :
    |highLocalCoordinate j x| ≤ 1 := by
  unfold highLocalCoordinate
  bound

end

section
variable {d k : ℕ} (j : HighWindowLabels d k) (x : Covariate d)

theorem highLocalCoordinates_measurable :
    Measurable (highLocalCoordinates j) := by
  apply measurable_pi_iff.mpr
  intro r
  exact (highLocalCoordinate_measurable (j r)).comp (measurable_pi_apply r)

theorem highLocalCoordinates_abs_le_one (r : Fin d) : |highLocalCoordinates j x r| ≤ 1 :=
  highLocalCoordinate_abs_le_one ..

def highRawChartCoordinates : Covariate d :=
  fun r => highRawChartCoordinate (j r) (x r)

end

section
variable {d k : ℕ} [NeZero k] (hk : 4 ≤ k) (j : HighWindowLabels d k)
include hk

theorem highPeriodicTensor_eq_chart_lift (x : Covariate d) :
    highPeriodicTensor j x = highWindowTensor d (highRawChartCoordinates j x) := by
  unfold highPeriodicTensor highWindowTensor highRawChartCoordinates highRawChartCoordinate
  simp_rw [highPeriodicWindow_eq_chart_lift hk]

theorem highPeriodizedChart_eq_chart_lift {G : Covariate d → ℝ}
    (hG0 : ∀ u, highWindowTensor d u = 0 → G u = 0) (x : Covariate d) :
    highPeriodizedChart j G x = G (highRawChartCoordinates j x) := by
  unfold highPeriodizedChart
  rw [finsum_eq_single _ (fun r => highChartLift (j r) (x r))]
  · simp [highChartLift_residue, implies_true, ite_true]
    rfl
  · intro z hz
    by_cases hres : ∀ r, (z r) = j r
    · simp [ite_eq_left hres]
      by_contra hG
      apply hz
      funext r
      have hpr : highWindowProfile (k * x r - z r) ≠ 0 := fun hp => (fun hp => hG (hG0 _ hp)) (Finset.prod_eq_zero (Finset.mem_univ r) hp)
      exact (highChartLift_eq_of_close hk (hres r) (by
        grind [highWindowProfile_eq_zero])).symm
    · simp_all

theorem highRawChartCoordinates_abs_lt_of_active
    {j : HighWindowLabels d k} {x : Covariate d}
    (hw : highPeriodicTensor j x ≠ 0) (r : Fin d) :
    |highRawChartCoordinates j x r| < 3/4 := by
  rw [highPeriodicTensor_eq_chart_lift hk j x] at hw
  have hp : highWindowProfile (highRawChartCoordinates j x r) ≠ 0 := fun hp => hw (Finset.prod_eq_zero (Finset.mem_univ r) hp)
  grind [highWindowProfile_eq_zero]

theorem highLocalCoordinates_eq_raw_of_active
    {j : HighWindowLabels d k} {x : Covariate d} (hw : highPeriodicTensor j x ≠ 0) :
    highLocalCoordinates j x = highRawChartCoordinates j x := by
  funext r
  have hbound : |highRawChartCoordinate (j r) (x r)| ≤ 1 := by
    have h := highRawChartCoordinates_abs_lt_of_active hk hw r
    change |highRawChartCoordinate (j r) (x r)| < _ at h
    linarith
  exact if_pos hbound

end

section
variable {d D k : ℕ} (j : HighWindowLabels d k) (γ : HighFrameIndex d D)

def highLocalFrameFeature
    (x : Covariate d) (γ : HighFrameIndex d D) : ℝ :=
  highFrameFeature (highLocalCoordinates j x) γ

theorem highLocalFrameFeature_measurable :
    Measurable (fun x => highLocalFrameFeature j x γ) := by
  unfold highLocalFrameFeature highFrameFeature
  apply Finset.measurable_fun_prod
  intro r _
  exact (((measurable_pi_apply r).comp (highLocalCoordinates_measurable j)).div_const 8).pow_const _

theorem highLocalFrameFeature_abs_le_one (x : Covariate d) (γ : HighFrameIndex d D) :
    |highLocalFrameFeature j x γ| ≤ 1 := by
  unfold highLocalFrameFeature highFrameFeature
  rw [Finset.abs_prod]
  apply Finset.prod_le_one₀
  · aesop
  · intro r _
    rw [abs_pow]
    apply pow_le_one₀ (abs_nonneg _)
    rw [abs_div]
    linarith [highLocalCoordinates_abs_le_one j x r]

theorem highFrameMonomial_scaled_eval (u : Covariate d) :
    MvPolynomial.eval u (frameScaledPolynomial (highFrameMonomial γ)) = highFrameFeature u γ := by
  rw [frameScaledPolynomial_eval]
  unfold highFrameMonomial highFrameFeature
  rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rfl

end

section
variable {d D k : ℕ} [NeZero k] (hk : 4 ≤ k) (j : HighWindowLabels d k) (x : Covariate d)
include hk

/-- The true periodized monomial chart equals its actual window times the
bounded Borel local monomial feature, including window zeros. -/
theorem highPeriodizedFrameMonomial_local_feature (γ : HighFrameIndex d D) :
    highPeriodizedChart j (highFrameProfile (highFrameMonomial γ)) x =
      highPeriodicTensor j x * highLocalFrameFeature j x γ := by
  rw [highPeriodizedChart_eq_chart_lift hk j
    (highFrameProfile_zero_of_window_zero (highFrameMonomial γ))]
  unfold highFrameProfile
  rw [highFrameMonomial_scaled_eval, ← highPeriodicTensor_eq_chart_lift hk j x]
  by_cases hw : highPeriodicTensor j x = 0
  · simp_all
  · rw [highLocalFrameFeature, highLocalCoordinates_eq_raw_of_active hk hw]

theorem highPeriodizedFrame_local_feature
    (c : HighFrameVector d D) :
    highPeriodizedChart j (highFrameProfile (highFramePolynomial c)) x =
      highPeriodicTensor j x * ∑ γ, highLocalFrameFeature j x γ * c γ := by
  rw [highPeriodizedFrame_evaluation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ _
  rw [highPeriodizedFrameMonomial_local_feature hk j x γ]
  ring

end

section
variable {d k D n : ℕ} [NeZero k] (hk : 4 ≤ k) (η : ℝ) (c : HighWindowLabels d k → HighFrameVector d D)
    (j : HighWindowLabels d k) (x : Covariate d)

/-- The actual regression field with one window coefficient block removed. -/
def highLocalFieldWithout : ℝ :=
  η * ∑ l ∈ Finset.univ.erase j,
    highPeriodizedChart l (highFrameProfile (highFramePolynomial (c l))) x

include hk in
theorem highFrameField_local_decomposition :
    highFrameField k η (fun l => highFramePolynomial (c l)) x =
      highLocalFieldWithout η c j x + η * highPeriodicTensor j x *
        ∑ γ, highLocalFrameFeature j x γ * c j γ := by
  have hs := Finset.sum_erase_add Finset.univ
    (fun l => highPeriodizedChart l (highFrameProfile (highFramePolynomial (c l))) x)
    (Finset.mem_univ j)
  rw [highPeriodizedFrame_local_feature hk j x (c j)] at hs
  unfold highFrameField highLocalFieldWithout
  rw [← hs]
  ring

include hk in
/-- The source's local coefficient regression representation is a theorem
about the actual periodic field, not an additional model premise. -/
theorem highFrameField_coefficientRegression (x : DesignSample d n) :
    coefficientRegression η (fun i => highLocalFieldWithout η c j (x i))
      (fun i => highPeriodicTensor j (x i))
      (fun i => highLocalFrameFeature j (x i)) (c j) =
      fun i => highFrameField k η (fun l => highFramePolynomial (c l)) (x i) := by
  funext i
  exact (highFrameField_local_decomposition hk η c j (x i)).symm

theorem highLocalFieldWithout_continuous :
    Continuous (highLocalFieldWithout η c j) := by
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro l _
  exact (highPeriodizedChart_contDiff l
    (highFrameProfile_contDiff _)
    (highFrameProfile_zero_of_window_zero _)).continuous

end

variable {d D k : ℕ} (j : HighWindowLabels d k) (x : Covariate d)

/-- The coefficient ball gives the actual uniformly bounded local profile. -/
theorem highLocalFrameFeature_linear_abs_bound (c : HighFrameVector d D) :
    |∑ γ, highLocalFrameFeature j x γ * c γ| ≤ ∑ γ, |c γ| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro γ _
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right (highLocalFrameFeature_abs_le_one ..)
    (abs_nonneg (c γ))).trans_eq (one_mul _)

theorem highLocalFrameFeature_ball_abs_le_one {C : ℝ} (hC : 1 ≤ C)
    {c : HighFrameVector d D} (hc : ∑ γ, |c γ| ≤ C⁻¹) :
    |∑ γ, highLocalFrameFeature j x γ * c γ| ≤ 1 := by
  apply (highLocalFrameFeature_linear_abs_bound j x c).trans
  exact hc.trans ((inv_le_one₀ (by linarith)).mpr hC)

end NearlyMinimax
