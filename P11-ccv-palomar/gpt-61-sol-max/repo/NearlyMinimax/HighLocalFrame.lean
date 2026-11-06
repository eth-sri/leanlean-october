module

public import NearlyMinimax.HighFrameEvaluation
public import NearlyMinimax.HighSeparatedScores
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
variable (k : ℕ)

/-- The nearest representative of the residue j in the scaled coordinate. -/
def highChartLift  (j : ZMod k) x  :=
  (j.val : ℤ) + (k : ℤ) * Int.floor (x - (j.val : ℝ) / k + 1 / 2)

theorem highChartLift_measurable  j : Measurable (highChartLift k j) := measurable_const.add (measurable_const.mul
    (Int.measurable_floor.comp (by fun_prop)))

theorem highChartLift_residue  [NeZero k] j x :
    (highChartLift k j x) = j := by
  simp [highChartLift]

section
variable [NeZero k] (hk : 4 ≤ k) (j : ZMod k) (x : ℝ)
include hk

/-- Every point inside the source patch selects the unique nearby lift. -/
theorem highChartLift_eq_of_close   (z : ℤ) (hz : z = j)
    (hclose : |k * x - z| < 1) : highChartLift k j x = z := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast hk
  obtain ⟨t, ht⟩ := (ZMod.intCast_eq_iff k z j).mp hz
  have htR : (z : ℝ) = (j.val : ℝ) + (k : ℝ) * t := by exact_mod_cast ht
  have harg : (k : ℝ) * (x - (j.val : ℝ) / k + 1/2) =
      (k : ℝ) * x - j.val + k/2 := by field_simp
  have hbounds := abs_lt.mp hclose
  have hf : Int.floor (x - (j.val : ℝ) / k + 1/2) = t := by
    apply Int.floor_eq_iff.mpr
    constructor
    · apply (mul_le_mul_iff_right₀ hkR).mp
      nlinarith
    · apply (mul_lt_mul_iff_right₀ hkR).mp
      nlinarith
  simp only [highChartLift, hf]
  exact ht.symm

theorem highPeriodicWindow_eq_chart_lift   :
    highPeriodicWindow k j x = highWindowProfile (k * x - highChartLift k j x) := by
  unfold highPeriodicWindow
  rw [finsum_eq_single _ (highChartLift k j x)]
  · simp only [ite_eq_left (highChartLift_residue k j x)]
  · intro z hz
    by_cases hj : (z : ZMod k) = j
    · simp only [ite_eq_left hj]
      by_contra hp
      have hclose : |(k : ℝ) * x - z| < 1 := by
        have hc : |(k : ℝ) * x - z| < 3/4 := by
          by_contra h
          exact hp (highWindowProfile_eq_zero _ (not_lt.mp h))
        linarith
      exact hz (highChartLift_eq_of_close k hk j x z hj hclose).symm
    · simp only [ite_eq_right hj]
end


def highRawChartCoordinate  j x  :=
  (k : ℝ) * x - highChartLift k j x

def highLocalCoordinate  j x  :=
  if |highRawChartCoordinate k j x| ≤ 1 then highRawChartCoordinate k j x else 0
end


def highLocalCoordinates (d k : ℕ) (j : HighWindowLabels d k) (x : Covariate d) : Covariate d :=
  fun r => highLocalCoordinate k (j r) (x r)

theorem highRawChartCoordinate_measurable k j :
    Measurable (highRawChartCoordinate k j) := (measurable_const.mul measurable_id).sub
    ((measurable_of_countable (fun z : ℤ => (z : ℝ))).comp (highChartLift_measurable k j))

theorem highLocalCoordinate_measurable k j :
    Measurable (highLocalCoordinate k j) := by
  unfold highLocalCoordinate
  apply Measurable.ite
  · exact measurableSet_le (highRawChartCoordinate_measurable k j).abs measurable_const
  · exact highRawChartCoordinate_measurable k j
  · exact measurable_const

theorem highLocalCoordinate_abs_le_one k j x :
    |highLocalCoordinate k j x| ≤ 1 := by
  unfold highLocalCoordinate
  split_ifs with h
  · exact h
  · norm_num

section
variable (d k : ℕ)

section
variable (j : HighWindowLabels d k)
include j

theorem highLocalCoordinates_measurable   :
    Measurable (highLocalCoordinates d k j) := by
  apply measurable_pi_iff.mpr
  intro r
  exact (highLocalCoordinate_measurable k (j r)).comp (measurable_pi_apply r)

theorem highLocalCoordinates_abs_le_one  
    x r : |highLocalCoordinates d k j x r| ≤ 1 :=
  highLocalCoordinate_abs_le_one k (j r) (x r)

def highRawChartCoordinates   (x : Covariate d) : Covariate d :=
  fun r => highRawChartCoordinate k (j r) (x r)
end


section
variable [NeZero k] (hk : 4 ≤ k) (j : HighWindowLabels d k)
include hk

theorem highPeriodicTensor_eq_chart_lift   x :
    highPeriodicTensor d k j x = highWindowTensor d (highRawChartCoordinates d k j x) := by
  unfold highPeriodicTensor highWindowTensor highRawChartCoordinates highRawChartCoordinate
  simp_rw [highPeriodicWindow_eq_chart_lift k hk]

theorem highPeriodizedChart_eq_chart_lift   G
    (hG0 : ∀ u, highWindowTensor d u = 0 → G u = 0) x :
    highPeriodizedChart d k j G x = G (highRawChartCoordinates d k j x) := by
  unfold highPeriodizedChart
  rw [finsum_eq_single _ (fun r => highChartLift k (j r) (x r))]
  · simp only [highChartLift_residue, implies_true, ite_true]
    rfl
  · intro z hz
    by_cases hres : ∀ r, (z r : ZMod k) = j r
    · simp only [ite_eq_left hres]
      by_contra hG
      have hprof  :=
        fun hp => hG (hG0 _ hp)
      apply hz
      funext r
      have hpr : highWindowProfile ((k : ℝ) * x r - z r) ≠ 0 := by
        intro hp
        exact hprof (Finset.prod_eq_zero (Finset.mem_univ r) hp)
      have hclose : |(k : ℝ) * x r - z r| < 1 := by
        have hpclose : |(k : ℝ) * x r - z r| < 3/4 := by
          by_contra hp
          exact hpr (highWindowProfile_eq_zero _ (not_lt.mp hp))
        linarith
      exact (highChartLift_eq_of_close k hk (j r) (x r) (z r) (hres r) hclose).symm
    · simp only [ite_eq_right hres]

section
variable (x : Covariate d) (hw : highPeriodicTensor d k j x ≠ 0)
include hw

theorem highRawChartCoordinates_abs_lt_of_active    r :
    |highRawChartCoordinates d k j x r| < 3/4 := by
  rw [highPeriodicTensor_eq_chart_lift d k hk j x] at hw
  have hp : highWindowProfile (highRawChartCoordinates d k j x r) ≠ 0 := by
    intro hp
    exact hw (Finset.prod_eq_zero (Finset.mem_univ r) hp)
  by_contra h
  exact hp (highWindowProfile_eq_zero _ (not_lt.mp h))

theorem highLocalCoordinates_eq_raw_of_active    :
    highLocalCoordinates d k j x = highRawChartCoordinates d k j x := by
  funext r
  have hbound : |highRawChartCoordinate k (j r) (x r)| ≤ 1 := by
    have h := highRawChartCoordinates_abs_lt_of_active d k hk j x hw r
    change |highRawChartCoordinate k (j r) (x r)| < 3/4 at h
    linarith
  exact if_pos hbound
end

end

end


section
variable {d D : ℕ}

def highLocalFrameFeature  k j
    x (γ : HighFrameIndex d D)  :=
  highFrameFeature (highLocalCoordinates d k j x) γ

theorem highLocalFrameFeature_measurable  k
    j (γ : HighFrameIndex d D) :
    Measurable (fun x => highLocalFrameFeature k j x γ) := by
  unfold highLocalFrameFeature highFrameFeature
  apply Finset.measurable_fun_prod
  intro r _
  exact (((measurable_pi_apply r).comp (highLocalCoordinates_measurable d k j)).div_const 8).pow_const _

theorem highLocalFrameFeature_abs_le_one  k
    j x (γ : HighFrameIndex d D) :
    |highLocalFrameFeature k j x γ| ≤ 1 := by
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

theorem highFrameMonomial_scaled_eval  (γ : HighFrameIndex d D) (u : Covariate d) :
    MvPolynomial.eval u (frameScaledPolynomial (highFrameMonomial γ)) = highFrameFeature u γ := by
  rw [frameScaledPolynomial_eval]
  unfold highFrameMonomial highFrameFeature
  rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [polynomial_box_exponent_apply]

section
variable (k : ℕ) [NeZero k] (hk : 4 ≤ k)
include hk

/-- The true periodized monomial chart equals its actual window times the
bounded Borel local monomial feature, including window zeros. -/
theorem highPeriodizedFrameMonomial_local_feature   j x (γ : HighFrameIndex d D) :
    highPeriodizedChart d k j (highFrameProfile (highFrameMonomial γ)) x =
      highPeriodicTensor d k j x * highLocalFrameFeature k j x γ := by
  rw [highPeriodizedChart_eq_chart_lift d k hk j _
    (highFrameProfile_zero_of_window_zero (highFrameMonomial γ))]
  unfold highFrameProfile
  rw [highFrameMonomial_scaled_eval, ← highPeriodicTensor_eq_chart_lift d k hk j x]
  by_cases hw : highPeriodicTensor d k j x = 0
  · simp only [hw, zero_mul]
  · rw [highLocalFrameFeature, highLocalCoordinates_eq_raw_of_active d k hk j x hw]

theorem highPeriodizedFrame_local_feature   j x
    (c : HighFrameIndex d D → ℝ) :
    highPeriodizedChart d k j (highFrameProfile (highFramePolynomial c)) x =
      highPeriodicTensor d k j x * ∑ γ, highLocalFrameFeature k j x γ * c γ := by
  rw [highPeriodizedFrame_evaluation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ _
  rw [highPeriodizedFrameMonomial_local_feature k hk j x γ]
  ring
end

end


/-- The actual regression field with one window coefficient block removed. -/
def highLocalFieldWithout d k D [NeZero k] η
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ) j
    x  :=
  η * ∑ l ∈ (Finset.univ : Finset (HighWindowLabels d k)).erase j,
    highPeriodizedChart d k l (highFrameProfile (highFramePolynomial (c l))) x

theorem highFrameField_local_decomposition d k D [NeZero k] (hk : 4 ≤ k)
    η c
    j x :
    highFrameField d k η (fun l => highFramePolynomial (c l)) x =
      highLocalFieldWithout d k D η c j x + η * highPeriodicTensor d k j x *
        ∑ γ, highLocalFrameFeature k j x γ * c j γ := by
  have hs := Finset.sum_erase_add (Finset.univ : Finset (HighWindowLabels d k))
    (fun l => highPeriodizedChart d k l (highFrameProfile (highFramePolynomial (c l))) x)
    (Finset.mem_univ j)
  rw [highPeriodizedFrame_local_feature k hk j x (c j)] at hs
  unfold highFrameField highLocalFieldWithout
  rw [← hs]
  ring

/-- The source's local coefficient regression representation is a theorem
about the actual periodic field, not an additional model premise. -/
theorem highFrameField_coefficientRegression d k D n [NeZero k] (hk : 4 ≤ k)
    η c
    j (x : Fin n → Covariate d) :
    coefficientRegression η (fun i => highLocalFieldWithout d k D η c j (x i))
      (fun i => highPeriodicTensor d k j (x i))
      (fun i => highLocalFrameFeature k j (x i)) (c j) =
      fun i => highFrameField d k η (fun l => highFramePolynomial (c l)) (x i) := by
  funext i
  exact (highFrameField_local_decomposition d k D hk η c j (x i)).symm

theorem highLocalFieldWithout_continuous d k D [NeZero k] η
    c j :
    Continuous (highLocalFieldWithout d k D η c j) := by
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro l _
  exact (highPeriodizedChart_contDiff d k l _
    (highFrameProfile_contDiff (highFramePolynomial (c l)))
    (highFrameProfile_zero_of_window_zero (highFramePolynomial (c l)))).continuous

/-- The coefficient ball gives the actual uniformly bounded local profile. -/
theorem highLocalFrameFeature_linear_abs_bound {d D } k
    j x (c : HighFrameIndex d D → ℝ) :
    |∑ γ, highLocalFrameFeature k j x γ * c γ| ≤ ∑ γ, |c γ| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro γ _
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right (highLocalFrameFeature_abs_le_one k j x γ)
    (abs_nonneg (c γ))).trans_eq (one_mul _)

theorem highLocalFrameFeature_ball_abs_le_one {d D } k
    j x C (hC : 1 ≤ C)
    (c : HighFrameIndex d D → ℝ) (hc : ∑ γ, |c γ| ≤ C⁻¹) :
    |∑ γ, highLocalFrameFeature k j x γ * c γ| ≤ 1 := by
  linarith [highLocalFrameFeature_linear_abs_bound k j x c, hc.trans ((inv_le_one₀ (by linarith : 0 < C)).mpr hC)]

end NearlyMinimax
