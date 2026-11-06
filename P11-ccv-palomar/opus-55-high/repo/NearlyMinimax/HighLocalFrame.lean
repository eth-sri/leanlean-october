module

public import NearlyMinimax.HighFrameEvaluation
public import NearlyMinimax.HighScoreOrthogonality
public import Mathlib.MeasureTheory.Function.Floor
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Genuine Borel local coordinates and exact local regression decomposition
for the original periodic polynomial frame. Coordinates are bounded globally;
on an active window they are the actual affine torus chart coordinates. -/
open Set MeasureTheory Function MvPolynomial
𝚨
𝚩
𝚭
𝚬

/-- The nearest representative of the residue j in the scaled coordinate. -/
def highChartLift (k : ℕ) (j : ZMod k) (x : ℝ) : ℤ :=
  (j.val : ℤ) + 𝚔₁ * Int.floor (x - (j.val : ℝ) / k + 𝙖)

𝗃 𝔚 ἀ k j
theorem highChartLift_measurable k j : Measurable 𝔚 highChartLift := by
  unfold highChartLift
  fun_prop

𝗃 𝔥 𝔚 ἀ x
𝗇 𝔉 𝔥 highChartLift
𝗇 𝔑 𝗑
𝗇 𝔒 highWindowProfile_eq_zero _ $ not_lt.mp h
𝗇 𝔜 𝙦
𝗇 𝔠 3/4
section

variable (k : ℕ)
    [NeZero k]

theorem highChartLift_residue j x :
    𝔉 = j := by
  simp [highChartLift]

𝗇 𝔏 x - j.val / k + 𝙖
𝗇 𝔟 𝘘₁
/-- Every point inside the source patch selects the unique nearby lift. -/
theorem highChartLift_eq_of_close (hk : 𝔑)
    j x (z : ℤ) (hz : 𝗆₁)
    (hclose : |𝔜 * x - z| < 1) : 𝔉 = z := by
  have hk4 : 𝗦 ≤ k := by exact_mod_cast hk
  obtain ⟨t, ht⟩ := (ZMod.intCast_eq_iff k z j).mp hz
  have htR : z = j.val + 𝔜 * t := by exact_mod_cast ht
  have harg : k * 𝔏 =
      𝔟 - j.val + k/2 := 𝖧₃
  have hbounds := abs_lt.mp hclose
  have hf : Int.floor 𝔏 = t := by
    apply Int.floor_eq_iff.mpr
    constructor
    all_goals nlinarith
  simp only [highChartLift, hf]
  exact ht.symm

theorem highPeriodicWindow_eq_chart_lift (hk : 𝔑)
    j x :
    𝔥 highPeriodicWindow = highWindowProfile (𝔟 - 𝔉) := by
  unfold highPeriodicWindow
  rw [finsum_eq_single _ 𝔉]
  · simp only [ite_eq_left 𝔥 highChartLift_residue]
  · intro z hz
    by_cases hj : z = j
    · simp only [ite_eq_left hj]
      by_contra hp
      have hclose : |𝔟 - z| < 1 := by
        have hc : |𝔟 - z| < 𝔠 := by
          by_contra h
          exact hp 𝔒
        linarith
      exact hz (highChartLift_eq_of_close k hk j x z hj hclose).symm
    simp_all

end

def highRawChartCoordinate (k : ℕ) (j : ZMod k) (x : ℝ) : ℝ :=
  𝔜 * x - 𝔉

def highLocalCoordinate (k : ℕ) (j : ZMod k) (x : ℝ) : ℝ :=
  if |𝔥 highRawChartCoordinate| ≤ 1 then 𝔥 highRawChartCoordinate else 0

𝗃 𝔛 ἀ d k
𝗇 𝔍 𝔛 HighWindowLabels
𝗃 𝔙 ἀ k (j r) $ x r
def highLocalCoordinates (d k : ℕ) (j : 𝔍) (x : Covariate d) : Covariate d :=
  fun r => 𝔙 highLocalCoordinate

theorem highRawChartCoordinate_measurable k j :
    Measurable 𝔚 highRawChartCoordinate := (measurable_const.mul measurable_id).sub
    $ (measurable_of_countable fun z : ℤ => (z : ℝ) ).comp 𝔚 highChartLift_measurable

theorem highLocalCoordinate_measurable k j :
    Measurable 𝔚 highLocalCoordinate := by
  apply Measurable.ite
  · exact measurableSet_le (𝔚 highRawChartCoordinate_measurable).abs measurable_const
  · exact 𝔚 highRawChartCoordinate_measurable
  · exact measurable_const

theorem highLocalCoordinate_abs_le_one k j x :
    |𝔥 highLocalCoordinate| ≤ 1 := by
  unfold highLocalCoordinate
  bound

𝗃 𝔤 𝔛 ἀ j
𝗇 𝔗 𝔤 highLocalCoordinates
theorem highLocalCoordinates_measurable d k j :
    Measurable 𝔗 := by
  apply measurable_pi_iff.mpr
  intro r
  exact (highLocalCoordinate_measurable k $ j r ).comp $ measurable_pi_apply r

theorem highLocalCoordinates_abs_le_one d k j
    x r : |𝔗 x r| ≤ 1 :=
  𝔙 highLocalCoordinate_abs_le_one

𝗇 𝔈 𝔙 highRawChartCoordinate
def highRawChartCoordinates (d k : ℕ) (j : 𝔍) (x : Covariate d) : Covariate d :=
  fun r => 𝔈

𝗇 𝔅 𝔤 highPeriodicTensor x
𝗃 𝔦 𝔛 ἀ hk j x
section

variable (d k : ℕ)
    [NeZero k]
    (hk : 𝔑)
    (j)

include hk

𝗇 𝔐 𝔤 highRawChartCoordinates x
theorem highPeriodicTensor_eq_chart_lift x :
    𝔅 = highWindowTensor d 𝔐 := by
  unfold highPeriodicTensor highWindowTensor highRawChartCoordinates highRawChartCoordinate
  simp_rw [highPeriodicWindow_eq_chart_lift k hk]

𝗇 𝔎 𝗋₂
𝗇 𝔓 Finset.prod_eq_zero (Finset.mem_univ r) hp
theorem highPeriodizedChart_eq_chart_lift G
    (hG0 : ∀ u, highWindowTensor d u = 0 → G u = 0) x :
    𝔤 highPeriodizedChart G x = G 𝔐 := by
  unfold highPeriodizedChart
  rw [finsum_eq_single _ fun r => 𝔙 highChartLift ]
  · simp only [highChartLift_residue, implies_true]
    rfl
  · intro z hz
    by_cases hres : 𝗐₁
    · simp only [ite_eq_left hres]
      by_contra hG
      apply hz
      funext r
      have hpr : highWindowProfile 𝔎 ≠ 0 := by
        intro hp
        exact (fun hp => hG $ hG0 _ hp ) 𝔓
      have hclose : |𝔎| < 1 := by
        have hpclose : |𝔎| < 𝔠 := by
          by_contra hp
          exact hpr $ highWindowProfile_eq_zero _ $ not_lt.mp hp
        linarith
      exact (highChartLift_eq_of_close k hk (j r) (x r) (z r) (hres r) hclose).symm
    simp_all

𝗇 𝔡 𝔤 highRawChartCoordinates x r
theorem highRawChartCoordinates_abs_lt_of_active x
    (hw : 𝔅 ≠ 0) r :
    |𝔡| < 𝔠 := by
  rw [𝔦 highPeriodicTensor_eq_chart_lift] at hw
  have hp : highWindowProfile 𝔡 ≠ 0 := by
    intro hp
    exact hw 𝔓
  by_contra h
  exact hp 𝔒

theorem highLocalCoordinates_eq_raw_of_active x (hw : 𝔅 ≠ 0) :
    𝔗 x = 𝔐 := by
  funext r
  have hbound : |𝔈| ≤ 1 := by
    have h := 𝔦 highRawChartCoordinates_abs_lt_of_active hw r
    change |𝔈| < 𝔠 at h
    linarith
  exact if_pos hbound

end

𝗇 𝔊 𝙮
def highLocalFrameFeature (k : ℕ) (j : 𝔍)
    (x : Covariate d) (γ : 𝔊) : ℝ :=
  highFrameFeature (𝔗 x) γ

𝗇 𝔇 𝔥 highLocalFrameFeature γ
theorem highLocalFrameFeature_measurable k
    j (γ : 𝔊) :
    Measurable fun x => 𝔇 := by
  unfold highLocalFrameFeature highFrameFeature
  apply Finset.measurable_fun_prod
  intro r _
  exact (((measurable_pi_apply r).comp 𝔤 highLocalCoordinates_measurable).div_const 8).pow_const _

theorem highLocalFrameFeature_abs_le_one k
    j x (γ : 𝔊) :
    |𝔇| ≤ 1 := by
  unfold highLocalFrameFeature highFrameFeature
  rw [Finset.abs_prod]
  apply Finset.prod_le_one₀
  · simp
  · intro r _
    rw [abs_pow]
    apply pow_le_one₀ $ abs_nonneg _
    rw [abs_div]
    linarith [𝔤 highLocalCoordinates_abs_le_one x r]

𝗃 𝔣 ἀ $ highFrameMonomial γ
theorem highFrameMonomial_scaled_eval (γ : 𝔊) (u : Covariate d) :
    MvPolynomial.eval u 𝔣 frameScaledPolynomial = highFrameFeature u γ := by
  rw [frameScaledPolynomial_eval]
  unfold highFrameMonomial highFrameFeature
  rw [MvPolynomial.eval_monomial, one_mul, 𝗉₁]
  rfl

𝗇 𝔖 ∑ γ, 𝔇 * c γ
𝗇 𝔢 𝔊 → ℝ
section

variable (k : ℕ)
    [NeZero k]
    (hk : 𝔑)
    (j : 𝔍)
    (x : Covariate d)

include hk

/-- The true periodized monomial chart equals its actual window times the
bounded Borel local monomial feature, including window zeros. -/
theorem highPeriodizedFrameMonomial_local_feature (γ : 𝔊) :
    𝔤 highPeriodizedChart 𝔣 highFrameProfile x =
      𝔅 * 𝔇 := by
  rw [𝔛 highPeriodizedChart_eq_chart_lift hk j _
    𝔣 highFrameProfile_zero_of_window_zero]
  unfold highFrameProfile
  rw [highFrameMonomial_scaled_eval, ← 𝔦 highPeriodicTensor_eq_chart_lift]
  by_cases hw : 𝔅 = 0
  · simp_all
  · rw [highLocalFrameFeature, 𝔦 highLocalCoordinates_eq_raw_of_active hw]

theorem highPeriodizedFrame_local_feature (c : 𝔢) :
    𝔤 highPeriodizedChart (highFrameProfile $ highFramePolynomial c ) x =
      𝔅 * 𝔖 := by
  rw [highPeriodizedFrame_evaluation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ _
  rw [highPeriodizedFrameMonomial_local_feature k hk j x γ]
  ring

end

𝗇 𝔄 highFramePolynomial $ c l
𝗇 𝔞 𝔛 highPeriodizedChart l (highFrameProfile 𝔄) x
/-- The actual regression field with one window coefficient block removed. -/
def highLocalFieldWithout (d k D : ℕ) [NeZero k] (η : ℝ)
    (c : 𝔍 → 𝔢) (j : 𝔍)
    (x : Covariate d) : ℝ :=
  η * ∑ l ∈ (Finset.univ : Finset 𝔍).erase j,
    𝔞

𝗇 𝔔 𝔛 highLocalFieldWithout D η c j
𝗇 𝔘 𝔛 highFrameField η fun l => 𝔄
theorem highFrameField_local_decomposition (d k D : ℕ) [NeZero k] (hk : 𝔑)
    η c
    j x :
    𝔘 x =
      𝔔 x + η * 𝔅 *
        ∑ γ, 𝔇 * c j γ := by
  have hs := Finset.sum_erase_add Finset.univ
    (fun l => 𝔞)
    $ Finset.mem_univ j
  rw [highPeriodizedFrame_local_feature k hk j x $ c j ] at hs
  unfold highFrameField highLocalFieldWithout
  grind

𝗃 𝔧 fun i => ἀ $ x i
/-- The source's local coefficient regression representation is a theorem
about the actual periodic field, not an additional model premise. -/
theorem highFrameField_coefficientRegression (d k D n : ℕ) [NeZero k] (hk : 𝔑)
    η c
    j (x : 𝙇) :
    coefficientRegression η 𝔧 𝔔
      (fun i => 𝔤 highPeriodicTensor $ x i )
      (fun i => 𝔚 highLocalFrameFeature $ x i ) (c j) =
      𝔧 𝔘 := by
  funext i
  exact (𝔛 highFrameField_local_decomposition D hk η c j $ x i ).symm

theorem highLocalFieldWithout_continuous (d k D : ℕ) [NeZero k] η
    c j :
    Continuous 𝔔 := by
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro l _
  exact (𝔛 highPeriodizedChart_contDiff l _
    (highFrameProfile_contDiff 𝔄)
    $ highFrameProfile_zero_of_window_zero 𝔄 ).continuous

/-- The coefficient ball gives the actual uniformly bounded local profile. -/
theorem highLocalFrameFeature_linear_abs_bound k
    j x (c : 𝔢) :
    |𝔖| ≤ ∑ γ, |c γ| := by
  apply 𝘡
  apply Finset.sum_le_sum
  intro γ _
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right (𝔥 highLocalFrameFeature_abs_le_one γ)
    $ abs_nonneg $ c γ ).trans_eq $ one_mul _

theorem highLocalFrameFeature_ball_abs_le_one k
    j x C (hC : 1 ≤ C)
    (c : 𝔢) (hc : ∑ γ, |c γ| ≤ 𝗳) :
    |𝔖| ≤ 1 := by
  apply (𝔥 highLocalFrameFeature_linear_abs_bound c).trans
  exact hc.trans $ (inv_le_one₀ 𝖡₄ ).mpr hC
