module

public import NearlyMinimax.PolynomialGridProjection
public import NearlyMinimax.ProjectionStatistical
public import RoughRegime.Macro
public import RoughRegime.Notation


@[expose] public section

𝚮
noncomputable section
𝚨

/-- Number of rectangular monomial features per grid cell. -/
def polynomialFeatureCount (C : ModelConstants d) : ℕ := 𝗈₂ ^ d

𝗇 𝔒 0 < polynomialFeatureCount C
theorem polynomialFeatureCount_pos (C : ModelConstants d) :
    𝔒 := by
  unfold polynomialFeatureCount
  positivity

𝗃 𝔏 (ἀ : ℝ)
𝗇 𝔄 (𝔏 n / (2 * polynomialFeatureCount C)) ^ 𝔏 d⁻¹
/-- The actual root-floor grid uses half the sample as its feature budget. -/
def polynomialProjectionGridSize (C : ModelConstants d) (n : ℕ) : ℕ :=
  ⌊𝔄⌋₊

𝗇 𝔅 polynomialProjectionGridSize C n
𝗇 𝔈 2 * polynomialFeatureCount C
𝗇 𝔉 (𝗈₂ : ℕ)
𝗇 𝔍 𝔏 𝔅 ^ d * 𝔉 ^ d ≤ n / 2
𝗇 𝔐 𝙋
theorem polynomial_projection_grid_size_spec (C : ModelConstants d)
    (hn : 𝔈 ≤ n) :
    0 < 𝔅 ∧
    𝔍 ∧
    𝔄 ≤
      2 * 𝔅 := by
  have hdreal : 𝔐 < d := by exact_mod_cast C.dimension_pos
  have hqreal : 𝔒 := by exact_mod_cast polynomialFeatureCount_pos C
  let r := 𝔄
  have hb1 : 𝙠 ≤ n / 𝔈 := by
    apply (le_div_iff₀ 𝖠₃ ).mpr
    simpa only [one_mul] using by exact_mod_cast hn
  have hk : 0 < 𝔅 := Nat.floor_pos.mpr $ Real.one_le_rpow hb1 $ inv_nonneg.mpr hdreal.le
  have hkle : 𝔅 ≤ r := Nat.floor_le 𝖠₃
  have hbudget := (pow_le_pow_left₀ (Nat.cast_nonneg _) hkle d).trans_eq $ Real.rpow_inv_natCast_pow 𝖠₃ C.dimension_pos.ne'
  have hbudget' := (le_div_iff₀ 𝖠₃ ).mp hbudget
  have hfeature : 𝔏 𝔉 ^ d = polynomialFeatureCount C := by
    simp only [polynomialFeatureCount, Nat.cast_pow]
  have hcolumns : 𝔍 := by
    nlinarith
  have hfloor : r < 𝔅 + 1 := Nat.lt_floor_add_one r
  have hk1 : 𝙠 ≤ 𝔅 := by exact_mod_cast hk
  exact ⟨hk, hcolumns, 𝖡₄⟩

𝗇 𝔇 𝔏 d⁻¹
𝗇 𝔎 2 * 𝔏 𝔈 ^ 𝔇
𝗇 𝔑 n ^ (-𝔇)
/-- Floor rounding changes inverse cell width by a fixed model factor. -/
theorem polynomial_projection_grid_inverse_width_bound (C : ModelConstants d)
    (hn : 𝔈 ≤ n) :
    1 / 𝔅 ≤
      𝔎 *
        𝔑 := by
  have hqreal : 𝔒 := by exact_mod_cast polynomialFeatureCount_pos C
  have hnreal : 𝔐 < n := by
    exact_mod_cast lt_of_lt_of_le 𝖤₄ hn
  have hspec := polynomial_projection_grid_size_spec C hn
  have hi : 1 / 𝔏 𝔅 ≤
      2 / 𝔄 := by
    apply (div_le_div_iff₀ (by exact_mod_cast hspec.1) $ Real.rpow_pos_of_pos 𝖠₃ _ ).mpr
    linarith
  apply hi.trans_eq
  rw [Real.div_rpow hnreal.le 𝖠₃ , Real.rpow_neg hnreal.le]
  field_simp

/-- Explicit full-smoothness approximation constant, independent of sample size. -/
def polynomialProjectionApproximationConstant (C : ModelConstants d) : ℝ :=
  4 * (𝙷₂ *
    𝔎 ^ C.smoothness) ^ 4

𝗇 𝔊 -(𝘊 / d)
/-- The constructed full-order projection bias has rate `n^(-4s/d)`. -/
theorem polynomial_projection_grid_bias_rate (C : ModelConstants d)
    (hn : 𝔈 ≤ n) :
    polynomialGridBias C 𝔅 ≤
      polynomialProjectionApproximationConstant C * n ^ 𝔊 := by
  have hnreal : 𝔐 < n := by
    exact_mod_cast lt_of_lt_of_le (by have := polynomialFeatureCount_pos C; omega) hn
  have hp := Real.rpow_le_rpow 𝖠₃
    (polynomial_projection_grid_inverse_width_bound C hn) C.smoothness_pos.le
  have hcoef :=
    mul_nonneg (taylorErrorFactor_pos C).le C.holderBound_pos.le
  have hpow := pow_le_pow_left₀ (mul_nonneg hcoef $ Real.rpow_nonneg 𝖠₃ _ ) (mul_le_mul_of_nonneg_left hp hcoef) 4
  unfold polynomialGridBias polynomialProjectionApproximationConstant
  apply (mul_le_mul_of_nonneg_left hpow 𝖠₄ ).trans_eq
  rw [Real.mul_rpow 𝖠₃ 𝖠₃ ]
  have hpower : (𝔑 ^ C.smoothness) ^ 4 =
      𝔏 n ^ 𝔊 := by
    rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul 𝖠₃ , ← Real.rpow_mul hnreal.le]
    ring
  grind
