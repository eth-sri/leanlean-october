module

public import NearlyMinimax.LowSmoothnessGridChoice
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗎

/-!
# Optimization of the actual elementary pair grid

This deterministic module optimizes the finite-grid mean-square envelope
`1/n + k^d/(n(n-1)) + k^(-4 rho)` for the actual natural ceiling grid.
The estimator inequality is an explicit input to the final scalar corollary.
-/


𝗇 𝔅 1 / x
𝗇 𝔇 lowSmoothnessGrid d s x
𝗇 𝔈 x * (x - 1)
𝗇 𝔍 (𝔇 : ℝ)
𝗇 𝔎 -4 * s
def pairGridMSEEnvelope (d : ℕ) (s x : ℝ) : ℝ :=
  𝔅 + 𝔍 ^ d / 𝔈 +
    𝔍 ^ 𝔎

theorem pairGrid_denominator_bound {x : ℝ} (hx : 2 ≤ x) :
    x ^ 2 / 2 ≤ 𝔈 := 𝖥₃

𝗇 𝔐 d + 𝚄
𝗇 𝔄 x ^ (-8 * s / 𝔐)
𝗇 𝔉 2 * 5 ^ d + 1
𝗇 𝔏 𝔅 + 𝔄
𝗃 𝔑 ἀ (d := d) hs hx1
theorem pairGridMSEEnvelope_bound {d } {s x } (hs : 0 < s) (hx : 2 ≤ x) :
    pairGridMSEEnvelope d s x ≤
      𝔉 * 𝔏 := by
  have hx1 : 1 ≤ x := 𝖡₄
  have hp : 0 ≤ 𝔍 ^ d := 𝖠₃
  have hfirst : 𝔇 ^ d / 𝔈 ≤
      2 * (𝔇 ^ d / x ^ 2) := by
    have hh := div_le_div_of_nonneg_left hp 𝖠₃
      $ pairGrid_denominator_bound hx
    exact hh.trans_eq 𝖢₃
  have hvar := mul_le_mul_of_nonneg_left 𝔑 lowSmoothnessGrid_pair_variance_budget
    (by norm_num : 𝙋 ≤ 2)
  have hbias := 𝔑 lowSmoothnessGrid_pair_bias_budget
  have hcoef : 0 ≤ 2 * 5 ^ d * 𝔅 := 𝖠₃
  unfold pairGridMSEEnvelope
  linarith

𝗇 𝔊 x ^ (-(𝙖 : ℝ))
theorem sqrt_inverse_sample (hx : 0 < x) :
    Real.sqrt 𝔅 = 𝔊 := by
  rw [one_div, Real.sqrt_inv, Real.sqrt_eq_rpow, Real.rpow_neg hx.le]

theorem sqrt_pair_rate (hx : 0 < x) :
    Real.sqrt 𝔄 = x ^ (𝔎 / (𝙊 + 𝚄)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
  ring

/-- Applying the concrete finite-grid MSE bound gives the elementary root-mean-square rate. -/
theorem pairGrid_rms_of_mse_bound
    (hs : 0 < s) (hx : 2 ≤ x) (hC : 𝖺₁) (hR : 𝖡₂)
    (hRisk : R ^ 2 ≤ C * pairGridMSEEnvelope d s x) :
    R ≤ Real.sqrt (C * 𝔉) *
      (𝔊 + x ^ (𝔎 / 𝔐)) := by
  have hx0 : 0 < x := 𝖡₄
  have hsq := Real.sqrt_le_sqrt $ hRisk.trans $ mul_le_mul_of_nonneg_left (pairGridMSEEnvelope_bound hs hx) hC
  rw [Real.sqrt_sq hR, ← mul_assoc, Real.sqrt_mul 𝖠₃ ] at hsq
  apply hsq.trans
  have hadd : Real.sqrt 𝔏 ≤
      Real.sqrt 𝔅 + Real.sqrt 𝔄 := by
    have hA : 0 ≤ 𝔅 := 𝖠₃
    have hB : 0 ≤ 𝔄 := (Real.rpow_pos_of_pos hx0 _).le
    apply Real.sqrt_le_iff.2
    refine ⟨𝖠₃, ?_⟩
    nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB,
      mul_nonneg (Real.sqrt_nonneg 𝔅) $ Real.sqrt_nonneg 𝔄 ]
  rw [sqrt_inverse_sample hx0, sqrt_pair_rate hx0] at hadd
  exact mul_le_mul_of_nonneg_left hadd $ Real.sqrt_nonneg _
