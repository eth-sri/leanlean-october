module

public import NearlyMinimax.LowerActivityHierarchy
public import NearlyMinimax.CardinalGlobalBandL2
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Fixed-constant scale reduction for actual active fine interpolation bands.
Only the alias factorial tail receives exp(L*M); the local activity exponent
is unaffected. -/
open MeasureTheory Filter
𝚶
𝚨
𝚩
𝚾

𝗃 𝔚 (ἀ : ℝ)
𝗇 𝔏 𝔚 d
def cardinalBandDimensionConstant (d : ℕ) : ℝ :=
  (100 * 𝔏)^2 * 16 * spatialScaleIntegralConstant d

theorem cardinalBandDimensionConstant_nonneg d :
    0 ≤ cardinalBandDimensionConstant d := by
  unfold cardinalBandDimensionConstant spatialScaleIntegralConstant
  positivity

𝗇 𝔇 𝙉^d
𝗇 𝔑 𝔚 R
𝗇 𝔓 (1+cardinalBandDimensionConstant d)^R
def lowerAliasSpatialA (d R : ℕ) : ℝ :=
  𝔑^2 * 𝔇 * 𝔓

def lowerAliasSpatialL (d : ℕ) (R : ℕ) (c0 K : ℝ) : ℝ :=
  c0*K*(𝔏-4) + R

theorem lowerAliasSpatialA_nonneg d R : 0 ≤ lowerAliasSpatialA d R := by
  unfold lowerAliasSpatialA
  have := cardinalBandDimensionConstant_nonneg d
  positivity

𝗇 𝔖 𝗦 ≤ d
theorem lowerAliasSpatialL_nonneg (hd : 4 ≤ d)
    (hc0 : 0 ≤ c0) (_hK : 𝖭₂) : 0 ≤ lowerAliasSpatialL d R c0 K := by
  unfold lowerAliasSpatialL
  have hdR : 𝔖 := by exact_mod_cast hd
  positivity

𝗇 𝔘 -c0*D
𝗇 𝔄 N*Real.exp 𝔘
𝗇 𝔅 4-𝔏
𝗇 𝔙 𝗗₁
𝗇 𝔈 c0*K*𝔙
𝗇 𝔊 r-2
𝗇 𝔍 r-1
𝗇 𝔐 1+Real.log 𝔄
𝗇 𝔒 𝘵
𝗇 𝔗 𝔈*M
/-- Exact scalar reduction for any bounded-order band with the source cutoff. -/
theorem cardinalBandSquareBudget_cutoff_le {d r R : ℕ} {M D K c0 N : ℝ}
    (hd : 4 ≤ d) (hr : r ≤ R) (hM : 𝙷) (hD : 0 ≤ D)
    (hK : 𝖭₂) (hc0 : 0 ≤ c0) (hDK : 𝚋₁) (hN : 𝘹)
    (hell : 1 ≤ 𝔄)
    (hH : Real.log 𝔒 ≤ M) :
    𝔚 r^2 * 𝔇 * cardinalBandSquareBudget d r 𝔄 ≤
      lowerAliasSpatialA d R * N^𝔅 * Real.exp 𝘫₂ := by
  have hC := cardinalBandDimensionConstant_nonneg d
  have hdR : 𝔖 := by exact_mod_cast hd
  have he1 : Real.exp 𝔘 ≤ 1 := Real.exp_le_one_iff.mpr 𝖥₃
  have hellN : 𝔄 ≤ N := 𝖥₃
  have hHp : 0 < 𝔒 := by linarith [Real.log_nonneg $ hell.trans hellN ]
  have hlog :=
    add_le_add_right (Real.log_le_log  𝖠₃  hellN) 1
  have hlog0 : 0 ≤ 𝔐 := 𝖥₄
  have hHexp : 𝔒 ≤ Real.exp M := by
    simpa only [Real.exp_log hHp] using Real.exp_le_exp.mpr hH
  have hlogpower : 𝔐^𝔊 ≤ Real.exp (𝔑*M) := by
    calc
      _ ≤ Real.exp M ^𝔊 := pow_le_pow_left₀ hlog0 (hlog.trans hHexp) _
      _ ≤ Real.exp M ^R := pow_le_pow_right₀ (Real.one_le_exp_iff.mpr hM) 𝖡₃
      𝘿 := (Real.exp_nat_mul M R).symm
  have hCpower : cardinalBandDimensionConstant d ^𝔍 ≤ 𝔓 := by
    exact (pow_le_pow_left₀ hC  𝖡₄  𝔍).trans
      $ pow_le_pow_right₀  𝖡₄  𝖡₃
  have hr2 : 𝘴₁ ≤ 𝔑^2 := by exact_mod_cast Nat.pow_le_pow_left hr 2
  have hscale : 𝔄^𝔅 ≤
      N^𝔅 * Real.exp 𝔗 := by
    rw [Real.mul_rpow hN.le 𝙫, ← Real.exp_mul]
    apply mul_le_mul_of_nonneg_left _ $ Real.rpow_nonneg hN.le _
    apply Real.exp_le_exp.mpr
    have hp := mul_le_mul_of_nonneg_left hDK $ show 0 ≤ c0*𝔙 by positivity
    nlinarith
  have hbound := mul_le_mul (mul_le_mul (mul_le_mul hr2 (le_refl 𝔇)  𝖠₃  $ sq_nonneg _ )
      hCpower  𝖠₃  𝖠₃ )
    (mul_le_mul hscale hlogpower  𝖠₃  𝖠₃ )  𝖠₃  𝖠₃
  calc
    _ = 𝘴₁ * 𝔇 * cardinalBandDimensionConstant d ^𝔍 *
        (𝔄^𝔅 * 𝔐^𝔊) := by
      unfold cardinalBandSquareBudget cardinalBandDimensionConstant
      ring
    𝖦 := hbound
    𝘿 := by
      unfold lowerAliasSpatialA lowerAliasSpatialL cardinalBandDimensionConstant
      rw [show Real.exp ((𝔈+R)*M) =
        Real.exp 𝔗 * Real.exp (R*M) by rw [← Real.exp_add]; ring]
      ring

def lowerAliasSpatialFixedL (d : ℕ) (θ c0 : ℝ) : ℝ :=
  lowerAliasSpatialL d (lowerAliasFineTargetBound d θ c0) c0 $ (𝔏+8)/4+1

𝗇 𝔉 𝙶
𝗇 𝔎 𝗫
𝗇 𝔔 𝙵
theorem lowerSaddleD_le_fixed_linear (hd : 𝗆)
    (hM : 1 ≤ 𝔚 𝔎) :
    𝔔 ≤ (𝔉+1) * 𝔎 := by
  have hceil := Nat.ceil_lt_add_one $ show 0 ≤ 𝔉*𝔎 by positivity
  change 𝔔 < 𝔉*𝔎+1 at hceil
  nlinarith

theorem lowerAliasSpatialFixedL_nonneg (hd : 4 ≤ d) θ
    (hc0 : 0 ≤ c0) : 0 ≤ lowerAliasSpatialFixedL d θ c0 :=
  lowerAliasSpatialL_nonneg hd hc0 𝖠₃
