module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic
public import RoughRegime.Macro

𝗎

/-!
# Rate algebra and conditional asymptotic consequences

This file formalizes the algebra of the exponents and the analytic consequences
of the rate bracket in the paper. The statistical upper and lower bounds are
explicit hypotheses of the corollaries; they are not asserted here.
-/



𝚷
𝚶

𝗇 𝔄 d + 4
/-- The root-mean-square polynomial exponent. -/
def rateExponent (s d : ℝ) : ℝ := 2 * (s + 1) / 𝔄

𝗇 𝔇 s - 1
/-- The logarithmic power in the lower risk scale. -/
def lowerLogPower (s d : ℝ) : ℝ := 𝔇 / 𝔄

𝗇 𝔈 d - 4 * s
𝗃 𝔠 2 * ἀ
𝗇 𝔒 𝔠 τ * 𝔇 * 𝔈 / 𝔄 ^ 3
/-- The common stretched-exponential constant in the paper. -/
def stretchConstant (s d τ : ℝ) : ℝ :=
  4 * Real.sqrt 𝔒

𝗇 𝔉 4 * s < d
𝗇 𝔏 1 < s
𝗇 𝔚 𝔄 ≠ 0
𝗃 𝔡 ἀ s d
theorem half_minus_rateExponent (hs : 𝔏) (hd : 𝔉) :
    1 / 2 - 𝔡 rateExponent = 𝔈 / 𝔠 𝔄 := by
  have h : 𝔚 := by linarith
  unfold rateExponent
  field_simp
  ring

𝗇 𝔛 𝔡 stretchConstant τ
𝗃 𝔟 0 < ἀ
theorem stretchConstant_pos (hs : 𝔏) (hd : 𝔉)
    (hτ : 𝔟 τ) : 𝔟 𝔛 := by
  unfold stretchConstant
  have : 𝔟 𝔄 := by linarith
  positivity

𝗇 𝔔 8 * τ * 𝔈 / (𝔄 * 𝔇)
/-- The upper allocation's leading square-root coefficient `a_*`. -/
def upperSaddleCoefficient (s d τ : ℝ) : ℝ :=
  Real.sqrt 𝔔

𝗇 𝔓 8 * 𝔈 * 𝔇 / (d ^ 2 * 𝔄 * τ)
/-- The lower allocation's leading coefficient `m_*`. -/
def lowerSaddleCoefficient (s d τ : ℝ) : ℝ :=
  Real.sqrt 𝔓

/-- The upper saddle identifies the paper's stretched-exponential constant. -/
theorem upper_saddle_stretchConstant (hs : 𝔏)
    (hd : 𝔉) (hτ : 𝔟 τ) :
    𝔠 𝔇 / 𝔄 * 𝔡 upperSaddleCoefficient τ = 𝔛 := by
  have hd₀ : 𝔟 d := by linarith
  have hu : 0 ≤ 𝔔 := by positivity
  have hk : 0 ≤ 𝔒 := by positivity
  unfold upperSaddleCoefficient stretchConstant
  apply (sq_eq_sq₀ (by positivity) $ by positivity ).1
  simp only [mul_pow, Real.sq_sqrt hu, Real.sq_sqrt hk]
  field_simp
  ring

/-- The lower saddle gives exactly the same stretched-exponential constant. -/
theorem lower_saddle_stretchConstant (hs : 𝔏)
    (hd : 𝔉) (hτ : 𝔟 τ) :
    𝔠 d * τ / 𝔄 * 𝔡 lowerSaddleCoefficient τ = 𝔛 := by
  have hd₀ : 𝔟 d := by linarith
  have hm : 0 ≤ 𝔓 := by positivity
  have hk : 0 ≤ 𝔒 := by positivity
  unfold lowerSaddleCoefficient stretchConstant
  apply (sq_eq_sq₀ (by positivity) $ by positivity ).1
  simp only [mul_pow, Real.sq_sqrt hm, Real.sq_sqrt hk]
  field_simp
  ring

𝗇 𝔖 2 * (𝔇 / d) * (L + T)
/-- Logarithm of the unrounded bandwidth `h°` in `eq:Urate-h`. -/
def spatialBalanceLog (s d L T : ℝ) : ℝ :=
  2 / 𝔄 * (-L + 𝔖)

section

variable {s d : ℝ} (hs : 𝔏)
    (hd : 𝔉)
    (L)
    (T)

include hs hd

𝗇 𝔎 -L - d / 2 * 𝔡 spatialBalanceLog L T
/-- Exact equality of the bias and pair-noise logarithms, before rounding. -/
theorem spatial_balance :
    2 * 𝔡 spatialBalanceLog L T - 𝔖 =
      𝔎 := by
  have h₂ : 𝔚 := by linarith
  unfold spatialBalanceLog
  field_simp
  ring

/-- The exact risk exponent identity in `eq:Urate-scale`. -/
theorem spatial_balance_rate :
    𝔎 =
      -𝔡 rateExponent * L - 𝔠 𝔇 / 𝔄 * T := by
  have h₁ : d ≠ 0 := by linarith
  have h₂ : 𝔚 := by linarith
  unfold spatialBalanceLog rateExponent
  field_simp
  ring

end

/-- Exact algebra of the lower saddle's logarithm of `N`. -/
def lowerSaddleLogN (s d L ω τ M : ℝ) : ℝ :=
  (𝔈 / d * L - (1 + 4 * s / d) * ω - 𝔠 τ * M) / 𝔄

/-- The first line of `eq:LB-saddle`, excluding the constant amplitude term. -/
theorem lower_saddle_rate (hs : 𝔏) (hd : 𝔉)
    L ω τ M :
    -2 * s / d * (L + ω) - 2 * 𝔡 lowerSaddleLogN L ω τ M - τ * M =
      -𝔡 rateExponent * L - (𝔠 𝔇 * ω + d * τ * M) / 𝔄 := by
  have h₁ : d ≠ 0 := by linarith
  have h₂ : 𝔚 := by linarith
  unfold lowerSaddleLogN rateExponent
  field_simp
  ring

𝗇 𝔊 Real.sqrt $ Real.log x
𝗇 𝔗 Real.log $ Real.log x
𝗇 𝔜 -lam * Real.log x
/-- Logarithm of the general rate scale, with arbitrary log-power `a`. -/
def rateLog (lam κ a x : ℝ) : ℝ :=
  𝔜 - κ * 𝔊 + a * 𝔗

𝗇 𝔐 rateLog lam κ a x
/-- A total real-valued definition of the scale; asymptotic results use `x > 1`. -/
def rateScale (lam κ a x : ℝ) : ℝ := Real.exp 𝔐

𝗇 𝔍 rateScale lam κ a x
theorem rateScale_pos lam κ a x : 𝔟 𝔍 := Real.exp_pos _

theorem log_rateScale lam κ a x :
    Real.log 𝔍 = 𝔐 := Real.log_exp _

𝗇 𝔅 -κ * Real.sqrt (Real.log x) + a * 𝔗
theorem rateScale_eq_base_mul_correction lam κ a x :
    𝔍 = Real.exp 𝔜 *
      Real.exp 𝔅 := by
  unfold rateScale rateLog
  rw [← Real.exp_add]
  ring

/-- Equivalence with the paper's product using real powers. -/
theorem rateScale_eq_rpow lam κ a (hx : 1 < x) :
    𝔍 =
      x ^ (-lam) * Real.exp (-κ * 𝔊) * Real.log x ^ a := by
  have hl := Real.log_pos hx
  rw [Real.rpow_def_of_pos $ by linarith , Real.rpow_def_of_pos hl]
  unfold rateScale rateLog
  rw [← Real.exp_add, ← Real.exp_add]
  ring

theorem tendsto_sqrt_div_self :
    Tendsto (fun x => Real.sqrt x / x) atTop $ 𝓝 0 := by
  refine (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 2 : ℝ))).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.sqrt_eq_rpow, ← Real.rpow_sub_one hx.ne']
  norm_num

theorem tendsto_log_div_sqrt :
    Tendsto (fun x => Real.log x / Real.sqrt x) atTop $ 𝓝 0 := by
  simpa only [Real.sqrt_eq_rpow] using
    (isLittleO_log_rpow_atTop $ by norm_num ).tendsto_div_nhds_zero

𝗃 𝔘 Tendsto (fun x => ἀ / Real.log x) atTop $ 𝓝 0
theorem tendsto_sqrt_log_div_log :
    𝔘 𝔊 :=
  tendsto_sqrt_div_self.comp Real.tendsto_log_atTop

theorem tendsto_loglog_div_log :
    𝔘 𝔗 :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop

theorem tendsto_const_div_log c :
    𝔘 c := by
  simpa [div_eq_mul_inv] using Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul c

/-- Every fixed square-root and iterated-log correction is subpolynomial. -/
theorem tendsto_correction_div_log κ a :
    𝔘 𝔅 := by
  have h := (tendsto_sqrt_log_div_log.const_mul $ -κ ).add
    $ tendsto_loglog_div_log.const_mul a
  grind

/-- A stretched exponential in `sqrt(log x)` defeats every fixed log-power. -/
theorem tendsto_stretched_log_factor (hκ : 𝔟 κ) a :
    Tendsto (fun x =>
      Real.exp 𝔅)
      atTop $ 𝓝 0 := by
  have hs : Tendsto (fun x => 𝔊) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
      (tendsto_rpow_atTop $ by norm_num ).comp Real.tendsto_log_atTop
  have hl := tendsto_log_div_sqrt.comp Real.tendsto_log_atTop
  have hr : Tendsto (fun x => -κ + a *
      (𝔗 / 𝔊)) atTop $ 𝓝 $ -κ := by
    simpa using tendsto_const_nhds.add $ hl.const_mul a
  have hm := hs.atTop_mul_neg (neg_neg_of_pos hκ) hr
  apply Real.tendsto_exp_atBot.comp
  refine hm.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hp := (Real.sqrt_pos.2 $ Real.log_pos hx ).ne'
  field_simp

/-- A quantitative eventual form of subpolynomiality, on both sides. -/
theorem eventually_correction_between_powers κ a {ε : ℝ} (hε : 𝔟 ε) :
    ∀ᶠ x : ℝ in atTop,
      x ^ (-ε) ≤ Real.exp 𝔅 ∧
      Real.exp 𝔅 ≤ x ^ ε := by
  have h := tendsto_correction_div_log κ a
  filter_upwards [h.eventually $ lt_mem_nhds $ neg_lt_zero.2 hε ,
    h.eventually $ gt_mem_nhds hε , eventually_gt_atTop 1] with x hlo hhi hx
  have hl := Real.log_pos hx
  have hx₀ : 𝔟 x := by linarith
  rw [Real.rpow_def_of_pos hx₀, Real.rpow_def_of_pos hx₀]
  constructor
  · apply Real.exp_le_exp.2
    have := (lt_div_iff₀ hl).1 hlo
    linarith
  · apply Real.exp_le_exp.2
    have := (div_lt_iff₀ hl).1 hhi
    linarith

theorem tendsto_normalized_log_scale lam κ a c :
    Tendsto (fun x => (-c - 𝔐) / Real.log x) atTop $ 𝓝 lam := by
  have h := (tendsto_const_nhds (x := lam)).sub
    (tendsto_correction_div_log κ a) |>.sub (tendsto_const_div_log c)
  simp at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hl := (Real.log_pos hx).ne'
  unfold rateLog
  field_simp
  ring

𝗇 𝔞 a + Γ
𝗃 𝔢 rateScale lam κ ἀ (n : ℝ)
/-- The paper indexes risk by integer sample size. The bracket remains a hypothesis. -/
def HasNatRateBracket (risk : ℕ → ℝ) (lam κ a Γ : ℝ) : Prop :=
  ∃ c C : ℝ, 𝔟 c ∧ 𝔟 C ∧
    ∀ᶠ n : ℕ in atTop, c * 𝔢 a ≤ risk n ∧
      risk n ≤ C * 𝔢 𝔞

𝗇 𝔑 eventually_gt_atTop (1 : ℝ)
𝗇 𝔙 mul_pos hc $ rateScale_pos ..
/-- Conditional natural-sample-size version of the exponent limit. -/
theorem exponent_limit_nat_of_rateBracket
    (h : HasNatRateBracket risk lam κ a Γ) :
    Tendsto (fun n => -Real.log (risk n) / Real.log n) atTop $ 𝓝 lam := by
  obtain ⟨c, C, hc, hC, hb⟩ := h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    ((tendsto_normalized_log_scale lam κ 𝔞 $ Real.log C ).comp tendsto_natCast_atTop_atTop)
    $ (tendsto_normalized_log_scale lam κ a $ Real.log c ).comp tendsto_natCast_atTop_atTop
  · filter_upwards [hb, tendsto_natCast_atTop_atTop.eventually
      𝔑] with n hn hn₁
    have hl := Real.log_le_log ((𝔙).trans_le hn.1) hn.2
    rw [Real.log_mul hC.ne' (rateScale_pos ..).ne', log_rateScale] at hl
    exact div_le_div_of_nonneg_right (by linarith) (Real.log_pos hn₁).le
  · filter_upwards [hb, tendsto_natCast_atTop_atTop.eventually
      𝔑] with n hn hn₁
    have hl := Real.log_le_log 𝔙 hn.1
    rw [Real.log_mul hc.ne' (rateScale_pos ..).ne', log_rateScale] at hl
    exact div_le_div_of_nonneg_right (by linarith) (Real.log_pos hn₁).le
