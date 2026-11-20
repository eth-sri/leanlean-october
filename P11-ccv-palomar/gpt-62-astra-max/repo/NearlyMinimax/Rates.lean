module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

@[expose] public section

/-!
# Rate algebra and conditional asymptotic consequences

This file formalizes the algebra of the exponents and the analytic consequences
of the rate bracket in the paper. The statistical upper and lower bounds are
explicit hypotheses of the corollaries; they are not asserted here.
-/

noncomputable section

namespace NearlyMinimax

open Filter
open scoped Topology

section
variable (s d τ : ℝ)

/-- The root-mean-square polynomial exponent. -/
def rateExponent : ℝ := 2 * (s + 1) / (d + 4)

/-- The logarithmic power in the lower risk scale. -/
def lowerLogPower : ℝ := (s - 1) / (d + 4)

/-- The common stretched-exponential constant in the paper. -/
def stretchConstant : ℝ :=
  4 * Real.sqrt (2 * τ * (s - 1) * (d - 4 * s) / (d + 4) ^ 3)

end

section
variable {s d : ℝ} (lam κ a x : ℝ) {τ : ℝ} (hs : 1 < s) (hd : 4 * s < d) (hτ : 0 < τ) (L T : ℝ)

include hs hd in
theorem half_minus_rateExponent :
    1 / 2 - rateExponent s d = (d - 4 * s) / (2 * (d + 4)) := by
  grind [rateExponent]

include hs hd hτ in
theorem stretchConstant_pos : 0 < stretchConstant s d τ := by
  unfold stretchConstant
  have : 0 < d + 4 := by linarith
  positivity

/-- The upper allocation's leading square-root coefficient `a_*`. -/
def upperSaddleCoefficient (s d τ : ℝ) : ℝ :=
  Real.sqrt (8 * τ * (d - 4 * s) / ((d + 4) * (s - 1)))

/-- The lower allocation's leading coefficient `m_*`. -/
def lowerSaddleCoefficient (s d τ : ℝ) : ℝ :=
  Real.sqrt (8 * (d - 4 * s) * (s - 1) / (d ^ 2 * (d + 4) * τ))

include hs hd hτ in
/-- The upper saddle identifies the paper's stretched-exponential constant. -/
theorem upper_saddle_stretchConstant :
    2 * (s - 1) / (d + 4) * upperSaddleCoefficient s d τ = stretchConstant s d τ := by
  have hdp : 0 < d + 4 := by linarith
  have hu : 0 ≤ 8 * τ * (d - 4 * s) / ((d + 4) * (s - 1)) := by positivity
  have hk : 0 ≤ 2 * τ * (s - 1) * (d - 4 * s) / (d + 4) ^ 3 := by positivity
  unfold upperSaddleCoefficient stretchConstant
  apply (sq_eq_sq₀ (by positivity) (by positivity)).1
  simp [mul_pow, div_pow, Real.sq_sqrt hu, Real.sq_sqrt hk]
  field_simp
  ring

include hs hd hτ in
/-- The lower saddle gives exactly the same stretched-exponential constant. -/
theorem lower_saddle_stretchConstant :
    2 * d * τ / (d + 4) * lowerSaddleCoefficient s d τ = stretchConstant s d τ := by
  have hd₀ : 0 < d := by linarith
  have hm : 0 ≤ 8 * (d - 4 * s) * (s - 1) / (d ^ 2 * (d + 4) * τ) := by positivity
  have hk : 0 ≤ 2 * τ * (s - 1) * (d - 4 * s) / (d + 4) ^ 3 := by positivity
  unfold lowerSaddleCoefficient stretchConstant
  apply (sq_eq_sq₀ (by positivity) (by positivity)).1
  simp [mul_pow, div_pow, Real.sq_sqrt hm, Real.sq_sqrt hk]
  field_simp
  ring

/-- Logarithm of the unrounded bandwidth `h°` in `eq:Urate-h`. -/
def spatialBalanceLog (s d L T : ℝ) : ℝ :=
  2 / (d + 4) * (-L + 2 * ((s - 1) / d) * (L + T))

include hs hd in
/-- Exact equality of the bias and pair-noise logarithms, before rounding. -/
theorem spatial_balance :
    2 * spatialBalanceLog s d L T - 2 * ((s - 1) / d) * (L + T) =
      -L - d / 2 * spatialBalanceLog s d L T := by
  grind [spatialBalanceLog]

include hs hd in
/-- The exact risk exponent identity in `eq:Urate-scale`. -/
theorem spatial_balance_rate :
    -L - d / 2 * spatialBalanceLog s d L T =
      -rateExponent s d * L - 2 * (s - 1) / (d + 4) * T := by
  grind [spatialBalanceLog, rateExponent]

/-- Exact algebra of the lower saddle's logarithm of `N`. -/
def lowerSaddleLogN (s d L ω τ M : ℝ) : ℝ :=
  ((d - 4 * s) / d * L - (1 + 4 * s / d) * ω - 2 * τ * M) / (d + 4)

include hs hd in
/-- The first line of `eq:LB-saddle`, excluding the constant amplitude term. -/
theorem lower_saddle_rate (ω τ M : ℝ) :
    -2 * s / d * (L + ω) - 2 * lowerSaddleLogN s d L ω τ M - τ * M =
      -rateExponent s d * L - (2 * (s - 1) * ω + d * τ * M) / (d + 4) := by
  have h₁ : d ≠ 0 := by linarith
  have h₂ : d + 4 ≠ 0 := by linarith
  unfold lowerSaddleLogN rateExponent
  field_simp
  ring

/-- Logarithm of the general rate scale, with arbitrary log-power `a`. -/
def rateLog : ℝ :=
  -lam * Real.log x - κ * Real.sqrt (Real.log x) + a * Real.log (Real.log x)

/-- A total real-valued definition of the scale; asymptotic results use `x > 1`. -/
def rateScale : ℝ := Real.exp (rateLog lam κ a x)

theorem rateScale_pos : 0 < rateScale lam κ a x := Real.exp_pos _

theorem log_rateScale :
    Real.log (rateScale lam κ a x) = rateLog lam κ a x := Real.log_exp _

theorem rateScale_eq_base_mul_correction :
    rateScale lam κ a x = Real.exp (-lam * Real.log x) *
      Real.exp (-κ * Real.sqrt (Real.log x) + a * Real.log (Real.log x)) := by
  unfold rateScale rateLog
  rw [← Real.exp_add]
  congr 1
  ring

/-- Equivalence with the paper's product using real powers. -/
theorem rateScale_eq_rpow {x : ℝ} (hx : 1 < x) :
    rateScale lam κ a x =
      x ^ (-lam) * Real.exp (-κ * Real.sqrt (Real.log x)) * (Real.log x) ^ a := by
  have hl  := Real.log_pos hx
  rw [Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos hl]
  unfold rateScale rateLog
  rw [← Real.exp_add, ← Real.exp_add]
  ring

end

theorem tendsto_sqrt_div_self :
    Tendsto (fun x : ℝ => Real.sqrt x / x) atTop (𝓝 0) := by
  refine (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 2 : ℝ))).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.sqrt_eq_rpow, ← Real.rpow_sub_one hx.ne']
  norm_num

theorem tendsto_log_div_sqrt :
    Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
  simpa only [Real.sqrt_eq_rpow] using
    (isLittleO_log_rpow_atTop (by norm_num)).tendsto_div_nhds_zero

theorem tendsto_sqrt_log_div_log :
    Tendsto (fun x : ℝ => Real.sqrt (Real.log x) / Real.log x) atTop (𝓝 0) :=
  tendsto_sqrt_div_self.comp Real.tendsto_log_atTop

theorem tendsto_loglog_div_log :
    Tendsto (fun x : ℝ => Real.log (Real.log x) / Real.log x) atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop

section
variable (lam κ a c : ℝ)

theorem tendsto_const_div_log :
    Tendsto (fun x : ℝ => c / Real.log x) atTop (𝓝 0) := by
  simpa [div_eq_mul_inv] using (Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul c)

/-- Every fixed square-root and iterated-log correction is subpolynomial. -/
theorem tendsto_correction_div_log :
    Tendsto (fun x : ℝ =>
      (-κ * Real.sqrt (Real.log x) + a * Real.log (Real.log x)) / Real.log x)
      atTop (𝓝 0) := by
  convert ((tendsto_sqrt_log_div_log.const_mul (-κ)).add (tendsto_loglog_div_log.const_mul a)) using 1 <;> simp [add_div, mul_div_assoc, neg_div]

/-- A stretched exponential in `sqrt(log x)` defeats every fixed log-power. -/
theorem tendsto_stretched_log_factor {κ : ℝ} (hκ : 0 < κ) (a : ℝ) :
    Tendsto (fun x : ℝ =>
      Real.exp (-κ * Real.sqrt (Real.log x) + a * Real.log (Real.log x)))
      atTop (𝓝 0) := by
  have hs : Tendsto (Real.sqrt ∘ Real.log) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
      (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  have hl := tendsto_log_div_sqrt.comp Real.tendsto_log_atTop
  apply Real.tendsto_exp_atBot.comp
  refine (hs.atTop_mul_neg (neg_neg_of_pos hκ) (by simpa using tendsto_const_nhds.add (hl.const_mul a))).congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  grind [(Real.sqrt_pos.2 (Real.log_pos hx)).ne']

/-- A quantitative eventual form of subpolynomiality, on both sides. -/
theorem eventually_correction_between_powers {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      x ^ (-ε) ≤ Real.exp (-κ * Real.sqrt (Real.log x) + a * Real.log (Real.log x)) ∧
      Real.exp (-κ * Real.sqrt (Real.log x) + a * Real.log (Real.log x)) ≤ x ^ ε := by
  have h := tendsto_correction_div_log κ a
  filter_upwards [h.eventually (lt_mem_nhds (neg_lt_zero.2 hε)),
    h.eventually (gt_mem_nhds hε), eventually_gt_atTop 1] with x hlo hhi hx
  have hl  := Real.log_pos hx
  have hx₀ : 0 < x := by linarith
  rw [Real.rpow_def_of_pos hx₀, Real.rpow_def_of_pos hx₀]
  constructor
  · apply Real.exp_le_exp.2
    have := (lt_div_iff₀ hl).1 hlo
    linarith
  · apply Real.exp_le_exp.2
    have := (div_lt_iff₀ hl).1 hhi
    linarith

theorem tendsto_normalized_log_scale :
    Tendsto (fun x : ℝ => (-c - rateLog lam κ a x) / Real.log x) atTop (𝓝 lam) := by
  have h := (tendsto_const_nhds (x := lam)).sub
    (tendsto_correction_div_log κ a) |>.sub (tendsto_const_div_log c)
  simp at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hl  := (Real.log_pos hx).ne'
  unfold rateLog
  field_simp
  ring

end

/-- The paper indexes risk by integer sample size. The bracket remains a hypothesis. -/
def HasNatRateBracket (risk : ℕ → ℝ) (lam κ a Γ : ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ᶠ n : ℕ in atTop, c * rateScale lam κ a (n : ℝ) ≤ risk n ∧
      risk n ≤ C * rateScale lam κ (a + Γ) (n : ℝ)

/-- Conditional natural-sample-size version of the exponent limit. -/
theorem exponent_limit_nat_of_rateBracket {risk : ℕ → ℝ} {lam κ a Γ : ℝ}
    (h : HasNatRateBracket risk lam κ a Γ) :
    Tendsto (fun n : ℕ => -Real.log (risk n) / Real.log (n : ℝ)) atTop (𝓝 lam) := by
  obtain ⟨c, C, hc, hC, hb⟩ := h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    ((tendsto_normalized_log_scale lam κ (a + Γ) (Real.log C)).comp tendsto_natCast_atTop_atTop)
    ((tendsto_normalized_log_scale lam κ a (Real.log c)).comp tendsto_natCast_atTop_atTop)
  · filter_upwards [hb, tendsto_natCast_atTop_atTop.eventually
      (eventually_gt_atTop (1 : ℝ))] with n hn hn₁
    have hl := Real.log_le_log ((mul_pos hc (rateScale_pos ..)).trans_le hn.1) hn.2
    rw [Real.log_mul hC.ne' (rateScale_pos ..).ne', log_rateScale] at hl
    exact div_le_div_of_nonneg_right (by linarith) (Real.log_pos hn₁).le
  · filter_upwards [hb, tendsto_natCast_atTop_atTop.eventually
      (eventually_gt_atTop (1 : ℝ))] with n hn hn₁
    have hl := Real.log_le_log (mul_pos hc (rateScale_pos ..)) hn.1
    rw [Real.log_mul hc.ne' (rateScale_pos ..).ne', log_rateScale] at hl
    exact div_le_div_of_nonneg_right (by linarith) (Real.log_pos hn₁).le

end NearlyMinimax
