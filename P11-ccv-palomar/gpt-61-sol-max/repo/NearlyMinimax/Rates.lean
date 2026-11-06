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

/-- The root-mean-square polynomial exponent. -/
def rateExponent (s d : ℝ) : ℝ := 2 * (s + 1) / (d + 4)

/-- The logarithmic power in the lower risk scale. -/
def lowerLogPower (s d : ℝ) : ℝ := (s - 1) / (d + 4)

/-- The common stretched-exponential constant in the paper. -/
def stretchConstant s d τ  :=
  4 * Real.sqrt (2 * τ * (s - 1) * (d - 4 * s) / (d + 4) ^ 3)

theorem half_minus_rateExponent {s d } (hs : 1 < s) (hd : 4 * s < d) :
    1 / 2 - rateExponent s d = (d - 4 * s) / (2 * (d + 4)) := by
  have h : d + 4 ≠ 0 := by linarith
  unfold rateExponent
  field_simp
  ring

theorem stretchConstant_pos {s d τ } (hs : 1 < s) (hd : 4 * s < d)
    (hτ : 0 < τ) : 0 < stretchConstant s d τ := by
  unfold stretchConstant
  have : 0 < d + 4 := by linarith
  simp_all

/-- The upper allocation's leading square-root coefficient `a_*`. -/
def upperSaddleCoefficient s d τ  :=
  Real.sqrt (8 * τ * (d - 4 * s) / ((d + 4) * (s - 1)))

/-- The lower allocation's leading coefficient `m_*`. -/
def lowerSaddleCoefficient s d τ  :=
  Real.sqrt (8 * (d - 4 * s) * (s - 1) / (d ^ 2 * (d + 4) * τ))

section
variable {s d τ : ℝ} (hs : 1 < s) (hd : 4 * s < d) (hτ : 0 < τ)
include hs hd hτ

/-- The upper saddle identifies the paper's stretched-exponential constant. -/
theorem upper_saddle_stretchConstant  :
    2 * (s - 1) / (d + 4) * upperSaddleCoefficient s d τ = stretchConstant s d τ := by
  have hd₀ : 0 < d := by linarith
  
  
  
  have hu : 0 ≤ 8 * τ * (d - 4 * s) / ((d + 4) * (s - 1)) := by positivity
  have hk : 0 ≤ 2 * τ * (s - 1) * (d - 4 * s) / (d + 4) ^ 3 := by positivity
  unfold upperSaddleCoefficient stretchConstant
  apply (sq_eq_sq₀ (by positivity) (by positivity)).1
  simp only [mul_pow, div_pow, Real.sq_sqrt hu, Real.sq_sqrt hk]
  field_simp
  ring

/-- The lower saddle gives exactly the same stretched-exponential constant. -/
theorem lower_saddle_stretchConstant  :
    2 * d * τ / (d + 4) * lowerSaddleCoefficient s d τ = stretchConstant s d τ := by
  have hd₀ : 0 < d := by linarith
  
  
  
  have hm : 0 ≤ 8 * (d - 4 * s) * (s - 1) / (d ^ 2 * (d + 4) * τ) := by positivity
  have hk : 0 ≤ 2 * τ * (s - 1) * (d - 4 * s) / (d + 4) ^ 3 := by positivity
  unfold lowerSaddleCoefficient stretchConstant
  apply (sq_eq_sq₀ (by positivity) (by positivity)).1
  simp only [mul_pow, div_pow, Real.sq_sqrt hm, Real.sq_sqrt hk]
  field_simp
  ring
end


/-- Logarithm of the unrounded bandwidth `h°` in `eq:Urate-h`. -/
def spatialBalanceLog (s d L T : ℝ) : ℝ :=
  2 / (d + 4) * (-L + 2 * ((s - 1) / d) * (L + T))

section
variable {s d : ℝ} (hs : 1 < s) (hd : 4 * s < d)
include hs hd

/-- Exact equality of the bias and pair-noise logarithms, before rounding. -/
theorem spatial_balance  L T :
    2 * spatialBalanceLog s d L T - 2 * ((s - 1) / d) * (L + T) =
      -L - d / 2 * spatialBalanceLog s d L T := by
  
  have h₂ : d + 4 ≠ 0 := by linarith
  unfold spatialBalanceLog
  field_simp
  ring

/-- The exact risk exponent identity in `eq:Urate-scale`. -/
theorem spatial_balance_rate  L T :
    -L - d / 2 * spatialBalanceLog s d L T =
      -rateExponent s d * L - 2 * (s - 1) / (d + 4) * T := by
  have h₁ : d ≠ 0 := by linarith
  have h₂ : d + 4 ≠ 0 := by linarith
  unfold spatialBalanceLog rateExponent
  field_simp
  ring
end


/-- Exact algebra of the lower saddle's logarithm of `N`. -/
def lowerSaddleLogN (s d L ω τ M : ℝ) : ℝ :=
  ((d - 4 * s) / d * L - (1 + 4 * s / d) * ω - 2 * τ * M) / (d + 4)

/-- The first line of `eq:LB-saddle`, excluding the constant amplitude term. -/
theorem lower_saddle_rate {s d } (hs : 1 < s) (hd : 4 * s < d)
    L ω τ M :
    -2 * s / d * (L + ω) - 2 * lowerSaddleLogN s d L ω τ M - τ * M =
      -rateExponent s d * L - (2 * (s - 1) * ω + d * τ * M) / (d + 4) := by
  have h₁ : d ≠ 0 := by linarith
  have h₂ : d + 4 ≠ 0 := by linarith
  unfold lowerSaddleLogN rateExponent
  field_simp
  ring

section
variable (lam κ a x : ℝ)
include lam κ a x

/-- Logarithm of the general rate scale, with arbitrary log-power `a`. -/
def rateLog   :=
  -lam * Real.log x - κ * Real.sqrt (Real.log x) + a * Real.log (Real.log x)

/-- A total real-valued definition of the scale; asymptotic results use `x > 1`. -/
def rateScale   := Real.exp (rateLog lam κ a x)

theorem rateScale_pos  : 0 < rateScale lam κ a x := Real.exp_pos _

theorem log_rateScale  :
    Real.log (rateScale lam κ a x) = rateLog lam κ a x := Real.log_exp _

theorem rateScale_eq_base_mul_correction  :
    rateScale lam κ a x = Real.exp (-lam * Real.log x) *
      Real.exp (-κ * Real.sqrt (Real.log x) + a * Real.log (Real.log x)) := by
  unfold rateScale rateLog
  rw [← Real.exp_add]
  
  ring
end


/-- Equivalence with the paper's product using real powers. -/
theorem rateScale_eq_rpow lam κ a {x } (hx : 1 < x) :
    rateScale lam κ a x =
      x ^ (-lam) * Real.exp (-κ * Real.sqrt (Real.log x)) * (Real.log x) ^ a := by
  have hx₀ : 0 < x := by linarith
  have hl  := Real.log_pos hx
  rw [Real.rpow_def_of_pos hx₀, Real.rpow_def_of_pos hl]
  unfold rateScale rateLog
  rw [← Real.exp_add, ← Real.exp_add]
  
  ring

theorem tendsto_sqrt_div_self :
    Tendsto (fun x  => Real.sqrt x / x) atTop (𝓝 0) := by
  refine (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 2 : ℝ))).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.sqrt_eq_rpow, ← Real.rpow_sub_one hx.ne']
  norm_num

theorem tendsto_log_div_sqrt :
    Tendsto (fun x  => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
  simpa only [Real.sqrt_eq_rpow] using
    (isLittleO_log_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))).tendsto_div_nhds_zero

theorem tendsto_sqrt_log_div_log :
    Tendsto (fun x  => Real.sqrt (Real.log x) / Real.log x) atTop (𝓝 0) :=
  tendsto_sqrt_div_self.comp Real.tendsto_log_atTop

theorem tendsto_loglog_div_log :
    Tendsto (fun x  => Real.log (Real.log x) / Real.log x) atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop

theorem tendsto_const_div_log c :
    Tendsto (fun x  => c / Real.log x) atTop (𝓝 0) := by
  simpa [div_eq_mul_inv] using (Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul c)

/-- Every fixed square-root and iterated-log correction is subpolynomial. -/
theorem tendsto_correction_div_log κ a :
    Tendsto (fun x  =>
      (-κ * Real.sqrt (Real.log x) + a * Real.log (Real.log x)) / Real.log x)
      atTop (𝓝 0) := by
  have h := (tendsto_sqrt_log_div_log.const_mul (-κ)).add
    (tendsto_loglog_div_log.const_mul a)
  grind

/-- A stretched exponential in `sqrt(log x)` defeats every fixed log-power. -/
theorem tendsto_stretched_log_factor {κ } (hκ : 0 < κ) a :
    Tendsto (fun x  =>
      Real.exp (-κ * Real.sqrt (Real.log x) + a * Real.log (Real.log x)))
      atTop (𝓝 0) := by
  have hs : Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
      (tendsto_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))).comp Real.tendsto_log_atTop
  have hl := tendsto_log_div_sqrt.comp Real.tendsto_log_atTop
  have hr : Tendsto (fun x : ℝ => -κ + a *
      (Real.log (Real.log x) / Real.sqrt (Real.log x))) atTop (𝓝 (-κ)) := by
    simpa using tendsto_const_nhds.add (hl.const_mul a)
  have hm := hs.atTop_mul_neg (neg_neg_of_pos hκ) hr
  apply Real.tendsto_exp_atBot.comp
  refine hm.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hp  := (Real.sqrt_pos.2 (Real.log_pos hx)).ne'
  field_simp

/-- A quantitative eventual form of subpolynomiality, on both sides. -/
theorem eventually_correction_between_powers κ a {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      x ^ (-ε) ≤ Real.exp (-κ * Real.sqrt (Real.log x) + a * Real.log (Real.log x)) ∧
      Real.exp (-κ * Real.sqrt (Real.log x) + a * Real.log (Real.log x)) ≤ x ^ ε := by
  have h := tendsto_correction_div_log κ a
  filter_upwards [h.eventually (lt_mem_nhds (neg_lt_zero.2 hε)),
    h.eventually (gt_mem_nhds hε), eventually_gt_atTop (1 : ℝ)] with x hlo hhi hx
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

theorem tendsto_normalized_log_scale lam κ a c :
    Tendsto (fun x  => (-c - rateLog lam κ a x) / Real.log x) atTop (𝓝 lam) := by
  have h := (tendsto_const_nhds (x := lam)).sub
    (tendsto_correction_div_log κ a) |>.sub (tendsto_const_div_log c)
  simp only [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hl  := (Real.log_pos hx).ne'
  unfold rateLog
  field_simp
  ring

/-- The paper indexes risk by integer sample size. The bracket remains a hypothesis. -/
def HasNatRateBracket (risk : ℕ → ℝ) lam κ a Γ  :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ᶠ n : ℕ in atTop, c * rateScale lam κ a (n : ℝ) ≤ risk n ∧
      risk n ≤ C * rateScale lam κ (a + Γ) (n : ℝ)

/-- Conditional natural-sample-size version of the exponent limit. -/
theorem exponent_limit_nat_of_rateBracket {risk } {lam κ a Γ }
    (h : HasNatRateBracket risk lam κ a Γ) :
    Tendsto (fun n  => -Real.log (risk n) / Real.log n) atTop (𝓝 lam) := by
  obtain ⟨c, C, hc, hC, hb⟩ := h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    ((tendsto_normalized_log_scale lam κ (a + Γ) (Real.log C)).comp tendsto_natCast_atTop_atTop)
    ((tendsto_normalized_log_scale lam κ a (Real.log c)).comp tendsto_natCast_atTop_atTop)
  · filter_upwards [hb, tendsto_natCast_atTop_atTop.eventually
      (eventually_gt_atTop (1 : ℝ))] with n hn hn₁
    have hr  := (mul_pos hc (rateScale_pos _ _ _ _)).trans_le hn.1
    have hl := Real.log_le_log hr hn.2
    rw [Real.log_mul hC.ne' (rateScale_pos _ _ _ _).ne', log_rateScale] at hl
    exact div_le_div_of_nonneg_right (by linarith) (Real.log_pos hn₁).le
  · filter_upwards [hb, tendsto_natCast_atTop_atTop.eventually
      (eventually_gt_atTop (1 : ℝ))] with n hn hn₁
    have hl := Real.log_le_log (mul_pos hc (rateScale_pos _ _ _ _)) hn.1
    rw [Real.log_mul hc.ne' (rateScale_pos _ _ _ _).ne', log_rateScale] at hl
    exact div_le_div_of_nonneg_right (by linarith) (Real.log_pos hn₁).le

end NearlyMinimax
