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
def stretchConstant (s d τ : ℝ) : ℝ :=
  4 * Real.sqrt (2 * τ * (s - 1) * (d - 4 * s) / (d + 4) ^ 3)

theorem half_minus_rateExponent  (hs : 1 < s) (hd : 4 * s < d) :
    1 / 2 - rateExponent s d = (d - 4 * s) / (2 * (d + 4)) := by
  have : d + 4 ≠ 0 := by linarith
  unfold rateExponent
  field_simp
  ring

theorem stretchConstant_pos  (hs : 1 < s) (hd : 4 * s < d)
    (hτ : 0 < τ) : 0 < stretchConstant s d τ := by
  unfold stretchConstant
  have : 0 < d + 4 := by linarith
  have : 0 < s - 1 := by linarith
  have : 0 < d - 4 * s := by linarith
  positivity

/-- The upper allocation's leading square-root coefficient `a_*`. -/
def upperSaddleCoefficient (s d τ : ℝ) : ℝ :=
  Real.sqrt (8 * τ * (d - 4 * s) / ((d + 4) * (s - 1)))

/-- The lower allocation's leading coefficient `m_*`. -/
def lowerSaddleCoefficient (s d τ : ℝ) : ℝ :=
  Real.sqrt (8 * (d - 4 * s) * (s - 1) / (d ^ 2 * (d + 4) * τ))

/-- The upper saddle identifies the paper's stretched-exponential constant. -/
theorem upper_saddle_stretchConstant  (hs : 1 < s)
    (hd : 4 * s < d) (hτ : 0 < τ) :
    2 * (s - 1) / (d + 4) * upperSaddleCoefficient s d τ = stretchConstant s d τ := by
  have : 0 < d := by linarith
  have : 0 < d + 4 := by linarith
  have : 0 < s - 1 := by linarith
  have : 0 < d - 4 * s := by linarith
  have hu : 0 ≤ 8 * τ * (d - 4 * s) / ((d + 4) * (s - 1)) := by positivity
  have hk : 0 ≤ 2 * τ * (s - 1) * (d - 4 * s) / (d + 4) ^ 3 := by positivity
  unfold upperSaddleCoefficient stretchConstant
  apply (sq_eq_sq₀ (by positivity) (by positivity)).1
  simp only [mul_pow, div_pow, Real.sq_sqrt hu, Real.sq_sqrt hk]
  field_simp
  ring

/-- Logarithm of the unrounded bandwidth `h°` in `eq:Urate-h`. -/
def spatialBalanceLog (s d L T : ℝ) : ℝ :=
  2 / (d + 4) * (-L + 2 * ((s - 1) / d) * (L + T))

/-- Exact equality of the bias and pair-noise logarithms, before rounding. -/
theorem spatial_balance  (hs : 1 < s) (hd : 4 * s < d) (L T ) :
    2 * spatialBalanceLog s d L T - 2 * ((s - 1) / d) * (L + T) =
      -L - d / 2 * spatialBalanceLog s d L T := by
  have : d ≠ 0 := by linarith
  have : d + 4 ≠ 0 := by linarith
  unfold spatialBalanceLog
  field_simp
  ring

/-- The exact risk exponent identity in `eq:Urate-scale`. -/
theorem spatial_balance_rate  (hs : 1 < s) (hd : 4 * s < d) (L T ) :
    -L - d / 2 * spatialBalanceLog s d L T =
      -rateExponent s d * L - 2 * (s - 1) / (d + 4) * T := by
  have : d ≠ 0 := by linarith
  have : d + 4 ≠ 0 := by linarith
  unfold spatialBalanceLog rateExponent
  field_simp
  ring

/-- Exact algebra of the lower saddle's logarithm of `N`. -/
def lowerSaddleLogN (s d L ω τ M : ℝ) : ℝ :=
  ((d - 4 * s) / d * L - (1 + 4 * s / d) * ω - 2 * τ * M) / (d + 4)

/-- Logarithm of the general rate scale, with arbitrary log-power `a`. -/
def rateLog (lam κ a x : ℝ) : ℝ :=
  -lam * Real.log x - κ * Real.sqrt (Real.log x) + a * Real.log (Real.log x)

/-- A total real-valued definition of the scale; asymptotic results use `x > 1`. -/
def rateScale (lam κ a x : ℝ) : ℝ := Real.exp (rateLog lam κ a x)

theorem rateScale_pos (lam κ a x ) : 0 < rateScale lam κ a x := Real.exp_pos _

theorem log_rateScale (lam κ a x ) :
    Real.log (rateScale lam κ a x) = rateLog lam κ a x := Real.log_exp _

theorem rateScale_eq_base_mul_correction (lam κ a x ) :
    rateScale lam κ a x = Real.exp (-lam * Real.log x) *
      Real.exp (-κ * Real.sqrt (Real.log x) + a * Real.log (Real.log x)) := by
  unfold rateScale rateLog
  rw [← Real.exp_add]
  congr 1
  ring

/-- Equivalence with the paper's product using real powers. -/
theorem rateScale_eq_rpow (lam κ a )  (hx : 1 < x) :
    rateScale lam κ a x =
      x ^ (-lam) * Real.exp (-κ * Real.sqrt (Real.log x)) * (Real.log x) ^ a := by
  rw [Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos (Real.log_pos hx)]
  unfold rateScale rateLog
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem tendsto_sqrt_div_self :
    Tendsto (fun x => Real.sqrt x / x) atTop (𝓝 0) := by
  refine (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 2 : ℝ))).congr' ?_
  filter_upwards [eventually_gt_atTop ↑0] with x hx
  rw [Real.sqrt_eq_rpow, ← Real.rpow_sub_one hx.ne']
  norm_num

theorem tendsto_log_div_sqrt :
    Tendsto (fun x => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
  simpa only [Real.sqrt_eq_rpow] using
    (isLittleO_log_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))).tendsto_div_nhds_zero

theorem tendsto_sqrt_log_div_log :
    Tendsto (fun x => Real.sqrt (Real.log x) / Real.log x) atTop (𝓝 0) :=
  tendsto_sqrt_div_self.comp Real.tendsto_log_atTop

theorem tendsto_loglog_div_log :
    Tendsto (fun x => Real.log (Real.log x) / Real.log x) atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop

theorem tendsto_const_div_log (c ) :
    Tendsto (fun x => c / Real.log x) atTop (𝓝 0) := by
  simpa [div_eq_mul_inv] using (Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul c)

/-- Every fixed square-root and iterated-log correction is subpolynomial. -/
theorem tendsto_correction_div_log (κ a ) :
    Tendsto (fun x =>
      (-κ * Real.sqrt (Real.log x) + a * Real.log (Real.log x)) / Real.log x)
      atTop (𝓝 0) := by
  have h := (tendsto_sqrt_log_div_log.const_mul (-κ)).add
    (tendsto_loglog_div_log.const_mul a)
  convert h using 1 <;> simp [add_div, mul_div_assoc, neg_div]

/-- A stretched exponential in `sqrt(log x)` defeats every fixed log-power. -/
theorem tendsto_stretched_log_factor  (hκ : 0 < κ) (a ) :
    Tendsto (fun x =>
      Real.exp (-κ * Real.sqrt (Real.log x) + a * Real.log (Real.log x)))
      atTop (𝓝 0) := by
  have hs : Tendsto (fun x => Real.sqrt (Real.log x)) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow, Function.comp_def] using
      (tendsto_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))).comp Real.tendsto_log_atTop
  have hl := tendsto_log_div_sqrt.comp Real.tendsto_log_atTop
  have hm := hs.atTop_mul_neg (neg_neg_of_pos hκ) (by simpa using tendsto_const_nhds.add (hl.const_mul a))
  apply Real.tendsto_exp_atBot.comp
  refine hm.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have  := (Real.sqrt_pos.2 (Real.log_pos hx)).ne'
  field_simp

theorem tendsto_normalized_log_scale (lam κ a c ) :
    Tendsto (fun x => (-c - rateLog lam κ a x) / Real.log x) atTop (𝓝 lam) := by
  have h := (tendsto_const_nhds (x := lam)).sub
    (tendsto_correction_div_log κ a) |>.sub (tendsto_const_div_log c)
  simp only [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  unfold rateLog
  field_simp
  ring

/-- The paper indexes risk by integer sample size. The bracket remains a hypothesis. -/
def HasNatRateBracket (risk : ℕ → ℝ) (lam κ a Γ : ℝ) : Prop :=
  ∃ c C, 0 < c ∧ 0 < C ∧
    ∀ᶠ n : ℕ in atTop, c * rateScale lam κ a n ≤ risk n ∧
      risk n ≤ C * rateScale lam κ (a + Γ) n

/-- Conditional natural-sample-size version of the exponent limit. -/
theorem exponent_limit_nat_of_rateBracket {risk : ℕ → ℝ} {lam κ a Γ : ℝ}
    (h : HasNatRateBracket risk lam κ a Γ) :
    Tendsto (fun n => -Real.log (risk n) / Real.log n) atTop (𝓝 lam) := by
  obtain ⟨c, C, hc, hC, hb⟩ := h
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    ((tendsto_normalized_log_scale lam κ (a + Γ) (Real.log C)).comp tendsto_natCast_atTop_atTop)
    ((tendsto_normalized_log_scale lam κ a (Real.log c)).comp tendsto_natCast_atTop_atTop)
  · filter_upwards [hb, tendsto_natCast_atTop_atTop.eventually
      (eventually_gt_atTop (1 : ℝ))] with n hn hn₁
    have hl := Real.log_le_log ((mul_pos hc (rateScale_pos _ _ _ _)).trans_le hn.1) hn.2
    rw [Real.log_mul hC.ne' (rateScale_pos _ _ _ _).ne', log_rateScale] at hl
    exact div_le_div_of_nonneg_right (by linarith) (Real.log_pos hn₁).le
  · filter_upwards [hb, tendsto_natCast_atTop_atTop.eventually
      (eventually_gt_atTop (1 : ℝ))] with n hn hn₁
    have hl := Real.log_le_log (mul_pos hc (rateScale_pos _ _ _ _)) hn.1
    rw [Real.log_mul hc.ne' (rateScale_pos _ _ _ _).ne', log_rateScale] at hl
    exact div_le_div_of_nonneg_right (by linarith) (Real.log_pos hn₁).le

end NearlyMinimax
