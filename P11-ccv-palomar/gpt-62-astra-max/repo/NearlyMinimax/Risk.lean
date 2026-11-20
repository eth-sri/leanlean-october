module

public import Mathlib

@[expose] public section

/-!
# Deterministic stabilization and score-to-risk comparison

This module formalizes the clipping and denominator-stabilization step
(eq. U14-stab), the fundamental-calculus part of Lemma path-risk, and
its finite-outcome probability specialization.  The path theorem uses an
integrable derivative on the interval; it does not claim the paper's
full absolutely-continuous, almost-everywhere formulation.
-/

open scoped BigOperators
open Set MeasureTheory

namespace NearlyMinimax

set_option backward.isDefEq.respectTransparency false

/-- Projection of a real-valued statistic to an interval. -/
def clip (lo hi x : ℝ) : ℝ := max lo (min hi x)

/-- Projection to the interval is `1`-Lipschitz. -/
theorem clip_lipschitz (lo hi : ℝ) : LipschitzWith 1 (clip lo hi) := ((LipschitzWith.id.const_min hi).const_max lo)

/-- The clipped statistic lies in the designated interval. -/
theorem clip_mem_Icc {lo hi x : ℝ} (hinterval : lo ≤ hi) :
    clip lo hi x ∈ Icc lo hi := ⟨le_max_left _ _, max_le hinterval (min_le_left _ _)⟩

section
variable {lo hi V x : ℝ} (hlo : lo ≤ V) (hhi : V ≤ hi)
include hhi hlo

/-- Any clipped statistic and interval-valued target are separated by
at most the diameter of the interval. -/
theorem clip_error_le_diameter :
    |clip lo hi x - V| ≤ hi - lo := by
  grind [clip_mem_Icc (x := x) (hlo.trans hhi)]

/-- Clipping fixes any target in the clipping interval. -/
theorem clip_target :
    clip lo hi V = V := by
  simp_all [clip]

/-- Clipping cannot increase the absolute error at an admissible target. -/
theorem clip_error_le :
    |clip lo hi x - V| ≤ |x - V| := by
  grind [clip]

end

/-- The stabilized and clipped pair-ratio inequality (eq. U14-stab).
`ED` represents the expected denominator. -/
theorem stabilized_ratio_error {lo hi V N D ED a : ℝ}
    (ha : 0 < a) (hlo : lo ≤ V) (hhi : V ≤ hi)
    (hV : 0 ≤ V) (hED : 2 * a ≤ ED) :
    |clip lo hi (N / max D a) - V| ≤
      a⁻¹ * (|N - V * D| + hi * |D - ED|) := by
  have hmax  := ha.trans_le (le_max_right D a)
  have href : a ≤ ED := by linarith
  have hhineg  := hV.trans hhi
  have hf := (by grind : |max D a - D| ≤ |D - ED|)
  have hnum : |N - V * max D a| ≤ |N - V * D| + hi * |D - ED| := by
    calc
      _ = |(N - V * D) - V * (max D a - D)| := by ring
      _ ≤ _ := abs_sub _ _
      _ = |N - V * D| + V * |max D a - D| := by simp_all
      _ ≤ _ := by
        gcongr
  have hmain : |N / max D a - V| ≤
      a⁻¹ * (|N - V * D| + hi * |D - ED|) := by
    have hid : N / max D a - V = (N - V * max D a) / max D a := by
      field_simp
    rw [hid, abs_div, abs_of_pos hmax]
    calc
      _ ≤
          _ := div_le_div_of_nonneg_right hnum hmax.le
      _ ≤ (|N - V * D| + hi * |D - ED|) / a :=
        by bound
      _ = _ := by ring
  exact (clip_error_le hlo hhi).trans hmain

section
variable {m m' scoreNorm : ℝ → ℝ} {δ r V₀ Vδ : ℝ} (hδ : 0 ≤ δ)
    (hderiv : ∀ t ∈ Icc 0 δ, HasDerivAt m (m' t) t) (hm' : IntervalIntegrable m' volume 0 δ)
    (hscore : IntervalIntegrable scoreNorm volume 0 δ) (hbound : ∀ t ∈ Icc 0 δ, |m' t| ≤ r * scoreNorm t)
include hδ hderiv hm' hscore hbound

/-- The actual analytic integration step: a derivative bounded by
`r * scoreNorm` bounds the endpoint change by the integrated score norm. -/
theorem path_mean_change_le :
    |m δ - m 0| ≤ r * ∫ t in 0..δ, scoreNorm t := by
  rw [← (intervalIntegral.integral_eq_sub_of_hasDerivAt (by simpa [uIcc_of_le hδ] using hderiv) hm'), ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.norm_integral_le_of_norm_le (f := m') hδ
    (Filter.Eventually.of_forall (fun t ht => hbound t ⟨le_of_lt ht.1, ht.2⟩))
    (hscore.const_mul r)

/-- Two endpoint errors and the integrated derivative bound imply the
linear score-to-risk bound of Lemma path-risk. -/
theorem path_separation_le
    (hfirst : |m 0 - V₀| ≤ r) (hlast : |m δ - Vδ| ≤ r) :
    |Vδ - V₀| ≤ (2 + ∫ t in 0..δ, scoreNorm t) * r := by
  grind [path_mean_change_le hδ hderiv hm' hscore hbound]

end

/-- Squaring the comparison and subtracting the exceptional-state
contribution yields the risk lower bound in eq. path-risk. -/
theorem path_risk_lower_bound {Δ B r risk D ε : ℝ}
    (hB : 0 ≤ B) (hr : 0 ≤ r) (hΔ : 0 ≤ Δ)
    (hsep : Δ ≤ (2 + B) * r)
    (hrisk : r ^ 2 = risk + D ^ 2 * ε) :
    Δ ^ 2 / (2 + B) ^ 2 - D ^ 2 * ε ≤ risk := by
  have hden : 0 < 2 + B := by linarith
  have hsq : Δ ^ 2 ≤ ((2 + B) * r) ^ 2 := by
    bound
  have hdiv : Δ ^ 2 / (2 + B) ^ 2 ≤ r ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hden)).mpr
    nlinarith [hsq]
  linarith

/-- Integral Cauchy–Schwarz on an arbitrary measure space, stated with
ordinary real second moments. -/
theorem integral_cauchy_schwarz {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤
      Real.sqrt (∫ x, (f x) ^ 2 ∂μ) * Real.sqrt (∫ x, (g x) ^ 2 ∂μ) := by
  have hholder : Real.HolderConjugate 2 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hcs := integral_mul_norm_le_Lp_mul_Lq hholder
    (by simpa using hf) (by simpa using hg)
  calc
    _ ≤ _ := norm_integral_le_integral_norm (fun x => f x * g x)
    _ = ∫ x, |f x| * |g x| ∂μ := by simp
    _ ≤ _ := by
      simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] using hcs

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ] {T R : α → ℝ} {V r : ℝ}
    (hT : MemLp T 2 μ)
include hT

/-- Mean-square risk controls bias for arbitrary probability laws. -/
theorem probability_mean_error_le (hr : 0 ≤ r)
    (hrisk : (∫ x, (T x - V) ^ 2 ∂μ) ≤ r ^ 2) :
    |(∫ x, T x ∂μ) - V| ≤ r := by
  have hcs := integral_cauchy_schwarz (f := (fun x => T x - V)) (hT.sub (memLp_const V)) (memLp_const 1)
  simp at hcs
  rw [integral_sub (hT.integrable (by norm_num)) (integrable_const V)] at hcs
  simp at hcs
  exact hcs.trans (Real.sqrt_le_iff.mpr ⟨hr, hrisk⟩)

/-- Centering and integral Cauchy–Schwarz prove the score derivative
bound on arbitrary probability spaces. -/
theorem probability_score_bound (hR : MemLp R 2 μ) (hr : 0 ≤ r)
    (hcenter : (∫ x, R x ∂μ) = 0)
    (hrisk : (∫ x, (T x - V) ^ 2 ∂μ) ≤ r ^ 2) :
    |∫ x, T x * R x ∂μ| ≤ r * Real.sqrt (∫ x, (R x) ^ 2 ∂μ) := by
  have hTRInt : Integrable (fun x => T x * R x) μ := hT.integrable_mul hR
  have hVRInt  :=
    (hR.const_mul V).integrable (by norm_num)
  have hid : (∫ x, (T x - V) * R x ∂μ) = ∫ x, T x * R x ∂μ := by
    simp_rw [sub_mul]
    rw [integral_sub hTRInt hVRInt, integral_const_mul, hcenter, mul_zero, sub_zero]
  have hcs := integral_cauchy_schwarz (f := (fun x => T x - V))
    (hT.sub (memLp_const V)) hR
  rw [hid] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_right
    (Real.sqrt_le_iff.mpr ⟨hr, hrisk⟩) (Real.sqrt_nonneg _))

end NearlyMinimax
