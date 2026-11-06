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


variable {lo hi x V r : ℝ}
/-- Projection of a real-valued statistic to an interval. -/
def clip (lo hi x : ℝ) : ℝ := max lo (min hi x)

/-- Projection to the interval is `1`-Lipschitz. -/
theorem clip_lipschitz (lo hi ) : LipschitzWith 1 (clip lo hi) := by
  change LipschitzWith 1 (fun x => max lo (min hi x))
  simpa only [id_eq] using ((LipschitzWith.id.const_min hi).const_max lo)

/-- The clipped statistic lies in the designated interval. -/
theorem clip_mem_Icc  (hinterval : lo ≤ hi) :
    clip lo hi x ∈ Icc lo hi := ⟨le_max_left _ _, max_le hinterval (min_le_left _ _)⟩

/-- Any clipped statistic and interval-valued target are separated by
at most the diameter of the interval. -/
theorem clip_error_le_diameter  (hlo : lo ≤ V) (hhi : V ≤ hi) :
    |clip lo hi x - V| ≤ hi - lo := by
  have hc := clip_mem_Icc (x := x) (hlo.trans hhi)
  apply abs_le.mpr
  constructor <;> linarith [hc.1, hc.2]

/-- Clipping fixes any target in the clipping interval. -/
theorem clip_target  (hlo : lo ≤ V) (hhi : V ≤ hi) :
    clip lo hi V = V := by
  simp [clip, min_eq_right hhi, max_eq_right hlo]

/-- Clipping cannot increase the absolute error at an admissible target. -/
theorem clip_error_le  (hlo : lo ≤ V) (hhi : V ≤ hi) :
    |clip lo hi x - V| ≤ |x - V| := by
  by_cases hxlo : x ≤ lo
  · have hxhi  := hxlo.trans (hlo.trans hhi)
    rw [clip, min_eq_right hxhi, max_eq_left hxlo,
      abs_of_nonpos (sub_nonpos.mpr hlo), abs_of_nonpos (sub_nonpos.mpr (hxlo.trans hlo))]
    linarith
  · have hlox  := le_of_lt (lt_of_not_ge hxlo)
    by_cases hxhi : x ≤ hi
    · simp [clip, min_eq_right hxhi, max_eq_right hlox]
    · have hhix  := le_of_lt (lt_of_not_ge hxhi)
      rw [clip, min_eq_left hhix, max_eq_right (hlo.trans hhi),
        abs_of_nonneg (sub_nonneg.mpr hhi),
        abs_of_nonneg (sub_nonneg.mpr (hhi.trans hhix))]
      linarith

/-- Two endpoint errors and the integrated derivative bound imply the
linear score-to-risk bound of Lemma path-risk. -/
theorem path_separation_le {m m' scoreNorm : ℝ → ℝ} {δ r V₀ Vδ : ℝ}
    (hδ : 0 ≤ δ)
    (hderiv : ∀ t ∈ Icc 0 δ, HasDerivAt m (m' t) t)
    (hm' : IntervalIntegrable m' volume 0 δ)
    (hscore : IntervalIntegrable scoreNorm volume 0 δ)
    (hbound : ∀ t ∈ Icc 0 δ, |m' t| ≤ r * scoreNorm t)
    (hfirst : |m 0 - V₀| ≤ r) (hlast : |m δ - Vδ| ≤ r) :
    |Vδ - V₀| ≤ (2 + ∫ t in 0..δ, scoreNorm t) * r := by
  have h_path_mean_change_le : |m δ - m 0| ≤ r * ∫ t in 0..δ, scoreNorm t := by
    have hFTC  :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (by simpa [uIcc_of_le hδ] using hderiv) hm'
    rw [← hFTC, ← intervalIntegral.integral_const_mul]
    simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_of_norm_le (f := m') hδ
      (Filter.Eventually.of_forall (fun t ht => by
        simpa [Real.norm_eq_abs] using hbound t ⟨le_of_lt ht.1, ht.2⟩))
      (hscore.const_mul r)
  calc
    |Vδ - V₀| = |(Vδ - m δ) + (m δ - m 0) + (m 0 - V₀)| := by congr 1; ring
    _ ≤ |Vδ - m δ| + |m δ - m 0| + |m 0 - V₀| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ r + (r * ∫ t in 0..δ, scoreNorm t) + r := by
      rw [abs_sub_comm Vδ (m δ)]
      exact add_le_add (add_le_add hlast (h_path_mean_change_le)) hfirst
    _ = _ := by ring

/-- Integral Cauchy–Schwarz on an arbitrary measure space, stated with
ordinary real second moments. -/
theorem integral_cauchy_schwarz  [MeasurableSpace α]
    (μ : Measure α) (f g : α → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤
      Real.sqrt (∫ x, (f x) ^ 2 ∂μ) * Real.sqrt (∫ x, (g x) ^ 2 ∂μ) := by
  have hholder : Real.HolderConjugate 2 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hcs := integral_mul_norm_le_Lp_mul_Lq hholder
    (by simpa using hf) (by simpa using hg)
  have hcs' : (∫ x, |f x| * |g x| ∂μ) ≤
      Real.sqrt (∫ x, (f x) ^ 2 ∂μ) * Real.sqrt (∫ x, (g x) ^ 2 ∂μ) := by
    simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] using hcs
  calc
    |∫ x, f x * g x ∂μ| ≤ ∫ x, |f x * g x| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => f x * g x)
    _ = ∫ x, |f x| * |g x| ∂μ := by simp_rw [abs_mul]
    _ ≤ _ := hcs'

/-- Mean-square risk controls bias for arbitrary probability laws. -/
theorem probability_mean_error_le  [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (T : α → ℝ) (V r : ℝ)
    (hT : MemLp T 2 μ) (hr : 0 ≤ r)
    (hrisk : (∫ x, (T x - V) ^ 2 ∂μ) ≤ r ^ 2) :
    |(∫ x, T x ∂μ) - V| ≤ r := by
  have hcs := integral_cauchy_schwarz μ (fun x => T x - V) (fun _ => 1) (hT.sub (memLp_const V)) (memLp_const 1)
  simp only [mul_one, one_pow] at hcs
  rw [integral_sub (hT.integrable (by norm_num)) (integrable_const V)] at hcs
  simp only [integral_const, probReal_univ, one_smul, Real.sqrt_one, mul_one] at hcs
  exact hcs.trans ((Real.sqrt_le_iff).mpr ⟨hr, hrisk⟩)

/-- Centering and integral Cauchy–Schwarz prove the score derivative
bound on arbitrary probability spaces. -/
theorem probability_score_bound  [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (T R : α → ℝ) (V r : ℝ)
    (hT : MemLp T 2 μ) (hR : MemLp R 2 μ) (hr : 0 ≤ r)
    (hcenter : (∫ x, R x ∂μ) = 0)
    (hrisk : (∫ x, (T x - V) ^ 2 ∂μ) ≤ r ^ 2) :
    |∫ x, T x * R x ∂μ| ≤ r * Real.sqrt (∫ x, (R x) ^ 2 ∂μ) := by
  have hTRInt : Integrable (fun x => T x * R x) μ := hT.integrable_mul hR
  have hVRInt : Integrable (fun x => V * R x) μ :=
    (hR.const_mul V).integrable (by norm_num)
  have hid : (∫ x, (T x - V) * R x ∂μ) = ∫ x, T x * R x ∂μ := by
    simp_rw [sub_mul]
    rw [integral_sub hTRInt hVRInt, integral_const_mul, hcenter, mul_zero, sub_zero]
  have hcs := integral_cauchy_schwarz μ (fun x => T x - V) R
    (hT.sub (memLp_const V)) hR
  rw [hid] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_right
    ((Real.sqrt_le_iff).mpr ⟨hr, hrisk⟩) (Real.sqrt_nonneg _))

/-- Squaring the comparison and subtracting the exceptional-state
contribution yields the risk lower bound in eq. path-risk. -/
theorem path_risk_lower_bound {Δ B r risk D ε : ℝ}
    (hB : 0 ≤ B) (hr : 0 ≤ r) (hΔ : 0 ≤ Δ)
    (hsep : Δ ≤ (2 + B) * r)
    (hrisk : r ^ 2 = risk + D ^ 2 * ε) :
    Δ ^ 2 / (2 + B) ^ 2 - D ^ 2 * ε ≤ risk := by
  have hden : 0 < 2 + B := by linarith
  have : Δ ^ 2 / (2 + B) ^ 2 ≤ r ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hden)).mpr
    nlinarith [(by have hprod  := mul_nonneg hden.le hr; exact (sq_le_sq₀ hΔ hprod).mpr hsep)]
  linarith


end NearlyMinimax
