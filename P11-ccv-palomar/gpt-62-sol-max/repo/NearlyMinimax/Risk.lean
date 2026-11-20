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
theorem clip_lipschitz (lo hi : ℝ) : LipschitzWith 1 (clip lo hi) := by
  change LipschitzWith 1 (fun x => max lo (min hi x))
  simpa only [id_eq] using ((LipschitzWith.id.const_min hi).const_max lo)

/-- The clipped statistic lies in the designated interval. -/
theorem clip_mem_Icc {lo hi x : ℝ} (hinterval : lo ≤ hi) :
    clip lo hi x ∈ Icc lo hi := ⟨le_max_left _ _, max_le hinterval (min_le_left _ _)⟩

/-- Any clipped statistic and interval-valued target are separated by
at most the diameter of the interval. -/
theorem clip_error_le_diameter {lo hi V x : ℝ} (hlo : lo ≤ V) (hhi : V ≤ hi) :
    |clip lo hi x - V| ≤ hi - lo := by
  have hc := clip_mem_Icc (x := x) (hlo.trans hhi)
  grind

/-- Clipping fixes any target in the clipping interval. -/
theorem clip_target {lo hi V : ℝ} (hlo : lo ≤ V) (hhi : V ≤ hi) :
    clip lo hi V = V := by
  simp [clip, min_eq_right hhi, max_eq_right hlo]

/-- Clipping cannot increase the absolute error at an admissible target. -/
theorem clip_error_le {lo hi V x : ℝ} (hlo : lo ≤ V) (hhi : V ≤ hi) :
    |clip lo hi x - V| ≤ |x - V| := by
  grind [clip.eq_1]

/-- A denominator floored at `a` can move only as much as its discrepancy
from a reference mean greater than `a`. -/
theorem denominator_floor_error {a D ED : ℝ} (hED : a ≤ ED) :
    |max D a - D| ≤ |D - ED| := by
  grind

/-- The stabilized and clipped pair-ratio inequality (eq. U14-stab).
`ED` represents the expected denominator. -/
theorem stabilized_ratio_error {lo hi V N D ED a : ℝ}
    (ha : 0 < a) (hlo : lo ≤ V) (hhi : V ≤ hi)
    (hV : 0 ≤ V) (hED : 2 * a ≤ ED) :
    |clip lo hi (N / max D a) - V| ≤
      a⁻¹ * (|N - V * D| + hi * |D - ED|) := by
  have hmax := ha.trans_le (le_max_right D a)
  have href : a ≤ ED := by linarith
  have hhineg := hV.trans hhi
  have hf := denominator_floor_error (D := D) href
  have hnum : |N - V * max D a| ≤ |N - V * D| + hi * |D - ED| := by
    calc
      |N - V * max D a| = |(N - V * D) - V * (max D a - D)| := by ring
      _ ≤ |N - V * D| + |V * (max D a - D)| := abs_sub _ _
      _ = |N - V * D| + V * |max D a - D| := by rw [abs_mul, abs_of_nonneg hV]
      _ ≤ |N - V * D| + hi * |D - ED| := by
        gcongr
  have hmain : |N / max D a - V| ≤
      a⁻¹ * (|N - V * D| + hi * |D - ED|) := by
    have hid : N / max D a - V = (N - V * max D a) / max D a := by
      field_simp
    rw [hid, abs_div, abs_of_pos hmax]
    have htotal : 0 ≤ |N - V * D| + hi * |D - ED| := by positivity
    calc
      |N - V * max D a| / max D a ≤
          (|N - V * D| + hi * |D - ED|) / max D a := by
        gcongr
      _ ≤ (|N - V * D| + hi * |D - ED|) / a :=
        div_le_div_of_nonneg_left htotal ha (le_max_right D a)
      _ = _ := by ring
  exact (clip_error_le hlo hhi).trans hmain

/-- Two bounds on endpoint bias and a bound on movement of the mean give separation. -/
theorem endpoint_separation_le {V₀ Vδ m₀ mδ r B : ℝ}
    (hfirst : |m₀ - V₀| ≤ r) (hlast : |mδ - Vδ| ≤ r) (hmove : |mδ - m₀| ≤ B) :
    |Vδ - V₀| ≤ 2 * r + B := by
  rw [abs_sub_comm] at hlast
  linarith only [abs_sub_le Vδ mδ V₀, abs_sub_le mδ m₀ V₀, hfirst, hlast, hmove]

/-- Squaring the comparison and subtracting the exceptional-state
contribution yields the risk lower bound in eq. path-risk. -/
theorem path_risk_lower_bound {Δ B r risk D ε : ℝ}
    (hB : 0 ≤ B) (hΔ : 0 ≤ Δ)
    (hsep : Δ ≤ (2 + B) * r)
    (hrisk : r ^ 2 = risk + D ^ 2 * ε) :
    Δ ^ 2 / (2 + B) ^ 2 - D ^ 2 * ε ≤ risk := by
  have hden : 0 < 2 + B := by linarith
  have hsq : Δ ^ 2 ≤ ((2 + B) * r) ^ 2 := by
    gcongr
  have hdiv : Δ ^ 2 / (2 + B) ^ 2 ≤ r ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hden)).mpr
    linarith
  linarith

section
variable {α : Type*} [MeasurableSpace α]
    (μ : Measure α)

/-- Integral Cauchy–Schwarz on an arbitrary measure space, stated with
ordinary real second moments. -/
theorem integral_cauchy_schwarz (f g : α → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤
      Real.sqrt (∫ x, (f x) ^ 2 ∂μ) * Real.sqrt (∫ x, (g x) ^ 2 ∂μ) := by
  have hholder : Real.HolderConjugate 2 2 := by
    norm_num [Real.holderConjugate_iff]
  have hcs := integral_mul_norm_le_Lp_mul_Lq hholder
    (by simpa using hf) (by simpa using hg)
  have hcs' : (∫ x, |f x| * |g x| ∂μ) ≤
      Real.sqrt (∫ x, (f x) ^ 2 ∂μ) * Real.sqrt (∫ x, (g x) ^ 2 ∂μ) := by
    simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] using hcs
  calc
    |∫ x, f x * g x ∂μ| ≤ ∫ x, |f x * g x| ∂μ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => f x * g x)
    _ = ∫ x, |f x| * |g x| ∂μ := by simp
    _ ≤ _ := hcs'

/-- Mean-square risk controls bias for arbitrary probability laws. -/
theorem probability_mean_error_le [IsProbabilityMeasure μ] (T : α → ℝ) (V r : ℝ)
    (hT : MemLp T 2 μ) (hr : 0 ≤ r)
    (hrisk : (∫ x, (T x - V) ^ 2 ∂μ) ≤ r ^ 2) :
    |(∫ x, T x ∂μ) - V| ≤ r := by
  have hcenter := hT.sub (memLp_const V)
  have hcs := integral_cauchy_schwarz μ (fun x => T x - V) (fun _ => 1) hcenter (memLp_const 1)
  have hTInt := hT.integrable (by norm_num)
  have hVInt : Integrable (fun _ : α => V) μ := integrable_const V
  simp only [mul_one, one_pow] at hcs
  rw [integral_sub hTInt hVInt] at hcs
  simp only [integral_const, probReal_univ, one_smul, Real.sqrt_one, mul_one] at hcs
  exact hcs.trans ((Real.sqrt_le_iff).mpr ⟨hr, hrisk⟩)

/-- Centering and integral Cauchy–Schwarz prove the score derivative
bound on arbitrary probability spaces. -/
theorem probability_score_bound [IsProbabilityMeasure μ] (T R : α → ℝ) (V r : ℝ)
    (hT : MemLp T 2 μ) (hR : MemLp R 2 μ) (hr : 0 ≤ r)
    (hcenter : (∫ x, R x ∂μ) = 0)
    (hrisk : (∫ x, (T x - V) ^ 2 ∂μ) ≤ r ^ 2) :
    |∫ x, T x * R x ∂μ| ≤ r * Real.sqrt (∫ x, (R x) ^ 2 ∂μ) := by
  have hTRInt : Integrable (fun x => T x * R x) μ := hT.integrable_mul hR
  have hVRInt : Integrable (fun x => V * R x) μ :=
    (hR.const_mul V).integrable (by norm_num)
  have hid : (∫ x, (T x - V) * R x ∂μ) = ∫ x, T x * R x ∂μ := by
    simp [sub_mul, integral_sub hTRInt hVRInt, integral_const_mul, hcenter, mul_zero, sub_zero]
  have hcs := integral_cauchy_schwarz μ (fun x => T x - V) R
    (hT.sub (memLp_const V)) hR
  simpa [hid] using hcs.trans (mul_le_mul_of_nonneg_right
      ((Real.sqrt_le_iff).mpr ⟨hr, hrisk⟩) (Real.sqrt_nonneg _))

end

end NearlyMinimax
