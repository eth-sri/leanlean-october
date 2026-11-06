module
public import WeylPort.Analytic.RealLaplace
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

-- Lean 4.34 elaborator compatibility; kernel checking stays enabled.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Complex Gamma--Laplace integral for the DFI Neumann kernel

The oscillatory part of Schläfli's representation is handled by Abel
regularization.  This module proves the complex-damping Gamma integral on
the full right half-plane.  The proof differentiates under the integral and
uses analytic continuation from positive real damping parameters.
-/

open Complex Set MeasureTheory Filter
open scoped Topology

namespace RiemannZeta.GuthMaynard

theorem integrableOn_cpow_mul_cexp_neg_complex_mul_Ioi
    {s a : ℂ} (hs : 0 < s.re) (ha : 0 < a.re) :
    IntegrableOn (fun x : ℝ =>
      (x : ℂ) ^ (s - 1) * cexp (-(a * x))) (Set.Ioi 0) := by
  have hbase := integrableOn_cpow_mul_exp_neg_mul_Ioi hs ha
  refine hbase.norm.mono' ?_ ?_
  fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    pm_8299
    pm_316 neg_re mul_re ofReal_re ofReal_im mul_zero sub_zero
    exact le_rfl

/-- The `dfiComplexLaplace` definition used by the source-facing construction in `DFIComplexLaplace`. -/
noncomputable def dfiComplexLaplace (s a : ℂ) : ℂ :=
  ∫ x : ℝ in Set.Ioi 0, (x : ℂ) ^ (s - 1) * cexp (-(a * x))

theorem hasDerivAt_dfiComplexLaplace
    {s a : ℂ} (hs : 0 < s.re) (ha : 0 < a.re) :
    HasDerivAt (dfiComplexLaplace s)
      (∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) * (-x) * cexp (-(a * x))) a := by
  pm_51
  have hFInt : Integrable (F a) (volume.restrict (Set.Ioi 0)) := by
    exact integrableOn_cpow_mul_cexp_neg_complex_mul_Ioi hs ha
  pm_50
  have hDiff : ∀ᵐ x ∂(volume.restrict (Set.Ioi 0)),
      ∀ b ∈ Metric.ball a r, HasDerivAt (F · x) (F' b x) b := by
    filter_upwards with x
    intro b _
    dsimp [F, F']
    convert (Complex.hasDerivAt_exp (-(b * x))).comp b
      (((hasDerivAt_id b).mul_const (x : ℂ)).neg) |>.const_mul
        ((x : ℂ) ^ (s - 1)) using 1
    · funext z; dsimp
    · ring
  pm_52
  exact h.2

section
variable {s : ℂ} (hs : 0 < s.re)
include s hs
theorem analyticOnNhd_dfiComplexLaplace :
    AnalyticOnNhd ℂ (dfiComplexLaplace s) {a : ℂ | 0 < a.re} := by
  have hopen : IsOpen {a : ℂ | 0 < a.re} :=
    isOpen_lt continuous_const continuous_re
  apply (show DifferentiableOn ℂ (dfiComplexLaplace s) {a : ℂ | 0 < a.re} by
    intro a ha
    exact (hasDerivAt_dfiComplexLaplace hs ha).differentiableAt.differentiableWithinAt
    ).analyticOnNhd hopen

theorem dfiComplexLaplace_ofReal {r : ℝ} (hr : 0 < r) :
    dfiComplexLaplace s (r : ℂ) = (r : ℂ) ^ (-s) * Gamma s := by
  have h := integral_cpow_mul_exp_neg_mul_Ioi_eq hs hr
  unfold dfiComplexLaplace
  rw [show (∫ x : ℝ in Set.Ioi 0,
      (x : ℂ) ^ (s - 1) * cexp (-((r : ℂ) * x))) =
      ∫ x : ℝ in Set.Ioi 0,
        (x : ℂ) ^ (s - 1) * cexp (-(r * x)) by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    push_cast
    rfl]
  rw [h]
  congr 1
  rw [one_div, Complex.inv_cpow]
  · rw [Complex.cpow_neg]
  · rw [Complex.arg_ofReal_of_nonneg hr.le]
    exact Real.pi_ne_zero.symm
end

theorem dfiComplexLaplace_eq
    {s a : ℂ} (hs : 0 < s.re) (ha : 0 < a.re) :
    dfiComplexLaplace s a = a ^ (-s) * Gamma s := by
  pm_54
  have hGDiff : DifferentiableOn ℂ G U := by
    intro b hb
    have hbpos : 0 < b.re := hb
    pm_771
  pm_53
  have hFreq : ∃ᶠ b : ℂ in 𝓝[≠] (1 : ℂ), F b = G b := by
    pm_55
    · rw [tendsto_nhdsWithin_iff] at hxs ⊢
      constructor
      · simpa only [Function.comp_def, Complex.ofReal_one] using Complex.continuous_ofReal.continuousAt.tendsto.comp hxs.1
      · simpa using hxs.2
    pm_8303
  pm_56

end RiemannZeta.GuthMaynard
