module
/-
Selected exponential-critical-moment convergence proofs adapted from Scott
McColm, PointMeanOffCritical.lean, exact revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0,
Copyright 2026 S. McColm. See third_party/twelfth/POINT_MEAN_NATIVE_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0.
The critical norm is the repository's literal actual-zeta norm.
-/
public import MathCollab.Density.Stronger.PointMean.MellinVertical
public import MathCollab.Density.Stronger.CriticalMoment
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Set MeasureTheory
open MathCollab.Density.ZetaGrowth
noncomputable section
namespace MathCollab.Density.Stronger.PointMean

/-- The untruncated exponential convolution occurring after the source choice
`delta = (log t)⁻¹`. -/
noncomputable def heathBrownFullCriticalMoment (t : ℝ) : ℝ :=
  ∫ u : ℝ, Real.exp (-|u|) *
    zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)

private theorem heathBrownMellinCriticalMoment_integrand_nonneg
    {delta t u : ℝ} (hdelta : 0 < delta) :
    0 ≤ Real.exp (-|u|) / (delta + |u|) *
      zetaMomentCriticalNorm (t + u) ^ (2 : ℕ) := by
  positivity

/-- Absolute convergence of the exact weighted critical-line moment. -/
theorem integrable_heathBrownMellinCriticalMoment
    {delta t : ℝ} (hdelta : 0 < delta) :
    Integrable (fun u : ℝ => Real.exp (-|u|) / (delta + |u|) *
      zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)) := by
  let f : ℝ → ℝ := fun u => Real.exp (-|u|) / (delta + |u|) *
    zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)
  pm_8399
  let M : ℝ := 100 / delta
  pm_5586 u
  have hBpos : 0 < B := by
    dsimp only [B]
    grind
  pm_82 hMnonneg M
  have hCont : Continuous f := by
    apply Continuous.mul
    · apply Continuous.div
      · fun_prop
      · fun_prop
      grind
    pm_5038
  have hg : Integrable g :=
    integrable_abs_sq_mul_exp_neg_abs.const_mul M
  have hTail : ∀ u : ℝ, B < |u| → ‖f u‖ ≤ g u := by
    intro u hu
    have hheight : 1 ≤ |t + u| := by
      pm_5400 u t
      rw [add_comm] at htri
      linarith
    pm_4447
    have hzeta := norm_riemannZeta_le_five_mul_norm hzRe
      (by aesop)
    pm_4445
    have hdenom : delta ≤ delta + |u| := by linarith [abs_nonneg u]
    have hrecip : 1 / (delta + |u|) ≤ 1 / delta := by
      exact one_div_le_one_div_of_le hdelta hdenom
    pm_4446
    have hfNonneg : 0 ≤ f u := by
      dsimp only [f]
      exact heathBrownMellinCriticalMoment_integrand_nonneg hdelta
    rw [Real.norm_eq_abs, abs_of_nonneg hfNonneg]
    dsimp only [f, g, M]
    have hexp : 0 ≤ Real.exp (-|u|) := (Real.exp_pos _).le
    calc
      Real.exp (-|u|) / (delta + |u|) *
          zetaMomentCriticalNorm (t + u) ^ (2 : ℕ) ≤
        (Real.exp (-|u|) / delta) * (100 * |u| ^ 2) := by
          gcongr
      _ = 100 / delta * (|u| ^ 2 * Real.exp (-|u|)) := by ring
  pm_4444
  grind

/-- Absolute convergence of Heath--Brown's full exponential convolution. -/
theorem integrable_heathBrownFullCriticalMoment (t : ℝ) :
    Integrable (fun u : ℝ => Real.exp (-|u|) *
      zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)) := by
  let f : ℝ → ℝ := fun u => Real.exp (-|u|) *
    zetaMomentCriticalNorm (t + u) ^ (2 : ℕ)
  pm_8399
  let g : ℝ → ℝ := fun u => 100 * (|u| ^ 2 * Real.exp (-|u|))
  have hBpos : 0 < B := by
    dsimp only [B]
    linarith [abs_nonneg t]
  have hCont : Continuous f := by
    exact (by fun_prop : Continuous (fun u : ℝ => Real.exp (-|u|))).mul
      ((continuous_zetaMomentCriticalNorm.pow 2).comp (by fun_prop))
  have hg : Integrable g :=
    integrable_abs_sq_mul_exp_neg_abs.const_mul 100
  have hTail : ∀ u : ℝ, B < |u| → ‖f u‖ ≤ g u := by
    intro u hu
    have hheight : 1 ≤ |t + u| := by
      have htri := abs_sub_abs_le_abs_sub u (-t)
      rw [abs_neg, sub_neg_eq_add, add_comm] at htri
      linarith
    pm_4447
    pm_8294 hheight
    pm_4445
    pm_4446
    have hfNonneg : 0 ≤ f u := by dsimp only [f]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hfNonneg]
    dsimp only [f, g]
    calc
      Real.exp (-|u|) * zetaMomentCriticalNorm (t + u) ^ (2 : ℕ) ≤
          Real.exp (-|u|) * (100 * |u| ^ 2) := by gcongr
      _ = 100 * (|u| ^ 2 * Real.exp (-|u|)) := by ring
  pm_4444
  rwa [hAllSet] at hAll

theorem heathBrownFullCriticalMoment_nonneg (t : ℝ) :
    0 ≤ heathBrownFullCriticalMoment t := by
  unfold heathBrownFullCriticalMoment
  exact integral_nonneg fun u => by positivity

end MathCollab.Density.Stronger.PointMean
