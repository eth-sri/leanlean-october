/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.PolarPotential
public import BergmanWeakType.Weighted.QuotientCap
public import BergmanWeakType.Weighted.NormalizerRadial
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Weighted positive potentials and their normalized circular caps -/

@[expose] public section

noncomputable section

open MeasureTheory Set Real

namespace BergmanWeakType.Weighted

def weightedDensity (α : ℝ) (f : ℂ → ℂ) : Measure ℂ :=
  (weightedArea α).withDensity (‖f ·‖ₑ)

theorem finite_weightedDensity {α : ℝ} {f : ℂ → ℂ} (hf : Integrable f (weightedArea α)) :
    IsFiniteMeasure (weightedDensity α f) :=
  isFiniteMeasure_withDensity (hasFiniteIntegral_iff_enorm.mp hf.hasFiniteIntegral).ne

theorem ae_mem_weighted_closedDisk (α : ℝ) (f : ℂ → ℂ) :
    ∀ᵐ w ∂weightedDensity α f, w ∈ Metric.closedBall 0 1 :=
  (withDensity_absolutelyContinuous _ _).ae_le
    ((ae_mem_disk_weightedArea α).mono fun _ hw ↦ Metric.ball_subset_closedBall hw)

def weightedPotential (α : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  ∫ w, ‖weightedKernel α z w‖ ∂weightedDensity α f

def weightedDiskPotential (α : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  weightedPotential α f z / normalizer α ‖z‖

theorem weightedDiskPotential_nonneg (α : ℝ) (f : ℂ → ℂ) (z : ℂ) : 0 ≤ weightedDiskPotential α f z :=
  div_nonneg (integral_nonneg fun _ ↦ norm_nonneg _) (normalizer_nonneg α ‖z‖)

theorem weightedPotential_eq_norm_mul {α : ℝ} {f : ℂ → ℂ}
    (hf : Integrable f (weightedArea α)) (z : ℂ) : weightedPotential α f z =
      ∫ w, ‖weightedKernel α z w‖ * ‖f w‖ ∂weightedArea α := by
  simpa only [weightedPotential, weightedDensity, enorm_eq_nnnorm, NNReal.smul_def, coe_nnnorm,
    smul_eq_mul, mul_comm] using integral_withDensity_eq_integral_smul₀
      hf.aestronglyMeasurable.aemeasurable.nnnorm (fun w ↦ ‖weightedKernel α z w‖)

theorem measurable_weightedDiskPotential {α : ℝ} {f : ℂ → ℂ}
    (hf : Integrable f (weightedArea α)) : Measurable (weightedDiskPotential α f) := by
  let := finite_weightedDensity hf
  have hn : Measurable (normalizer α) := by
    change Measurable (fun r ↦ normalizer α r)
    simp_rw [normalizer, circleAverage_eq_integral_angleMeasure]
    exact (show Measurable (fun p : ℝ × ℝ ↦ ‖1 - circleMap 0 p.1 p.2‖ ^ (-(α + 2))) by
      fun_prop).stronglyMeasurable.integral_prod_right'.measurable
  have hk : Measurable (fun p : ℂ × ℂ ↦ ‖weightedKernel α p.1 p.2‖) := by
    simp_rw [norm_weightedKernel]
    fun_prop
  exact hk.stronglyMeasurable.integral_prod_right'.measurable.div (hn.comp measurable_norm)

/-- Normalizing by the exact circular kernel average makes every capped circular mean
of an admissible weighted potential decrease with radius. -/
theorem antitoneOn_angularMean_cap {α : ℝ}
    {f : ℂ → ℂ} (hf : Integrable f (weightedArea α)) (c : ℝ) :
    AntitoneOn (angularMean fun r θ ↦ min (weightedDiskPotential α f (circleMap 0 r θ)) c)
      (radii) := by
  let S : PolarSource := ⟨weightedDensity α f, ae_mem_weighted_closedDisk α f, finite_weightedDensity hf⟩
  refine (S.antitoneOn_normalized_cap α c).congr fun r hr ↦ ?_
  simp only [angularMean, weightedDiskPotential, weightedPotential, S,
    PolarSource.integral, PolarSource.eval, polarKernel_eq_norm_weightedKernel,
    norm_circleMap_zero, abs_of_nonneg hr.1]

theorem angularMean_cap_le_mass {α : ℝ}
    {f : ℂ → ℂ} (hf : Integrable f (weightedArea α)) {r : ℝ}
    (hr : r ∈ radii) (c : ℝ) :
    angularMean (fun r θ ↦ min (weightedDiskPotential α f (circleMap 0 r θ)) c) r ≤
      ∫ w, ‖f w‖ ∂weightedArea α := by
  have h := antitoneOn_angularMean_cap hf c (by simp : (0 : ℝ) ∈ radii) hr hr.1
  simp [angularMean, weightedDiskPotential, weightedPotential_eq_norm_mul hf, weightedKernel] at h ⊢
  exact h.1

end BergmanWeakType.Weighted
