/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.TransferredCompactTest
public import DOZZ.GMC.Assembly.CircleIntensity
public import DOZZ.GMC.Annulus.PositiveRoot

/-! Identify the unpinned translated cutoff with a deterministic test of the actual cutoff GMC. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs
section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
section
variable (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
include hX hc

/-- The actual cutoff GMC integral, expressed against planar volume. -/
theorem regularized_integral_volume
    (γ r : ℝ) (ω : Ω) (f : ℂ → ℝ) :
    (∫ x, f x ∂regularizedGMC P Xc γ r ω) =
      ∫ x, f x * Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P) *
        normPlus x ^ (-4 : ℝ) ∂volume := by
  let : IsProbabilityMeasure P := hX.1
  have hV : Measurable (fun x => ∫ ω', Xc ω' x r ^ 2 ∂P) := by
    have h : Measurable (fun q : ℂ × Ω => Xc q.2 q.1 r ^ 2) :=
      ((hc.1 r).comp measurable_swap).pow_const 2
    exact h.stronglyMeasurable.integral_prod_right.measurable
  have hD : Measurable (fun x => ENNReal.ofReal
      (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P) *
        normPlus x ^ (-4 : ℝ))) := by
    have hC : Measurable (fun x => Xc ω x r) :=
      (hc.1 r).comp (measurable_const.prodMk measurable_id)
    have hN : Measurable (fun x => normPlus x ^ (-4 : ℝ)) := by
      unfold normPlus
      fun_prop
    fun_prop
  rw [regularizedGMC, integral_withDensity_eq_integral_toReal_smul hD
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_nonneg _)
    (Real.rpow_nonneg (by unfold normPlus; positivity) _))]
  ring

/-- On every compact subchart the cutoff pin removal is an exact scalar times an actual GMC test. -/
theorem unpinned_cutoff_test_identity
    (z : ℂ) (hz : 2 ≤ ‖z‖) (γ r ρ : ℝ) (hr : ρ + Real.exp (-r) ≤ 1)
    (f g : BoundedContinuousFunction ℂ ℝ)
    (hf : ∀ x, f x ≠ 0 → ‖x‖ ≤ ρ)
    (hg : ∀ w, g w = f (w-z) * Real.exp ((γ ^ 2 + 4) * Real.log (normPlus w)))
    (ω : Ω) :
    regularizedLogChaosTestMass P (Metric.ball 0 1) (fun x => normPlus x ^ (-4 : ℝ))
      (fun ω ε x => Xc ω (z+x) (Real.log (1/ε)) - Xc ω z 0) γ r ω f =
      Real.exp (-γ * Xc ω z 0) * ∫ w, g w ∂regularizedGMC P Xc γ r ω := by
  have hRef : logRegularizationReference (Metric.ball (0 : ℂ) 1)
      (fun x => normPlus x ^ (-4 : ℝ)) = volume.restrict (Metric.ball 0 1) := by
    rw [logRegularizationReference_restrict_of_subset univ _ _ Metric.isOpen_ball.measurableSet
      (subset_univ _)]
    simp only [logRegularizationReference, Measure.restrict_univ]
    exact gmcReferenceMeasure_restrict_unit_chart _ Metric.isOpen_ball.measurableSet
      (fun x hx => (by simp_all : ‖x‖ < 1).le)
  have hlog : Real.log (1 / Real.exp (-r)) = r := by
    simp
  rw [regularizedLogChaosTestMass, hRef, hlog,
    regularized_integral_volume P X Xc hX hc γ r ω g]
  rw [← integral_add_left_eq_self (μ := volume)
    (fun w : ℂ => g w * Real.exp _ *
      normPlus w ^ (-4 : ℝ)) z]
  rw [← integral_const_mul]
  rw [integral_restrict_eq_integral_of_zero_on_compl volume _
    Metric.isOpen_ball.measurableSet _ (by
      intro x hx
      have hf0 : f x = 0 := by
        by_contra h
        have hnorm := hf x h
        have hlt : ‖x‖ < 1 := by linarith [Real.exp_pos (-r)]
        exact hx (by simp_all)
      simp only [hf0, zero_mul])]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [hg _, add_sub_cancel_left]
  by_cases hx : f x = 0
  · simp_all
  · let p : localCircle := ⟨(x,r), by grind⟩
    obtain ⟨hO, hU⟩ := local_circle_second_moments P X Xc hX hc z hz p
    change _ = _ at hO
    change _ = r at hU
    rw [hO, hU, unpinned_density_ratio Xc z hz γ ω p]
    ring

end

end


end DOZZ.Proofs
