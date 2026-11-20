/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.NormalizerEndpoint
public import BergmanWeakType.WeakType

/-! # Admissible annular inputs for positive weighted sharpness -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology

namespace BergmanWeakType

private theorem radialMass_normalizer_le_weakBound {α R : ℝ} (hα : -1 < α)
    (hr : R ∈ radii) : ENNReal.ofReal ((1-R^2)^(α+1) * normalizer α R) ≤
      weakTypeConstant (weightedArea α) (weightedPositiveProjection α) := by
  let B  := {z | R ≤ ‖z‖} ∩ disk
  have mB : MeasurableSet B := (isClosed_le continuous_const continuous_norm).measurableSet.inter measurableSet_disk
  let := radialLaw_prob hα
  have mass : ENNReal.ofReal (exteriorMass α R) ≤ weightedArea α B := by
    rw [← radialLaw_tail hα hr, weightedArea_map hα, Measure.map_apply measurable_sample mB]
    calc
      _ = polarLaw α (Ioo R 1 ×ˢ univ) := by simp [polarLaw]
      _ ≤ _ := measure_mono fun p hp ↦ by have h := hp.1; simp [B,sample,abs_of_nonneg (hr.1.trans h.1.le), h.1.le,h.2]
  have hj := normalizer_pos α hr
  rw [mul_comm, ENNReal.ofReal_mul hj.le]; apply (mul_le_mul_right mass _).trans
  apply test_source hα (fun z w ↦ ‖weightedKernel α z w‖) (kernel_continuous α).norm (by unfold weightedKernel; fun_prop) _ Weighted.boundarySource
    mB inter_subset_right hj
  · intro z hz
    rw [Weighted.boundary_integral, Real.norm_of_nonneg (normalizer_nonneg ..)]
    exact normalizer_mono _ hr ⟨norm_nonneg _, (mem_disk_iff _).mp hz.2⟩ hz.1
  · intro f z
    simpa only [weightedPositiveProjection, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, smul_eq_mul, abs_mul, abs_of_nonneg (norm_nonneg _), ENNReal.ofReal_mul (abs_nonneg _), mul_comm] using
      (enorm_integral_le_lintegral_enorm  (fun w ↦ f w • ‖weightedKernel α z w‖))

/-- Admissible outer-annulus inputs recover the exact positive weighted lower constant. -/
theorem gammaConstant_le_weightedPositiveProjection_constant (α : ℝ) (hα : -1 < α) :
    ENNReal.ofReal (gammaConstant α) ≤
      weakTypeConstant (weightedArea α) (weightedPositiveProjection α) := by
  apply le_of_tendsto (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_radialMass_mul_normalizer hα))
  filter_upwards [Ioo_mem_nhdsLT (zero_lt_one)] with R hR
  exact radialMass_normalizer_le_weakBound hα ⟨hR.1.le,hR.2⟩

end BergmanWeakType
