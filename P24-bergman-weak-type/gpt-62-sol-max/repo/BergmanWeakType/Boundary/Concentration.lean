/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.KernelIntegrability
public import BergmanWeakType.Weighted.MassCoordinate
public import BergmanWeakType.WeakType
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.MeasureTheory.Measure.Regular

/-! # Kernel column bounds via local averaging -/

public section

open MeasureTheory Metric Set
open scoped ENNReal

namespace BergmanWeakType

/-- A column at any point of the closed disk can be tested by averaging admissible
inputs on arbitrarily small neighborhoods of that point. -/
theorem column_le_weakBound {α L : ℝ} {C : ℝ≥0∞} (hα : -1 < α)
    (hC : IsWeakTypeBound (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) C)
    {a : ℂ} (ha : a ∈ closure disk) {E : Set ℂ} (hE : MeasurableSet E) (hsub : E ⊆ disk)
    (hcol : ∀ z ∈ E, L ≤ ‖weightedKernel α z a‖) (hL : 0 < L) :
    ENNReal.ofReal L * weightedArea α E ≤ C := by
  let := weightedArea_isProbabilityMeasure α hα
  let μ := weightedArea α
  have ha' : a ∈ closedBall 0 1 := closure_minimal ball_subset_closedBall isClosed_closedBall ha
  have hcompact (K : Set ℂ) (hKE : K ⊆ E) (hK : IsCompact K) : ENNReal.ofReal L * μ K ≤ C := by
    apply le_of_tendsto (ENNReal.Tendsto.mul_const
      (ENNReal.continuous_ofReal.continuousWithinAt (s := Iio L)) (Or.inl (by positivity)))
    filter_upwards [Ioo_mem_nhdsLT hL] with ℓ hℓ
    have hc : ContinuousOn (fun p : ℂ × ℂ ↦ weightedKernel α p.1 p.2) (K ×ˢ closedBall 0 1) :=
      (continuousOn_weightedKernel_prod α).mono fun p hp ↦
        mul_norm_lt_one (hsub (hKE hp.1)) (by simpa using hp.2)
    obtain ⟨r, hr, hclose⟩ := Metric.uniformContinuousOn_iff.mp
      ((hK.prod (isCompact_closedBall 0 1)).uniformContinuousOn_of_continuous hc) _ (sub_pos.mpr hℓ.2)
    let s := ball a r ∩ disk
    have hs : IsOpen s := isOpen_ball.inter isOpen_ball
    refine hC.test_indicator hs.measurableSet ?_ hℓ.1.le (.of_forall fun z hz ↦ ?_)
    · intro he
      have hd := diskArea_absolutelyContinuous_weightedArea α hα he
      rw [diskArea, Measure.restrict_eq_self _ inter_subset_right] at hd
      exact (hs.measure_pos area (mem_closure_iff_nhds.mp ha _ (ball_mem_nhds _ hr))).ne' hd
    rw [← ofReal_norm, weightedProjection]
    simp_rw [← indicator_mul_right, mul_one, integral_indicator hs.measurableSet]
    apply ENNReal.ofReal_le_ofReal
    let g := weightedKernel α z
    have hi : IntegrableOn g s μ :=
      ((memLp_weightedKernel_top (hsub (hKE hz))).integrable le_top).integrableOn
    have he := norm_setIntegral_le_of_norm_le_const (f := fun w ↦ g w - g a)
      (measure_lt_top μ s) (fun w hw ↦ by
        simpa only [g, dist_eq_norm] using (hclose (z, w) ⟨hz, ball_subset_closedBall hw.2⟩
          (z, a) ⟨hz, ha'⟩ (by simpa [Prod.dist_eq, hr] using hw.1)).le)
    rw [integral_sub hi (integrable_const _), setIntegral_const] at he
    have hg := norm_sub_norm_le (μ.real s • g a) (∫ w in s, g w ∂μ)
    rw [norm_smul, Real.norm_of_nonneg (measureReal_nonneg (μ := μ) (s := s)), norm_sub_rev] at hg
    change ℓ * μ.real s ≤ ‖∫ w in s, g w ∂μ‖
    nlinarith only [he, hg, mul_le_mul_of_nonneg_left (hcol z (hKE hz)) (measureReal_nonneg (μ := μ) (s := s))]
  rw [hE.measure_eq_iSup_isCompact, ENNReal.mul_iSup]
  simp_rw [ENNReal.mul_iSup]
  aesop

/-- The interior column at the origin is identically one. -/
theorem one_le_weightedProjection_constant (α : ℝ) (hα : -1 < α) :
    1 ≤ weakTypeConstant (weightedArea α) (fun f z ↦ ‖weightedProjection α f z‖ₑ) := by
  let := weightedArea_isProbabilityMeasure α hα
  apply le_sInf
  intro C hC
  simpa [show weightedArea α disk = 1 from by
    rw [← measure_univ (μ := weightedArea α)]
    exact measure_congr (ae_eq_univ.mpr (ae_mem_disk_weightedArea α))]
    using column_le_weakBound hα hC (a := 0) (subset_closure (by simp)) measurableSet_disk
      Subset.rfl (L := 1) (by simp) zero_lt_one

end BergmanWeakType
