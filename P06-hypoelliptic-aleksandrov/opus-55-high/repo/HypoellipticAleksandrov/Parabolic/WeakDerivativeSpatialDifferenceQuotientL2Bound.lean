module

public import HypoellipticAleksandrov.Analysis.DensePairingNorm
public import HypoellipticAleksandrov.Parabolic.ParabolicMemLpSpatialDifferenceQuotient
public import HypoellipticAleksandrov.Parabolic.TimeVelocityOpenSmoothTestL2Density
public import HypoellipticAleksandrov.Parabolic.WeakDerivativeSpatialDifferenceQuotientPairing
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Weak derivatives control signed spatial difference quotients

This module assembles the open-carrier density and smooth-test pairing results
to obtain the sharp restricted `L²` bound for signed spatial difference
quotients.
-/

@[expose] public section


namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped Convex ENNReal RealInnerProductSpace Topology

/-- A selected weak velocity derivative controls every signed nonzero
spatial difference quotient on an arbitrary inner carrier whose full directed
segments remain in the open outer carrier. -/
theorem HasWeakVelocityPartialDerivOn.exists_spatialDifferenceQuotient_memLp_norm_le
    {d : ℕ} (U : Set (TimeVelocity d)) (hU : IsOpen U)
    (V : Set (TimeVelocity d)) (k : Fin d) (h : ℝ) (hh : h ≠ 0)
    (f g : TimeVelocity d → ℝ)
    (hf : ParabolicMemLpOn U (2 : ℝ≥0∞) f)
    (hg : ParabolicMemLpOn U (2 : ℝ≥0∞) g)
    (hweak : HasWeakVelocityPartialDerivOn U k f g)
    (hseg : ∀ z ∈ V, [z -[ℝ] spatialShift k h z] ⊆ U) :
    ∃ hq : ParabolicMemLpOn V (2 : ℝ≥0∞)
        (spatialDifferenceQuotient k h f),
      ‖hq.toLp (spatialDifferenceQuotient k h f)‖ ≤ ‖hg.toLp g‖ := by
  let W  := spatialSegmentSafeSet U k h
  have hW : IsOpen W := isOpen_spatialSegmentSafeSet U hU k h
  have hVW : V ⊆ W := by
    intro z hz
    aesop
  have hWU : W ⊆ U := by
    intro z hz
    exact hz (left_mem_segment ℝ z _)
  have hshift : MapsTo (spatialShift k h) W U := by
    intro z hz
    exact hz (right_mem_segment ℝ z _)
  let hqW  :=
    hf.spatialDifferenceQuotient_of_subset_mapsTo k h hWU hshift
  have hqW_bound : ‖hqW.toLp _‖ ≤ ‖hg.toLp g‖ := by
    apply HypoellipticAleksandrov.Analysis.norm_le_of_abs_real_inner_le_on_dense
      (dense_smoothCompactlySupported_toLp_timeVelocity hW)
      _ ‖hg.toLp g‖ (norm_nonneg _)
    intro q hq
    rcases hq with ⟨φ, hφW, hφsmooth, hφcompact, hφsupport, rfl⟩
    let hφglobal : MemLp φ (2) volume :=
      hφsmooth.continuous.memLp_of_hasCompactSupport hφcompact
    have hinner : (inner ℝ (hqW.toLp _)
        (hφW.toLp φ)) =
        ∫ z in W, spatialDifferenceQuotient k h f z * φ z
          ∂volume := by
      apply integral_congr_ae
      filter_upwards [hqW.coeFn_toLp, hφW.coeFn_toLp] with z hzq hzφ
      rw [hzq, hzφ]
      simp only [RCLike.inner_apply, conj_trivial, mul_comm]
    have houter : (∫ z in U, spatialDifferenceQuotient k h f z * φ z
          ∂volume) =
        ∫ z in W, spatialDifferenceQuotient k h f z * φ z
          ∂volume := by
      apply setIntegral_eq_of_subset_of_forall_diff_eq_zero hU.measurableSet hWU
      intro z hz
      have hznot : z ∉ tsupport φ := fun hzφ => hz.2 (hφsupport hzφ)
      rw [image_eq_zero_of_notMem_tsupport hznot, mul_zero]
    have hnorm : ‖hφglobal.toLp φ‖ = ‖hφW.toLp φ‖ := by
      rw [Lp.norm_toLp, Lp.norm_toLp,
        eLpNorm_restrict_eq_of_support_subset hφglobal.aestronglyMeasurable
          ((subset_tsupport φ).trans hφsupport)]
    rw [hinner, ← houter]
    simpa only [hnorm] using
      hweak.abs_setIntegral_spatialDifferenceQuotient_mul_le
        U k h f g φ hh hf hg hφsmooth hφcompact hφsupport
  let hqV : ParabolicMemLpOn V _
      _ :=
    hqW.mono_measure (Measure.restrict_mono_set volume hVW)
  refine ⟨hqV, ?_⟩
  calc
    ‖hqV.toLp _‖ ≤
        ‖hqW.toLp _‖ := by
      rw [Lp.norm_toLp, Lp.norm_toLp]
      refine ENNReal.toReal_mono hqW.eLpNorm_ne_top ?_
      exact eLpNorm_mono_measure _ (Measure.restrict_mono_set volume hVW)
    _ ≤ ‖hg.toLp g‖ := hqW_bound

end HypoellipticAleksandrov.Parabolic
