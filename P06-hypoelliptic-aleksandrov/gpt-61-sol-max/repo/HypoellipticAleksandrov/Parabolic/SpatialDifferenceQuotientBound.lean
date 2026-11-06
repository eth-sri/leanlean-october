module

public import HypoellipticAleksandrov.Parabolic.SpatialDifferenceQuotientCollar
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Compact-open bounds for spatial difference quotients

This module obtains a uniform signed spatial difference-quotient bound on a
compact time--velocity carrier from continuous differentiability on an open
neighborhood.  The quotient remains totalized at a zero increment.
-/

 public section

namespace HypoellipticAleksandrov.Parabolic

open scoped Convex

variable {d : ℕ}

private theorem segment_subset_cthickening_of_spatialShift
     {S : HypoellipticAleksandrov.Parabolic.Region d} {δ h : ℝ} {k : Fin d}
    {z : TimeVelocity d} (hz : z ∈ S) (hh : |h| ≤ δ) :
    [z -[ℝ] spatialShift k h z] ⊆ Metric.cthickening δ S := (fun ⦃w⦄ hw =>
  Metric.mem_cthickening_of_dist_le w z δ S hz
    (Trans.trans
      (Trans.trans
        (Trans.trans (Trans.trans (dist_eq_norm w z) (norm_sub_le_of_mem_segment hw))
          (Eq.symm (dist_eq_norm (spatialShift k h z) z)))
        (dist_spatialShift k h z))
      hh))

variable {S U : HypoellipticAleksandrov.Parabolic.Region d} {f : HypoellipticAleksandrov.Parabolic.ScalarField d}

private theorem abs_spatialDifferenceQuotient_le_of_fderiv_bound

    {δ C h : ℝ} {k : Fin d} {z : TimeVelocity d}
    (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U)
    (hδU : Metric.cthickening δ S ⊆ U)
    (hC : ∀ w ∈ Metric.cthickening δ S, ‖fderiv ℝ f w‖ ≤ C)
    (hCnonneg : 0 ≤ C)
    (hh : |h| ≤ δ) (hz : z ∈ S) :
    |spatialDifferenceQuotient k h f z| ≤ C := by
  let sharedTerm_094ce16c37 := (f (spatialShift k h z) - f z)

  by_cases hhzero : h = 0
  · subst h
    simp_all
  · have hsegment : (([z -[ℝ] spatialShift k h z])) ⊆ Metric.cthickening δ S :=
      segment_subset_cthickening_of_spatialShift hz hh



    have hdiff : ‖sharedTerm_094ce16c37‖ ≤
        C * ‖spatialShift k h z - z‖ :=
      (convex_segment z (spatialShift k h z)).norm_image_sub_le_of_norm_fderiv_le
        (by
            intro w hw
            exact (hf.contDiffAt (hU.mem_nhds ((hsegment.trans hδU) hw))).differentiableAt_one) (by
            intro w hw
            exact hC w (hsegment hw)) (left_mem_segment ℝ z _)
        (right_mem_segment ℝ z _)

    rw [spatialDifferenceQuotient_apply, spatialTranslate_apply, abs_div]
    calc
      |sharedTerm_094ce16c37| / |h| ≤ (C * |h|) / |h| :=
        div_le_div_of_nonneg_right (by
            calc
              |sharedTerm_094ce16c37| = ‖sharedTerm_094ce16c37‖ :=
                by rw [Real.norm_eq_abs]
              _ ≤ C * ‖spatialShift k h z - z‖ := hdiff
              _ = C * |h| := by
                rw [← dist_eq_norm, dist_spatialShift]) (abs_nonneg h)
      _ = C := mul_div_cancel_right₀ C (abs_ne_zero.mpr hhzero)

/-- A scalar field which is continuously differentiable on an open neighborhood
has uniformly bounded signed spatial difference quotients on a compact carrier. -/
theorem IsCompact.exists_spatialDifferenceQuotient_bound_of_contDiffOn_one

    (hS : IsCompact S) (hU : IsOpen U) (hSU : S ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      Metric.cthickening δ S ⊆ U ∧
      (∀ z ∈ Metric.cthickening δ S, ‖fderiv ℝ f z‖ ≤ C) ∧
      (∀ (k : Fin d) (h : ℝ), |h| ≤ δ →
        Set.MapsTo (spatialShift k h) S U) ∧
      (∀ (k : Fin d) (h : ℝ) (z : TimeVelocity d), |h| ≤ δ → z ∈ S →
        |spatialDifferenceQuotient k h f z| ≤ C) := by
  obtain ⟨δ, hδ, hδU, hshift⟩ :=
    IsCompact.exists_spatialShift_cthickening_collar hS hU hSU


  obtain ⟨C₀, hC₀⟩ := hS.cthickening.exists_bound_of_continuousOn ((hf.continuousOn_fderiv_of_isOpen hU (by norm_num)).mono hδU)
  refine ⟨δ, max C₀ 0, hδ, le_max_right _ _, hδU, ?_, hshift, ?_⟩
  · intro z hz
    exact (hC₀ z hz).trans (le_max_left _ _)
  · intro k h z hh hz
    exact abs_spatialDifferenceQuotient_le_of_fderiv_bound hU hf hδU
      (fun w hw => (hC₀ w hw).trans (le_max_left _ _)) (le_max_right _ _) hh hz

end HypoellipticAleksandrov.Parabolic
