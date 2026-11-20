/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Planar.KernelNorms
public import DOZZ.Hypergeom.Planar.TwoPointRpow

/-! Exact integrability tests for the two differentiated planar kernels. -/

@[expose] public section

open MeasureTheory
open scoped Topology

namespace DOZZ.Proofs

private theorem measurable_rpow_of_nonneg_local {f : ℂ → ℝ} (hf : Measurable f)
    (hfn : ∀ u, 0 ≤ f u) (s : ℝ) : Measurable (fun u => f u ^ s) := by
  have hrepr : (fun u => f u ^ s) =
      fun u => if f u = 0 then 0 ^ s else Real.exp (s * Real.log (f u)) := by
    funext u
    by_cases hu : f u = 0
    · simp [hu]
    · rw [ite_eq_right hu, Real.rpow_def_of_pos (lt_of_le_of_ne (hfn u) (Ne.symm hu))]
      congr 1
      ring
  rw [hrepr]
  apply Measurable.ite
  · exact MeasurableSet.preimage (measurableSet_singleton (0 : ℝ)) hf
  · exact measurable_const
  · fun_prop

/-- Exact integrability criterion for the Wirtinger derivative kernel. -/
theorem integrable_planarWirtingerKernel_iff (k β : ℝ) (hk : 0 < k) (z : ℂ) (hz : z ≠ 0) :
    Integrable (DOZZ.planarWirtingerKernel k β z) volume ↔ k < β ∧ β < 2 := by
  have hnum : Measurable (fun u : ℂ => ‖u - z‖ ^ k) :=
    measurable_rpow_of_nonneg_local (by fun_prop) (fun u => norm_nonneg (u - z)) k
  have hden : Measurable (fun u : ℂ => ‖u‖ ^ β) :=
    measurable_rpow_of_nonneg_local (by fun_prop) (fun u => norm_nonneg u) β
  have hmeas : Measurable (DOZZ.planarWirtingerKernel k β z) := by
    change Measurable (fun u : ℂ =>
      ((‖u - z‖ ^ k : ℝ) : ℂ) / ((z - u) ^ 2 * ((‖u‖ ^ β : ℝ) : ℂ)))
    fun_prop
  have hstrong : AEStronglyMeasurable (DOZZ.planarWirtingerKernel k β z) volume :=
    hmeas.aestronglyMeasurable
  rw [← integrable_norm_iff hstrong]
  have heq : (fun u : ℂ => ‖DOZZ.planarWirtingerKernel k β z u‖) =ᵐ[volume]
      (fun u => ‖u‖ ^ (-β) * ‖u - z‖ ^ (k - 2)) := by
    filter_upwards [Measure.ae_ne volume (0 : ℂ), Measure.ae_ne volume z] with u hu0 huz
    have hnorm := norm_planarWirtingerKernel_eq k β z u hu0 huz
    have hnorm0 : 0 ≤ ‖u‖ := norm_nonneg u
    calc
      ‖DOZZ.planarWirtingerKernel k β z u‖ =
          ‖u - z‖ ^ (k - 2) / ‖u‖ ^ β := hnorm
      _ = ‖u‖ ^ (-β) * ‖u - z‖ ^ (k - 2) := by
        rw [div_eq_mul_inv, Real.rpow_neg hnorm0]
        ring
  rw [integrable_congr heq]
  rw [integrableOn_two_point_rpow_iff (-β) (k - 2) z hz]
  constructor
  · rintro ⟨hβ, hk, hsum⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hkb, hβ⟩
    exact ⟨by linarith, by linarith, by linarith⟩

end DOZZ.Proofs
