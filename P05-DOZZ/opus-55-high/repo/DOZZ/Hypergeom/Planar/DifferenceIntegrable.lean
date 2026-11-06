/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.PlanarDifferenceKernel
public import DOZZ.Hypergeom.Planar.RadialCriteria
public import DOZZ.Hypergeom.Planar.TaylorTail

/-! Absolute integrability of the first-order-subtracted difference kernel. -/

@[expose] public section

open MeasureTheory Set Metric
open scoped Topology

namespace DOZZ.Proofs

private theorem measurable_complex_norm_rpow (p : ℝ) :
    Measurable (fun u : ℂ => ‖u‖ ^ p) :=
  by fun_prop
section
variable (k β : ℝ)

private theorem measurable_planarDifferenceKernel (z : ℂ) :
    Measurable (DOZZ.planarDifferenceKernel k β z) := by
  change Measurable (fun u =>
    (‖u - z‖ ^ k - ‖u‖ ^ k) / ‖u‖ ^ β)
  fun_prop
section
variable (hk : 0 < k)
include hk

private theorem abs_planarDifferenceKernel_local_le (hβ : k < β) (z u : ℂ)
    (hball : ‖u‖ < 2 * ‖z‖) :
    |DOZZ.planarDifferenceKernel k β z u| ≤
      (3 * ‖z‖) ^ k * ‖u‖ ^ (-β) + ‖u‖ ^ (k - β) := by
  by_cases hu : u = 0
  · subst u
    have hβpos : 0 < β := lt_trans hk hβ
    simp [DOZZ.planarDifferenceKernel, Real.zero_rpow, ne_of_gt hk,
      ne_of_gt hβpos, ne_of_lt (by linarith : k - β < 0),
      ne_of_lt (by linarith : -β < 0)]
  · have hr : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hshift : ‖u - z‖ ≤ 3 * ‖z‖ := by
      calc
        ‖u - z‖ ≤ ‖u‖ + ‖z‖ := norm_sub_le ..
        _ ≤ 3 * ‖z‖ := by linarith
    have hpow : ‖u - z‖ ^ k ≤ (3 * ‖z‖) ^ k :=
      Real.rpow_le_rpow (norm_nonneg _) hshift hk.le
    have hnum : |‖u - z‖ ^ k - ‖u‖ ^ k| ≤
        (3 * ‖z‖) ^ k + ‖u‖ ^ k := by
      exact (abs_sub ..).trans (add_le_add
        (by rw [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]; exact hpow)
        (by rw [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _) ]))
    have hden : 0 < ‖u‖ ^ β := Real.rpow_pos_of_pos hr β
    have hneg : ‖u‖ ^ (-β) = 1 / ‖u‖ ^ β := by
      rw [show -β = 0 - β by ring, Real.rpow_sub hr, Real.rpow_zero]
    have hsub : ‖u‖ ^ k / ‖u‖ ^ β = ‖u‖ ^ (k - β) :=
      (Real.rpow_sub hr k β).symm
    change |(‖u - z‖ ^ k - ‖u‖ ^ k) / ‖u‖ ^ β| ≤ _
    rw [abs_div, abs_of_pos hden]
    calc
      _ ≤ ((3 * ‖z‖) ^ k + ‖u‖ ^ k) / ‖u‖ ^ β :=
        div_le_div_of_nonneg_right hnum hden.le
      _ = (3 * ‖z‖) ^ k * (1 / ‖u‖ ^ β) +
          ‖u‖ ^ k / ‖u‖ ^ β := by ring
      _ = _ := by simp_all

private theorem abs_planarDifferenceKernel_tail_le (hk₂ : k < 2) (z u : ℂ) (hu : u ≠ 0)
    (hlarge : 2 * ‖z‖ ≤ ‖u‖) :
    |DOZZ.planarDifferenceKernel k β z u| ≤
      (k + (k * (1 + (15 / 4) *
        ((1 - k / 2) * (1 / 4 : ℝ) ^ (k / 2 - 2))) / 2)) * ‖z‖ *
        ‖u‖ ^ (k - 1 - β) := by
  have hr := norm_pos_iff.mpr hu
  let w := z / u
  have hw : ‖w‖ ≤ 1 / 2 := by
    dsimp [w]
    rw [norm_div]
    apply (div_le_iff₀ hr).2
    linarith
  let T := k * (1 + (15 / 4) *
    ((1 - k / 2) * (1 / 4) ^ (k / 2 - 2)))
  have hT : 0 ≤ T := by
    bound
  have hfirst : |‖1 - w‖ ^ k - 1| ≤ (k + T / 2) * ‖w‖ := by
    calc
      |‖1 - w‖ ^ k - 1| =
          |(‖1 - w‖ ^ k - 1 + k * w.re) - k * w.re| := by
            simp
      _ ≤ |‖1 - w‖ ^ k - 1 + k * w.re| + |k * w.re| := abs_sub ..
      _ ≤ T * ‖w‖ ^ 2 + k * ‖w‖ := by
        refine add_le_add (norm_unit_taylor_remainder_le k hk hk₂ w hw) ?_
        rw [abs_mul, abs_of_nonneg hk.le]
        exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm w) hk.le
      _ ≤ (T / 2) * ‖w‖ + k * ‖w‖ := by
        have hsq : ‖w‖ ^ 2 ≤ (1 / 2) * ‖w‖ := by nlinarith [hw, norm_nonneg w]
        calc
          T * ‖w‖ ^ 2 + k * ‖w‖ ≤ T * ((1 / 2) * ‖w‖) + k * ‖w‖ :=
            add_le_add (mul_le_mul_of_nonneg_left hsq hT) le_rfl
          _ = (T / 2) * ‖w‖ + k * ‖w‖ := by ring
      _ = _ := by ring
  have hfactor : ‖u - z‖ ^ k = ‖u‖ ^ k * ‖1 - w‖ ^ k := by
    have heq : u - z = u * (1 - w) := by
      dsimp [w]
      field_simp [hu]
    rw [heq, norm_mul, Real.mul_rpow (norm_nonneg u) (norm_nonneg (1 - w))]
  have hnum : |‖u - z‖ ^ k - ‖u‖ ^ k| ≤
      (k + T / 2) * ‖u‖ ^ k * ‖w‖ := by
    rw [hfactor]
    have hpow := Real.rpow_nonneg (norm_nonneg u) k
    calc
      |‖u‖ ^ k * ‖1 - w‖ ^ k - ‖u‖ ^ k| =
          ‖u‖ ^ k * |‖1 - w‖ ^ k - 1| := by
            rw [show ‖u‖ ^ k * ‖1 - w‖ ^ k - ‖u‖ ^ k =
              ‖u‖ ^ k * (‖1 - w‖ ^ k - 1) by ring,
              abs_mul, abs_of_nonneg hpow]
      _ ≤ ‖u‖ ^ k * ((k + T / 2) * ‖w‖) :=
        mul_le_mul_of_nonneg_left hfirst hpow
      _ = (k + T / 2) * ‖u‖ ^ k * ‖w‖ := by ring
  have hden := Real.rpow_pos_of_pos hr β
  have hpow₁ : ‖u‖ ^ k / ‖u‖ = ‖u‖ ^ (k - 1) := by
    simpa [Real.rpow_one] using (Real.rpow_sub hr k 1).symm
  have hpow₂ :=
    (Real.rpow_sub hr (k - 1) β).symm
  have hwNorm : ‖w‖ = ‖z‖ / ‖u‖ := by aesop
  change |(‖u - z‖ ^ k - ‖u‖ ^ k) / ‖u‖ ^ β| ≤ _
  rw [abs_div, abs_of_pos hden]
  calc
    _ ≤ ((k + T / 2) * ‖u‖ ^ k * ‖w‖) / ‖u‖ ^ β :=
      div_le_div_of_nonneg_right hnum hden.le
    _ = (k + T / 2) * ‖z‖ *
        (‖u‖ ^ k / ‖u‖) / ‖u‖ ^ β := by grind
    _ = (k + T / 2) * ‖z‖ * ‖u‖ ^ (k - 1 - β) := by
      calc
        _ = (k + T / 2) * ‖z‖ *
            (‖u‖ ^ (k - 1) / ‖u‖ ^ β) := by grind
        _ = _ := by simp_all
    _ ≤ (k + T / 2) * ‖z‖ * ‖u‖ ^ (k - 1 - β) := le_rfl

theorem integrableOn_planarDifferenceKernel_ball (hβ : k < β) (hβ₂ : β < 2) (z : ℂ) (hz : z ≠ 0) :
    IntegrableOn (DOZZ.planarDifferenceKernel k β z)
      (ball (0 : ℂ) (2 * ‖z‖)) volume := by
  let R : ℝ := 2 * ‖z‖
  let A := (3 * ‖z‖) ^ k
  have hR : 0 < R := by positivity
  have hA : 0 ≤ A := by positivity
  have hp₀ : -2 < -β := by linarith
  have hp₁ : -2 < k - β := by linarith
  have h₀ :=
    ((integrableOn_norm_rpow_ball_iff (-β) R hR).2 hp₀).const_mul A
  have h₁ :=
    (integrableOn_norm_rpow_ball_iff _ R hR).2 hp₁
  apply (h₀.add h₁).mono' (measurable_planarDifferenceKernel k β z).aestronglyMeasurable
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with u hu
  have hball : ‖u‖ < 2 * ‖z‖ := by
    aesop
  exact abs_planarDifferenceKernel_local_le k β hk hβ z u hball

theorem integrableOn_planarDifferenceKernel_tail (hβ₂ : β < 2) (hβtail : k + 1 < β)
    (z : ℂ) (hz : z ≠ 0) :
    IntegrableOn (DOZZ.planarDifferenceKernel k β z)
      (ball (0 : ℂ) (2 * ‖z‖))ᶜ volume := by
  let R : ℝ := 2 * ‖z‖
  let p := k - 1 - β
  let T := k * (1 + (15 / 4) *
    ((1 - k / 2) * (1 / 4) ^ (k / 2 - 2)))
  let A := (k + T / 2) * ‖z‖
  have hR : 0 < R := by positivity
  have hk₂ : k < 2 := by linarith
  have hp : p < -2 := by linarith
  have hT : 0 ≤ T := by
    bound
  have hA : 0 ≤ A := by positivity
  have hrad :=
    (integrableOn_norm_rpow_ball_compl_iff p R hR).2 hp
  change Integrable _
      (volume.restrict _ᶜ)
  apply (hrad.const_mul A).mono' (measurable_planarDifferenceKernel k β z).aestronglyMeasurable
  filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet.compl] with u hu
  have hlarge : 2 * ‖z‖ ≤ ‖u‖ := by
    aesop
  have hu : u ≠ 0 := by
    intro hu0
    subst u
    have h0ball : 0 ∈ ball (0 : ℂ) R := by
      simpa [Metric.mem_ball] using hR
    exact hu h0ball
  simpa [A, p, T, mul_assoc] using (abs_planarDifferenceKernel_tail_le k β hk hk₂ z u hu hlarge)

theorem integrable_planarDifferenceKernel (hβ : k < β) (hβ₂ : β < 2) (hβtail : k + 1 < β) :
    ∀ z : ℂ, Integrable (DOZZ.planarDifferenceKernel k β z) volume := by
  intro z
  by_cases hz : z = 0
  · subst z
    have hzero : DOZZ.planarDifferenceKernel k β 0 = fun _ : ℂ => 0 := by
      funext u
      simp [DOZZ.planarDifferenceKernel]
    simp_all
  · have hball := integrableOn_planarDifferenceKernel_ball k β hk hβ hβ₂ z hz
    rw [← integrableOn_univ, ← Set.union_compl_self _,
      integrableOn_union]
    exact ⟨hball, (integrableOn_planarDifferenceKernel_tail k β hk hβ₂ hβtail z hz)⟩

end

end

end DOZZ.Proofs
