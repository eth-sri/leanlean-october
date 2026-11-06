/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Planar.TaylorTail
public import Mathlib.Analysis.Complex.Isometry
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Rotation and scaling identities for the corrected planar Taylor kernel. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Topology

namespace DOZZ.Proofs
section
variable (k β : ℝ)
section
variable (hk : 0 < k) (hβ : k < β)
include hk hβ

theorem planarTaylorRemainder_rotate (ξ z v : ℂ) (hξ : ‖ξ‖ = 1) :
    DOZZ.planarTaylorRemainder k β (ξ * z) (ξ * v) =
      DOZZ.planarTaylorRemainder k β z v := by
  by_cases hv : v = 0
  · subst v
    simp [DOZZ.planarTaylorRemainder, Real.zero_rpow, ne_of_gt hk, ne_of_gt (lt_trans hk hβ)]
  · have hξ0 : ξ ≠ 0 := by
      aesop
    have hnormV : ‖ξ * v‖ = ‖v‖ := by simp_all
    have hshift : ξ * v - ξ * z = ξ * (v - z) := by ring
    have hnormShift : ‖ξ * v - ξ * z‖ = ‖v - z‖ := by
      simp_all
    have hquot : (ξ * z) / (ξ * v) = z / v := by
      field_simp
    have hstarquot : star (ξ * z) / star (ξ * v) = star z / star v := by
      simpa using (congrArg star hquot)
    rw [DOZZ.planarTaylorRemainder, DOZZ.planarTaylorRemainder,
      hnormShift, hnormV, hquot, hstarquot]

theorem planarTaylorRemainder_real_scale (r : ℝ) (hr : 0 < r) (v : ℂ) :
    DOZZ.planarTaylorRemainder k β (r : ℂ) (r • v) =
      r ^ (k - β) * DOZZ.planarTaylorRemainder k β 1 v := by
  by_cases hv : v = 0
  · subst v
    have hβpos : 0 < β := lt_trans hk hβ
    simp [DOZZ.planarTaylorRemainder, Real.zero_rpow, ne_of_gt hk, ne_of_gt hβpos]
  · have hnormv : ‖r • v‖ = r * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    have hshift : r • v - (r : ℂ) = (r : ℂ) * (v - 1) := by
      change (r : ℂ) * v - (r : ℂ) = (r : ℂ) * (v - 1)
      ring
    have hnormshift : ‖r • v - (r : ℂ)‖ = r * ‖v - 1‖ := by
      simp_all
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hquot : (r : ℂ) / (r • v) = 1 / v := by
      grind
    have hstarquot : star (r : ℂ) / star (r • v) = star 1 / star v := by
      simpa using (congrArg star hquot)
    have hpowerV : (r * ‖v‖) ^ k = r ^ k * ‖v‖ ^ k :=
      Real.mul_rpow hr.le (norm_nonneg v)
    have hpowerShift : (r * ‖v - 1‖) ^ k = r ^ k * ‖v - 1‖ ^ k :=
      Real.mul_rpow hr.le (norm_nonneg (v - 1))
    have hpowerDen : (r * ‖v‖) ^ β = r ^ β * ‖v‖ ^ β :=
      Real.mul_rpow hr.le (norm_nonneg v)
    have hnum :
        ‖r • v - (r : ℂ)‖ ^ k - ‖r • v‖ ^ k +
            (k / 2) * ‖r • v‖ ^ k *
              ((r : ℂ) / (r • v) + star (r : ℂ) / star (r • v)).re =
          r ^ k * (‖v - 1‖ ^ k - ‖v‖ ^ k +
            (k / 2) * ‖v‖ ^ k * (1 / v + star 1 / star v).re) := by
      grind
    change (‖r • v - (r : ℂ)‖ ^ k - ‖r • v‖ ^ k +
        (k / 2) * ‖r • v‖ ^ k *
          ((r : ℂ) / (r • v) + star (r : ℂ) / star _).re) /
        ‖r • v‖ ^ β =
      r ^ (k - β) *
        ((‖v - 1‖ ^ k - ‖v‖ ^ k + (k / 2) * ‖v‖ ^ k *
          (1 / v + star 1 / star v).re) / ‖v‖ ^ β)
    rw [hnum, hnormv, hpowerDen]
    have hrβ : 0 < r ^ β := Real.rpow_pos_of_pos hr β
    have hvβ : 0 < ‖v‖ ^ β := by positivity
    calc
      _ = (r ^ k / r ^ β) *
          ((‖v - 1‖ ^ k - ‖v‖ ^ k + (k / 2) * ‖v‖ ^ k *
            (1 / v + star 1 / star v).re) / ‖v‖ ^ β) := by
              ring
      _ = _ := by rw [← Real.rpow_sub hr k β]

end
section
variable (hk : 0 < k) (hβ : k < β) (ξ : ℂ) (hξ : ‖ξ‖ = 1) (r : ℝ) (hr : 0 < r) (z : ℂ) (hz : ξ * (r : ℂ) = z)
include hk hβ hξ hr hz

theorem planarTaylorRemainder_rotated_scale (v : ℂ) :
    DOZZ.planarTaylorRemainder k β z (ξ * (r • v)) =
      r ^ (k - β) * DOZZ.planarTaylorRemainder k β 1 v := by
  calc
    DOZZ.planarTaylorRemainder k β z _ =
        DOZZ.planarTaylorRemainder k β .. := by simp_all
    _ = DOZZ.planarTaylorRemainder k β r _ :=
      planarTaylorRemainder_rotate k β hk hβ ξ r _ hξ
    _ = r ^ (k - β) * DOZZ.planarTaylorRemainder k β 1 v :=
      planarTaylorRemainder_real_scale k β hk hβ r hr v

theorem planarTaylorRemainder_integral_scale :
    (∫ u : ℂ, DOZZ.planarTaylorRemainder k β z u) =
      r ^ (2 + k - β) *
        (∫ u : ℂ, DOZZ.planarTaylorRemainder k β 1 u) := by
  let g : ℂ → ℝ := fun u => DOZZ.planarTaylorRemainder k β z (ξ * u)
  have hc := hξ
  have hrotation : (∫ u : ℂ, g u) =
      (∫ u : ℂ, DOZZ.planarTaylorRemainder k β z u) := by
    let c : Circle := ⟨ξ, by simpa [Submonoid.unitSphere] using hξ⟩
    simpa using
      (LinearIsometryEquiv.measurePreserving (rotation c)).integral_comp
        ((rotation c).toContinuousLinearEquiv.toHomeomorph).measurableEmbedding
        (DOZZ.planarTaylorRemainder k β z)
  have hscaling :
      (∫ u : ℂ, g (r • u)) = (r ^ 2)⁻¹ * (∫ u : ℂ, g u) := by
    have h := Measure.integral_comp_smul_of_nonneg volume g r (hR := hr.le)
    simp_all
  have hpoint : (fun u => g (r • u)) = fun u =>
      r ^ (k - β) * DOZZ.planarTaylorRemainder k β 1 u := by
    funext u
    exact planarTaylorRemainder_rotated_scale k β hk hβ ξ hξ r hr z hz u
  rw [hpoint, integral_const_mul, hrotation] at hscaling
  have hmul := congrArg (fun x : ℝ => r ^ 2 * x) hscaling
  have hleft : r ^ 2 * (r ^ (k - β) *
      (∫ u : ℂ, DOZZ.planarTaylorRemainder k β 1 u)) =
      r ^ (2 + k - β) *
        (∫ u : ℂ, DOZZ.planarTaylorRemainder k β 1 u) := by
    have hp : r ^ 2 * r ^ (k - β) = r ^ (2 + (k - β)) := by
      rw [← Real.rpow_natCast r 2]
      exact (Real.rpow_add hr 2 _).symm
    grind
  have hright : r ^ 2 * ((r ^ 2)⁻¹ *
      (∫ u : ℂ, DOZZ.planarTaylorRemainder k β z u)) =
      (∫ u : ℂ, DOZZ.planarTaylorRemainder k β z u) := by
    field_simp
  linarith

end

end

end DOZZ.Proofs
