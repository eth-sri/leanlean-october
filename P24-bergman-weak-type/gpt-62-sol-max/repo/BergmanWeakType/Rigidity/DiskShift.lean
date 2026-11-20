/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Kernel
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section
noncomputable section

open Set Complex
open scoped ComplexConjugate

namespace BergmanWeakType

/-- The disk automorphism sending zero to `a`, written as a function on the plane. -/
def diskShift (a z : ℂ) : ℂ := (a + z) / (1 + z * conj a)

@[simp] theorem diskShift_zero (a : ℂ) : diskShift a 0 = a := by simp [diskShift]

@[simp] theorem diskShift_neg_self (a : ℂ) : diskShift (-a) a = 0 := by simp [diskShift]

theorem diskShift_den_ne_zero {a z : ℂ} (ha : a ∈ disk) (hz : z ∈ disk) : 1 + z * conj a ≠ 0 := by
  simpa only [neg_mul, sub_neg_eq_add, starRingEnd_apply] using
    kernel_denominator_ne_zero (z := -z) (w := a) (by simpa using hz) ((mem_disk_iff _).mp ha).le

theorem diskShift_mapsTo {a : ℂ} (ha : a ∈ disk) : MapsTo (diskShift a) disk disk := by
  intro z hz
  have h₁ : 0 < 1 - ‖a‖ ^ 2 := by simp_all
  have h₂ : 0 < 1 - ‖z‖ ^ 2 := by simp_all
  have he : ‖1 + z * conj a‖ ^ 2 - ‖a + z‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
    simp [Complex.sq_norm, Complex.normSq_add, Complex.normSq_mul, Complex.mul_re]
    ring
  rw [mem_disk_iff, diskShift, norm_div, div_lt_one₀ (norm_pos_iff.mpr
    (diskShift_den_ne_zero ha hz))]
  nlinarith [mul_pos h₁ h₂, norm_nonneg (1 + z * conj a), norm_nonneg (a + z)]

theorem diskShift_neg_apply {a z : ℂ} (ha : a ∈ disk) (hz : z ∈ disk) :
    diskShift (-a) (diskShift a z) = z := by
  have h := diskShift_den_ne_zero ha hz
  have hn := diskShift_den_ne_zero (a := -a) (by simp_all)
    (diskShift_mapsTo ha hz)
  grind [diskShift]

theorem diskShift_bijOn {a : ℂ} (ha : a ∈ disk) : BijOn (diskShift a) disk disk := by
  have hn : -a ∈ disk := by simp_all
  exact (show InvOn (diskShift (-a)) (diskShift a) disk disk from
    ⟨fun _ ↦ diskShift_neg_apply ha, fun w hw ↦ by simpa using diskShift_neg_apply hn hw⟩).bijOn
    (diskShift_mapsTo ha) (diskShift_mapsTo hn)

theorem hasDerivAt_diskShift {a z : ℂ} (ha : a ∈ disk) (hz : z ∈ disk) :
    HasDerivAt (diskShift a) ((1 - a * conj a) / (1 + z * conj a) ^ 2) z := by
  convert ((hasDerivAt_id z).const_add a).div (((hasDerivAt_id z).mul_const (conj a)).const_add 1)
    (diskShift_den_ne_zero ha hz) using 1
  · rfl
  grind

theorem diskShift_tau_ne_zero {a : ℂ} (ha : a ∈ disk) : 1 - a * conj a ≠ 0 := by
  exact kernel_denominator_ne_zero ha (mem_disk_iff _ |>.mp ha).le

theorem differentiableOn_diskShift {a : ℂ} (ha : a ∈ disk) :
    DifferentiableOn ℂ (diskShift a) disk :=
  fun _ hz ↦ (hasDerivAt_diskShift ha hz).differentiableAt.differentiableWithinAt

end BergmanWeakType
