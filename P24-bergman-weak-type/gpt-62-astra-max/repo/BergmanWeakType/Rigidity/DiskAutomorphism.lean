/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Kernel
public import BergmanWeakType.Calculus
public import Mathlib.Analysis.Complex.Basic

/-! # Automorphisms interchanging two points of the open disk -/
@[expose] public section
noncomputable section
open Set Complex
open scoped ComplexConjugate
namespace Complex

/-- Nonvanishing of the derivative includes complex differentiability. This condition
is preserved under nonconstant locally uniform limits, by Hurwitz applied to the derivatives. -/
abbrev RegularOn (f : ℂ → ℂ) (U : Set ℂ) := ∀ z ∈ U, deriv f z ≠ 0

theorem RegularOn.diff {U : Set ℂ} {f : ℂ → ℂ} (h : RegularOn f U) : DifferentiableOn ℂ f U :=
  fun z hz ↦ (differentiableAt_of_deriv_ne_zero (h z hz)).differentiableWithinAt

theorem RegularOn.hd {U : Set ℂ} {f : ℂ → ℂ} (h : RegularOn f U) (z) (hz : z ∈ U) :
    HasDerivAt f (deriv f z) z := by simp_all [differentiableAt_of_deriv_ne_zero]

theorem RegularOn.comp {f g : ℂ → ℂ} {U V : Set ℂ} (hg : RegularOn g V) (hf : RegularOn f U)
    (hm : MapsTo f U V) : RegularOn (g ∘ f) U := fun z hz ↦ by
  rw [((hg.hd _ (hm hz)).comp z (hf.hd z hz)).deriv]; exact mul_ne_zero (hg _ (hm hz)) (hf z hz)

end Complex

namespace BergmanWeakType

def diskSwap (c z : ℂ) := (c - z) / (1 - star c * z)
def diskFactor (c : ℂ) : ℝ := 1 - ‖c‖^2

theorem diskFactor_pos {c : ℂ} (hc : c ∈ disk) : 0 < diskFactor c := by
  unfold diskFactor; simp_all

theorem factor_complex (c : ℂ) : (diskFactor c : ℂ) = 1 - star c * c := by
  simp [diskFactor, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]

variable {c z : ℂ} (hc : c ∈ disk) (hz : z ∈ disk)

include hc hz

theorem diskSwap_den : 1 - star c * z ≠ 0 := by grind [denominator_ne, mem_disk_iff]

theorem diskSwap_mem : diskSwap c z ∈ disk := by
  have h : ‖1 - star c * z‖^2 - ‖c-z‖^2 = diskFactor c * diskFactor z := by
    simp [diskFactor, Complex.sq_norm, Complex.normSq_apply]; ring
  rw [mem_disk_iff, diskSwap, norm_div, div_lt_one (norm_pos_iff.mpr (diskSwap_den hc hz))]
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)]
  linarith [mul_pos (diskFactor_pos hc) (diskFactor_pos hz)]

omit hc hz

@[simp] theorem diskSwap_zero (c : ℂ) : diskSwap c 0 = c := by simp [diskSwap]
@[simp] theorem diskSwap_self (c : ℂ) : diskSwap c c = 0 := by simp [diskSwap]

include hc hz

theorem diskSwap_swap : diskSwap c (diskSwap c z) = z := by
  grind [diskSwap, diskSwap_den]

omit hz

theorem diskSwap_bijOn : BijOn (diskSwap c) disk disk :=
  ⟨fun _ ↦ diskSwap_mem hc, fun _ hx _ hy h ↦ by grind [diskSwap_swap],
    fun z hz ↦ (by grind [diskSwap_mem, diskSwap_swap])⟩

include hz

theorem diskSwap_hasDerivAt : HasDerivAt (diskSwap c) (-(diskFactor c : ℂ)/(1-star c*z)^2) z := by
  unfold diskSwap
  scalar_deriv [diskSwap_den hc hz]
  rw [factor_complex]; ring

omit hz in
theorem diskSwap_regular : RegularOn (diskSwap c) disk := fun z hz ↦ by
  rw [(diskSwap_hasDerivAt hc hz).deriv]; exact div_ne_zero (by simp [(diskFactor_pos hc).ne']) (by grind [diskSwap_den])

theorem inv_deriv_swap : (deriv (diskSwap c) (diskSwap c z))⁻¹ = deriv (diskSwap c) z := by
  have eq : diskSwap c ∘ diskSwap c =ᶠ[nhds z] id := (Metric.isOpen_ball.eventually_mem hz).mono fun w hw ↦ diskSwap_swap hc hw
  have h := eq.deriv_eq
  rw [((diskSwap_regular hc).hd _ (diskSwap_mem hc hz) |>.comp z ((diskSwap_regular hc).hd z hz)).deriv, deriv_id] at h
  grind

end BergmanWeakType
