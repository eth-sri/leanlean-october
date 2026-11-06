/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs

/-! The algebraic nondegeneracy input for the uniform shape estimate of
a number-field lattice. Multiplication preserving a rational hyperplane
must be multiplication by a scalar. The proof uses linear functionals and
works over an arbitrary field extension. -/

@[expose] public section
namespace CCDN
noncomputable section

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- On the complement to the scalars inside a hyperplane containing one,
the multiplication pairing detected by the hyperplane functional is
nondegenerate. The second functional specifies that complement explicitly. -/
theorem multiplication_pairing_on_hyperplane_complement
    (ℓ μ : K →ₗ[F] F) (hℓ : ℓ ≠ 0) (hℓ1 : ℓ 1 = 0) (hμ1 : μ 1 = 1)
    (a : K) (ha0 : a ≠ 0) (hℓa : ℓ a = 0) (hμa : μ a = 0) :
    ∃ b : K, ℓ b = 0 ∧ μ b = 0 ∧ ℓ (a * b) ≠ 0 := by
  have ha : a ∉ Set.range (algebraMap F K) := by
    rintro ⟨c, hc⟩
    rw [← hc, Algebra.algebraMap_eq_smul_one, map_smul, hμ1, smul_eq_mul, mul_one] at hμa
    exact ha0 (by rw [← hc, hμa, map_zero])
  have hwit : ∃ b : K, ℓ b = 0 ∧ ℓ (a * b) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨z, hz⟩ : ∃ z : K, ℓ z ≠ 0 := by
      by_contra hz; push Not at hz; exact hℓ (LinearMap.ext hz)
    let u : K := (ℓ z)⁻¹ • z
    have hu : ℓ u = 1 := by simp [u, hz]
    let c : F := ℓ (a * u)
    have hp (t : K) : ℓ (a * t) = c * ℓ t := by
      have h0 := h (t - ℓ t • u) (by simp [hu])
      rw [mul_sub, mul_smul_comm, map_sub, map_smul] at h0
      change ℓ (a * t) - ℓ t * c = 0 at h0
      exact (sub_eq_zero.mp h0).trans (mul_comm _ _)
    refine ha ⟨c, ?_⟩
    by_contra hne
    have hzero (t : K) : ℓ ((a - algebraMap F K c) * t) = 0 := by
      rw [sub_mul, ← Algebra.smul_def, map_sub, map_smul, hp]; simp
    have hh := hzero ((a - algebraMap F K c)⁻¹ * u)
    rw [mul_inv_cancel_left₀ (sub_ne_zero.mpr (Ne.symm hne)), hu] at hh
    exact one_ne_zero hh
  obtain ⟨b, hb, hab⟩ := hwit
  refine ⟨b - μ b • (1 : K), by simp [hb, hℓ1], by simp [hμ1], ?_⟩
  simpa only [mul_sub, mul_smul_comm, mul_one, map_sub, map_smul,
    hℓa, smul_zero, sub_zero] using hab

end
end CCDN
