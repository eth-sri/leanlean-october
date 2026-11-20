/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.ProjectiveSection
public import CCDN.Height.ProjectiveBox

/-! Finite affine fibers of a linear map exclude a projective base point.
Projective fibers inject into affine fibers after choosing a fixed
nonzero representative in the target. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- If the zeros of `I` in `ℚ^(n+1)` killed by the linear map `L` form a set of at most `M`
elements, then `L` does not vanish on the representative of any point of the projective zero
locus of `I`. -/
theorem projective_linear_image_ne_zero_of_finite_zero_fiber
    {n r : ℕ} (I : Ideal (MvPolynomial (Fin (n + 1)) ℚ))
    (L : (Fin (n + 1) → ℚ) →ₗ[ℚ] (Fin r → ℚ)) (M : ℕ)
    (hfinite : ∀ s : Finset (Fin (n + 1) → ℚ),
      (∀ z ∈ s, z ∈ idealZeroLocus I) →
      (∀ z ∈ s, L z = 0) → s.card ≤ M)
    (x : ProjectivePoint n) (hx : x ∈ projectiveIdealZeroLocus I) :
    L x.rep ≠ 0 := by
  classical
  intro hzero
  let z : Fin (M + 1) → (Fin (n + 1) → ℚ) := fun j => (j.val + 1 : ℚ) • x.rep
  have hz (j : Fin (M + 1)) : z j ≠ 0 := by
    apply smul_ne_zero _ x.rep_nonzero
    positivity
  have hmk (j : Fin (M + 1)) : Projectivization.mk ℚ (z j) (hz j) = x := by
    rw [← x.mk_rep, Projectivization.mk_eq_mk_iff']
    tauto
  have hinj : Function.Injective z := by
    intro i j hij
    have hh := smul_left_injective ℚ x.rep_nonzero hij
    apply Fin.ext
    exact_mod_cast (add_right_cancel hh)
  have hh := hfinite (Finset.univ.image z) (by
    intro w hw f hf
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
    tauto) (by
    intro w hw
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
    simp [z, map_smul, hzero, smul_zero])
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] at hh
  omega

/-- A projective fiber injects into the affine fiber over a specified nonzero representative. -/
theorem projective_linear_fiber_card_le
    {n m : ℕ} (A : Set (Fin (n + 1) → ℚ))
    (L : (Fin (n + 1) → ℚ) →ₗ[ℚ] (Fin (m + 1) → ℚ))
    (s : Finset (ProjectivePoint n))
    (hs : ∀ x ∈ s, ∀ v hv, Projectivization.mk ℚ v hv = x → v ∈ A)
    (hL : ∀ x ∈ s, L x.rep ≠ 0)
    (y : ProjectivePoint m)
    (he : ∀ (x) (hx : x ∈ s), Projectivization.mk ℚ (L x.rep) (hL x hx) = y)
    (M : ℕ)
    (hfinite : ∀ t : Finset (Fin (n + 1) → ℚ),
      (∀ z ∈ t, z ∈ A) →
      (∀ z ∈ t, L z = y.rep) → t.card ≤ M) :
    s.card ≤ M := by
  classical
  have hscale (x : s) : ∃ c : ℚˣ, c • y.rep = L x.val.rep := by
    exact (Projectivization.mk_eq_mk_iff ℚ _ _ _ _).mp
      ((he x.val x.property).trans y.mk_rep.symm)
  choose c hc using hscale
  let z := fun x => (c x : ℚ)⁻¹ • x.val.rep
  have hz (x : s) := smul_ne_zero (inv_ne_zero (c x).ne_zero) x.val.rep_nonzero
  have hmk (x : s) : Projectivization.mk ℚ (z x) (hz x) = x.val := by
    rw [← x.val.mk_rep, Projectivization.mk_eq_mk_iff']
    exact Exists.intro (↑(c x))⁻¹ rfl
  have himage (x : s) : L (z x) = y.rep := by
    dsimp only [z]
    rw [map_smul, ← hc x]
    change (c x : ℚ)⁻¹ • ((c x : ℚ) • y.rep) = y.rep
    rw [smul_smul, inv_mul_cancel₀ (c x).ne_zero, one_smul]
  have hinj : Function.Injective z := by
    intro x x' heq
    apply Subtype.ext
    rw [← hmk x, ← hmk x']
    simp [heq.symm]
  have hh := hfinite (Finset.univ.image z) (by
    intro w hw
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hw
    exact hs x.val x.property (z x) (hz x) (hmk x)) (by
    intro w hw
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hw
    exact himage x)
  simpa [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe] using hh

end
end CCDN
