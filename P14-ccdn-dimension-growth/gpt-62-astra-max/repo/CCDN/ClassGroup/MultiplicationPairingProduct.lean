/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! Nondegeneracy of multiplication in a field extension detects a product
of basis lengths controlling every successive minimum. -/

@[expose] public section
namespace CCDN
noncomputable section

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] (A : Matrix ι ι R) (hA : A.det ≠ 0)

include hA in
private lemma exists_permutation_nonzero_entries :
    ∃ σ : Equiv.Perm ι, ∀ i, A (σ i) i ≠ 0 := by
  by_contra h
  push Not at h
  apply hA
  rw [Matrix.det_apply]
  apply Finset.sum_eq_zero
  intro σ _
  obtain ⟨i, hi⟩ := h σ
  rw [Finset.prod_eq_zero (f := fun j ↦ A (σ j) j) (Finset.mem_univ i) hi, smul_zero]

include hA in
private lemma determinant_weight_product_bound
    (w : ι → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hw : ∀ i j, A i j ≠ 0 → M ≤ w i * w j) :
    M ^ Fintype.card ι ≤ (∏ i, w i) ^ 2 := by
  obtain ⟨σ, hσ⟩ := exists_permutation_nonzero_entries A hA
  calc
    M ^ Fintype.card ι = ∏ _i : ι, M := by simp
    _ ≤ ∏ i : ι, w (σ i) * w i :=
      Finset.prod_le_prod₀ (fun _ _ ↦ hM) (by grind)
    _ = (∏ i, w i) ^ 2 := by
      rw [Finset.prod_mul_distrib, Equiv.prod_comp, sq]

/-- The form `(x,y) ↦ ℓ(xy)` for a basis coordinate `ℓ` is nondegenerate:
for `x ≠ 0`, multiplication by `x` is surjective. In particular its matrix
contains a permutation of nonzero entries. -/
theorem field_basis_minimum_product (b : Module.Basis ι F K) (q : ι) (w : ι → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hw : ∀ i j, b.coord q (b i * b j) ≠ 0 → M ≤ w i * w j) :
    M ^ Fintype.card ι ≤ (∏ i, w i) ^ 2 := by
  let B : LinearMap.BilinForm F K := (LinearMap.mul F K).compr₂ (b.coord q)
  have hB : B.Nondegenerate := by
    constructor <;> intro x hx <;> by_contra hn <;> specialize hx (x⁻¹ * b q) <;>
      change b.coord q (_ * _) = 0 at hx
    · simp [mul_inv_cancel_left₀ hn] at hx
    · simp [mul_comm _ x, mul_inv_cancel_left₀ hn] at hx
  exact determinant_weight_product_bound _ ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB) w hM (by simpa [LinearMap.BilinForm.toMatrix_apply, B])

end
end CCDN
