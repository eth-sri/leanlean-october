/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! Multiplication paired with any nonzero coordinate functional is nondegenerate. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- A lower bound for a product of basis weights on every nonzero entry of the
multiplication pairing gives an inequality for the product of all the weights. -/
theorem basis_multiplication_product {F K ι : Type*} [Field F] [Field K] [Algebra F K]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F K) (j : ι) (w : ι → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hw : ∀ i k, b.coord j (b i * b k) ≠ 0 → M ≤ w i * w k) :
    M ^ Fintype.card ι ≤ (∏ i, w i) ^ 2 := by
  let B := (LinearMap.mul F K).compr₂ (b.coord j)
  have hl (x : K) (hx : ∀ y : K, b.coord j (x * y) = 0) : x = 0 := by
    by_contra hx0
    simpa [← mul_assoc, hx0] using hx (x⁻¹ * b j)
  have hB : B.Nondegenerate := ⟨hl, fun x hx => hl x (fun y => by simpa [B, mul_comm] using hx y)⟩
  have hdet := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB
  have hperm : ∃ σ : Equiv.Perm ι, ∀ i, b.coord j (b (σ i) * b i) ≠ 0 := by
    by_contra! h
    apply hdet
    rw [Matrix.det_apply]
    apply Finset.sum_eq_zero
    intro σ _
    obtain ⟨i, hi⟩ := h σ
    have hz : LinearMap.BilinForm.toMatrix b B (σ i) i = 0 := by
      simpa [LinearMap.BilinForm.toMatrix_apply, B] using hi
    rw [Finset.prod_eq_zero (f := fun k => LinearMap.BilinForm.toMatrix b B (σ k) k)
      (Finset.mem_univ i) hz, smul_zero]
  obtain ⟨σ, hσ⟩ := hperm
  calc
    M ^ Fintype.card ι = ∏ _i : ι, M := by simp
    _ ≤ ∏ i : ι, w (σ i) * w i :=
      Finset.prod_le_prod₀ (fun _ _ => hM) (fun i _ => hw _ _ (hσ i))
    _ = (∏ i, w i) ^ 2 := by rw [Finset.prod_mul_distrib, Equiv.prod_comp, sq]

end
end CCDN
