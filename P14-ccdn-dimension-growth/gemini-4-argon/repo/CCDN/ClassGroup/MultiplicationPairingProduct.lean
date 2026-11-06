/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import CCDN.ClassGroup.FieldMultiplicationHyperplane
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! Determinant nondegeneracy turns multiplication bounds on a hyperplane
complement into the product inequality used to control the largest
successive minimum. This file contains the algebraic product step. -/

@[expose] public section
namespace CCDN
noncomputable section

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- The intersection of the kernels of two linear functionals `ℓ` and `μ` on `K`. -/
def hyperplaneComplement (ℓ μ : K →ₗ[F] F) : Submodule F K :=
  LinearMap.ker ℓ ⊓ LinearMap.ker μ

/-- Let `ℓ ≠ 0` and `μ` be linear functionals on `K` with `ℓ 1 = 0` and `μ 1 = 1`, and let `b` be a
basis of `hyperplaneComplement ℓ μ` with weights `w`. If `M ≤ w i * w j` whenever
`ℓ (b i * b j) ≠ 0`, then `M ^ (d + 2) ≤ (M * ∏ i, w i) ^ 2`, where `d` is the size of the basis. -/
theorem hyperplane_multiplication_minimum_product
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ℓ μ : K →ₗ[F] F) (hℓ : ℓ ≠ 0) (hℓ1 : ℓ 1 = 0) (hμ1 : μ 1 = 1)
    (b : Module.Basis ι F (hyperplaneComplement ℓ μ))
    (w : ι → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hw : ∀ i j, ℓ ((b i : K) * (b j : K)) ≠ 0 → M ≤ w i * w j) :
    M ^ (Fintype.card ι + 2) ≤ (M * ∏ i, w i) ^ 2 := by
  let B : LinearMap.BilinForm F (hyperplaneComplement ℓ μ) :=
    { toFun a :=
        { toFun := fun x ↦ ℓ ((a : K) * (x : K))
          map_add' := by intros; simp [mul_add]
          map_smul' := by intros; simp }
      map_add' := by intros; ext; simp [add_mul]
      map_smul' := by intros; ext; simp }
  have hl (a : hyperplaneComplement ℓ μ) (ha : ∀ x, B a x = 0) : a = 0 := by
    by_contra hn
    obtain ⟨x, hxℓ, hxμ, hax⟩ :=
      multiplication_pairing_on_hyperplane_complement ℓ μ hℓ hℓ1 hμ1
        a (fun h ↦ hn (Subtype.ext h)) a.property.1 a.property.2
    exact hax (ha ⟨x, hxℓ, hxμ⟩)
  have hdet := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp
    ⟨hl, fun x hx ↦ hl x fun a ↦ by
      simpa only [B, LinearMap.coe_mk, AddHom.coe_mk, mul_comm] using hx a⟩
  have hσ : ∃ σ : Equiv.Perm ι, ∀ i, LinearMap.BilinForm.toMatrix b B (σ i) i ≠ 0 := by
    by_contra h; push Not at h; apply hdet; rw [Matrix.det_apply]
    refine Finset.sum_eq_zero fun σ _ ↦ ?_
    obtain ⟨i, hi⟩ := h σ
    rw [Finset.prod_eq_zero (f := fun j ↦ LinearMap.BilinForm.toMatrix b B (σ j) j)
      (Finset.mem_univ i) hi, smul_zero]
  obtain ⟨σ, hσ⟩ := hσ
  have hprod : M ^ Fintype.card ι ≤ (∏ i, w i) ^ 2 := by
    calc
      M ^ Fintype.card ι = ∏ _i : ι, M := by simp
      _ ≤ ∏ i : ι, w (σ i) * w i :=
        Finset.prod_le_prod₀ (fun _ _ ↦ hM) fun i _ ↦ hw _ _
          (by simpa only [LinearMap.BilinForm.toMatrix_apply, B,
            LinearMap.coe_mk, AddHom.coe_mk] using hσ i)
      _ = (∏ i, w i) ^ 2 := by rw [Finset.prod_mul_distrib, Equiv.prod_comp, sq]
  calc
    M ^ (Fintype.card ι + 2) = M ^ Fintype.card ι * M ^ 2 := pow_add _ _ _
    _ ≤ (∏ i, w i) ^ 2 * M ^ 2 := mul_le_mul_of_nonneg_right hprod (sq_nonneg M)
    _ = (M * ∏ i, w i) ^ 2 := by ring

end
end CCDN
