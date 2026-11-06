/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/TensorPresentation.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`); subsequently
refactored and proof-compressed while preserving the main results.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.AdicLifting

public import Mathlib.Algebra.Module.LocalizedModule.Int

public import Mathlib.RingTheory.Flat.Basic

@[expose] public section

namespace OAI.EuclideanRamsey









open scoped TensorProduct
lemma spatialMultiply_comm {d : ℕ} (T : AffineVector d ⊗[ℚ] AffineVector d) :
    spatialMultiply (affineArray (TensorProduct.comm ℚ _ _ T)) =
      (spatialMultiply (affineArray T)).transpose := by
  ext α β
  induction T using TensorProduct.inductionOn <;> simp_all
  exact mul_comm _ _



theorem exists_symmetric_tensor_presentation {W : Type*} [AddCommGroup W] [Module ℚ W]
    (T : W ⊗[ℚ] W) :
    ∃ (k : ℕ) (w : Fin k → W) (C : Matrix (Fin k) (Fin k) ℚ), C.IsSymm ∧
      (∑ j,∑ l,C j l • (w j ⊗ₜ[ℚ] w l)) =
        (1/2:ℚ) • (T + TensorProduct.comm ℚ W W T) := by
  classical
  obtain ⟨S,hS⟩ := TensorProduct.exists_finset T
  let w (j : ↥S × Bool) := if j.2 then j.1.val.2 else j.1.val.1
  let C (i j : ↥S × Bool) : ℚ := if i.1 = j.1 ∧ i.2 ≠ j.2 then 1/2 else 0
  have hC : Matrix.IsSymm C := by
    ext i j
    change C j i = C i j
    simp [C,eq_comm,and_comm]
  have hs : (∑ i,∑ j,C i j • (w i ⊗ₜ[ℚ] w j)) =
      (1/2:ℚ) • (T + TensorProduct.comm ℚ W W T) := by
    rw [hS]
    simp [C,w,Fintype.sum_prod_type,smul_add,Finset.smul_sum,
      TensorProduct.comm_tmul,← Finset.sum_coe_sort S,← Finset.sum_add_distrib,add_comm]
  let e := Fintype.equivFin (↥S × Bool)
  refine ⟨_,w ∘ e.symm,
    Matrix.reindex e e C,hC.submatrix _,?_⟩
  rw [← hs]
  exact Fintype.sum_equiv e.symm _ _ (fun i => e.symm.sum_comp (fun j => C (e.symm i) j • (w (e.symm i) ⊗ₜ[ℚ] w j)))






lemma rational_lattice_kernel {k : ℕ} (f : RationalSpace k →ₗ[ℚ] ℝ) :
    latticeSpan (AddMonoidHom.ker (f.toAddMonoidHom.comp rationalize)) = f.ker := by
  let g : Lattice k →ₗ[ℤ] RationalSpace k :=
    LinearMap.pi fun j => (Algebra.linearMap ℤ ℚ).comp (LinearMap.proj j)
  have h := (Submodule.localized'gi ℚ (nonZeroDivisors ℤ) g).l_u_eq f.ker
  rw [Submodule.localized'_eq_span] at h
  exact h


lemma quotientTensor_zero_of_evaluation {k : ℕ} (f : RationalSpace k →ₗ[ℚ] ℝ)
    (T : RationalSpace k ⊗[ℚ] RationalSpace k) (hT : TensorProduct.map f f T = 0) :
    quotientTensor (AddMonoidHom.ker (f.toAddMonoidHom.comp rationalize)) T = 0 := by
  change TensorProduct.map _ _ T = 0
  rw [rational_lattice_kernel]
  let j := f.ker.liftQ f le_rfl
  have hj  := LinearMap.ker_eq_bot.mp
    (Submodule.ker_liftQ_eq_bot' f.ker f rfl)
  apply (TensorProduct.map_injective_of_flat_flat j j hj hj)
  simpa [← LinearMap.comp_apply, ← TensorProduct.map_comp, j] using hT



lemma matrixTensor_map_family {k : ℕ} {W : Type*} [AddCommGroup W] [Module ℚ W]
    (w : Fin k → W) (C : Matrix (Fin k) (Fin k) ℚ) :
    TensorProduct.map (Fintype.linearCombination ℚ w) (Fintype.linearCombination ℚ w) (matrixTensor C) =
      ∑ j,∑ l,C j l • (w j ⊗ₜ[ℚ] w l) := by
  simp_all [matrixTensor]


end OAI.EuclideanRamsey
