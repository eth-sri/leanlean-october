/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/TensorPresentation.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system and shortened.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.AdicLifting

@[expose] public section

noncomputable section

open scoped TensorProduct

set_option autoImplicit true
namespace OAI.EuclideanRamsey
set_option hygiene false
local notation "𝔞" => (1 : 𝕄 d ℝ)

variable (a : Fin s → Space d)
abbrev AffineVector d := Option (Fin d) → ℝ

def affineArray : (AffineVector d ⊗[ℚ] AffineVector d) ≃ₗ[ℚ] RealArray d :=
  (TensorProduct.piLeft ℚ (AffineVector d) fun _ => ℝ).trans (LinearEquiv.piCongrRight fun _ => TensorProduct.piRight ℚ ℚ ℝ _)

def rowEvaluation (i : Fin s) : AffineVector d →ₗ[ℚ] ℝ :=
  (Fintype.linearCombination ℝ (realAugmented a i)).restrictScalars ℚ

theorem realCriterion_lattice (h : RealCriterion a) :
    ∃ (k : ℕ) (w : Fin k → AffineVector d) (C : 𝕄 k ℚ), C.IsSymm ∧
      Matrix.of (fun α j => w j (some α)) * C.map (Rat.cast : ℚ → ℝ) * (Matrix.of fun α j => w j (some α)).transpose = 1 ∧
      ∀ i,quotientTensor
        (AddMonoidHom.ker (((rowEvaluation a i).comp (Fintype.linearCombination ℚ w)).toAddMonoidHom.comp rationalize))
        (matrixTensor C) = 0 := by
  obtain ⟨P, hP, hG⟩ := h
  obtain ⟨S, hS⟩ := TensorProduct.exists_finset (affineArray.symm P)
  obtain ⟨k, w, hw⟩ := ((S.finite_toSet.image Prod.fst).union (S.finite_toSet.image Prod.snd)).fin_embedding
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp (show affineArray.symm P ∈
      Submodule.span ℚ (Set.range fun p : Fin k × Fin k => w p.1 ⊗ₜ[ℚ] w p.2) from
    hS ▸ Submodule.sum_mem _ fun x hx => Submodule.subset_span (by
      obtain ⟨j, hj⟩ : x.1 ∈ Set.range w := hw ▸ Or.inl ⟨x, hx, rfl⟩
      obtain ⟨l, hl⟩ : x.2 ∈ Set.range w := hw ▸ Or.inr ⟨x, hx, rfl⟩
      exact ⟨(j, l), by grind⟩))
  rw [Fintype.sum_prod_type, LinearEquiv.eq_symm_apply] at hc
  subst hc
  have ht (w z : AffineVector d) α β : affineArray (w ⊗ₜ[ℚ] z) α β = w α ⊗ₜ[ℚ] z β := rfl
  refine ⟨k, ⇑w, Matrix.of fun j l => (c (j, l) + c (l, j)) / 2, Matrix.IsSymm.ext fun j l => by simp [add_comm], ?_, fun i => ?_⟩
  · have hs (x z : AffineVector d) α β : spatialMultiply (affineArray (x ⊗ₜ[ℚ] z)) α β = x (some α) * z (some β) :=
      Algebra.TensorProduct.lmul'_apply_tmul _ _
    ext α β
    have h1 := congrFun₂ hG α β
    have h2 := congrFun₂ hG β α
    simp only [map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, hs, Rat.smul_def] at h1 h2
    rw [Finset.sum_comm] at h1
    rw [show 𝔞 α β = (𝔞 β α + 𝔞 α β) / 2 by simp [Matrix.one_apply, eq_comm], ← h1, ← h2,
      ← Finset.sum_add_distrib, Finset.sum_div]
    simp only [Matrix.mul_apply, Finset.sum_mul, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    simp
    ring
  · have hr x z : arrayEvaluation a i (affineArray (x ⊗ₜ[ℚ] z)) = rowEvaluation a i x ⊗ₜ rowEvaluation a i z := by
      simp [arrayEvaluation, rowEvaluation, ht, Fintype.linearCombination_apply, TensorProduct.sum_tmul, TensorProduct.tmul_sum, mul_comm, TensorProduct.add_tmul, TensorProduct.tmul_add, Finset.sum_add_distrib]
      exact Finset.sum_comm
    have hX := hP i
    simp only [map_sum, map_smul, hr] at hX
    set f := (rowEvaluation a i).comp (Fintype.linearCombination ℚ w)
    have hL : latticeSpan (f.toAddMonoidHom.comp rationalize).ker = LinearMap.ker f := by
      refine le_antisymm (Submodule.span_le.mpr ?_) fun x hx => ?_
      · rintro _ ⟨γ, hγ, rfl⟩
        exact hγ
      · let A : Matrix Unit (Fin k) ℚ := Matrix.of fun _ j => x j
        have hd : (A.den:ℚ) ≠ 0 := mod_cast A.den_ne_zero
        have he : rationalize (fun j => A.num () j) = (A.den:ℚ) • x := by
          ext j
          have := A.num_div_den () j
          simp [rationalize, A] at this ⊢
          rw [← this, mul_div_cancel₀ _ hd]
        simpa [ hd] using (latticeSpan _).smul_mem (A.den:ℚ)⁻¹
          (Submodule.subset_span ⟨_, by simp_all, he⟩)
    have hi := LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ f hL.le hL.ge)
    refine TensorProduct.map_injective_of_flat_flat _ _ hi hi ?_
    rw [map_zero, quotientTensor, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
    have hX' := congrArg (TensorProduct.comm ℚ ℝ ℝ) hX
    simp only [map_sum, map_smul, TensorProduct.comm_tmul, map_zero] at hX'
    rw [Finset.sum_comm] at hX'
    simp [matrixTensor, f, add_smul, Finset.sum_add_distrib, div_eq_inv_mul, mul_smul, ← Finset.smul_sum, hX, hX']
