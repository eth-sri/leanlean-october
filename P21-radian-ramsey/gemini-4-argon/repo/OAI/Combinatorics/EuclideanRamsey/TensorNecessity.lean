module

public import OAI.Combinatorics.EuclideanRamsey.Congruence

@[expose] public section

namespace OAI.EuclideanRamsey
noncomputable section
open scoped TensorProduct

abbrev RealTensor := ℝ ⊗[ℚ] ℝ
abbrev RealArray (d : ℕ) := Matrix (Option (Fin d)) (Option (Fin d)) RealTensor

def realAugmented {s d : ℕ} (a : Fin s → Space d) (i : Fin s) : Option (Fin d) → ℝ
  | none => 1
  | some j => a i j

def arrayEvaluation {s d : ℕ} (a : Fin s → Space d) (i : Fin s) :
    RealArray d →ₗ[ℚ] RealTensor where
  toFun P := ∑ α, ∑ β, (realAugmented a i α ⊗ₜ[ℚ] (1 : ℝ)) * P α β *
    ((1 : ℝ) ⊗ₜ[ℚ] realAugmented a i β)
  map_add' P Q := by simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' q P := by
    simp only [Matrix.smul_apply, RingHom.id_apply, mul_smul_comm, smul_mul_assoc, Finset.smul_sum]

def spatialMultiply {d : ℕ} : RealArray d →ₗ[ℚ] Matrix (Fin d) (Fin d) ℝ where
  toFun P α β := Algebra.TensorProduct.lmul' ℚ (P (some α) (some β))
  map_add' P Q := by ext; exact map_add (Algebra.TensorProduct.lmul' ℚ) _ _
  map_smul' q P := by ext; exact (Algebra.TensorProduct.lmul' ℚ).toLinearMap.map_smul q _

def RealCriterion {s d : ℕ} (a : Fin s → Space d) : Prop :=
  ∃ P : RealArray d, (∀ i, arrayEvaluation a i P = 0) ∧ spatialMultiply P = 1

end
end OAI.EuclideanRamsey
