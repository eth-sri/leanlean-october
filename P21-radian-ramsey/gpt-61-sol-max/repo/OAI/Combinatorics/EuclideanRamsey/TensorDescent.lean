/-
From openai/math (https://github.com/openai/math), commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, lean/OAI/Combinatorics/EuclideanRamsey/TensorDescent.lean;
licensed under the Apache License, Version 2.0 (see LICENSES/Apache-2.0.txt and NOTICE).
Modified: ported to the Lean module system for Lean v4.35.0-rc2 / Mathlib v4.35.0-rc2 (this
notice, a `module` header, `public import`, `@[expose] public section`); subsequently
refactored and proof-compressed while preserving the main results.
-/
module

public import OAI.Combinatorics.EuclideanRamsey.TensorNecessity

@[expose] public section

namespace OAI.EuclideanRamsey


noncomputable section

open scoped TensorProduct

variable (F : IntermediateField ℚ ℝ) {ι : Type*} (b : Module.Basis ι F ℝ)

def tensorCoordinates : (ℝ ⊗[ℚ] ℝ) ≃ₗ[ℚ] (ι × ι →₀ (F ⊗[ℚ] F)) :=
  (TensorProduct.congr (b.repr.restrictScalars ℚ) (b.repr.restrictScalars ℚ)).trans
    (finsuppTensorFinsupp ℚ ℚ F F ι ι)

lemma repr_mul (x : F) (u : ℝ) :
    b.repr ((x : ℝ) * u) = x • b.repr u := by
  simpa [Algebra.smul_def] using b.repr.map_smul x u

lemma tensorCoordinates_sandwich (x y : F) (T : ℝ ⊗[ℚ] ℝ) :
    tensorCoordinates F b (((x : ℝ) ⊗ₜ[ℚ] (1 : ℝ)) * T *
      ((1 : ℝ) ⊗ₜ[ℚ] (y : ℝ))) =
      (x ⊗ₜ[ℚ] y) • tensorCoordinates F b T := by
  ext ⟨i,j⟩
  induction T using TensorProduct.inductionOn <;>
    simp_all [tensorCoordinates, repr_mul, mul_comm _ (y : ℝ), mul_add, add_mul,
      Finsupp.add_apply, Finsupp.smul_apply]



end

end OAI.EuclideanRamsey
