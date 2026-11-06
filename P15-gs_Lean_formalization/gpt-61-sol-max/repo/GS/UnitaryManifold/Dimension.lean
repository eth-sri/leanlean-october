import GS.UnitaryManifold.CayleyModel
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

namespace GS.UnitaryManifold
/-- The standard adjoint splitting computes the dimension; no explicit coordinates are needed. -/
noncomputable def fullSkewCoordinateEquiv (q : ℕ) : Mat q ≃ₗ[ℝ] Model (fun _ : Fin q => 0) := by
  letI : FiniteDimensional ℝ (selfAdjoint (CMat q)) :=
    FiniteDimensional.of_injective (selfAdjoint.submodule ℝ (CMat q)).subtype Subtype.val_injective
  letI : FiniteDimensional ℝ (skewAdjoint (CMat q)) :=
    FiniteDimensional.of_injective (skewAdjoint.submodule ℝ (CMat q)).subtype Subtype.val_injective
  have hi : Function.Bijective (skewAdjoint.negISMul (A := CMat q)) :=
    Function.bijective_iff_has_inverse.mpr
      ⟨fun a => ⟨Complex.I • (a : CMat q), by simp⟩,
        fun a => Subtype.ext (skewAdjoint.I_smul_neg_I a),
        fun a => Subtype.ext (by simp [skewAdjoint.negISMul, smul_smul])⟩
  have he := (LinearEquiv.ofBijective _ hi).finrank_eq
  have hd := (StarModule.decomposeProdAdjoint ℝ (CMat q)).finrank_eq
  have hs : modelSpace (fun _ : Fin q => 0) = skewAdjoint.submodule ℝ (CMat q) := by
    ext A
    exact and_iff_right (fun i j h => (h rfl).elim)
  apply LinearEquiv.ofFinrankEq
  change _ = Module.finrank ℝ ↥(modelSpace (fun _ : Fin q => 0))
  rw [hs]
  change _ = Module.finrank ℝ (skewAdjoint (CMat q))
  rw [Module.finrank_prod] at hd
  simp [Mat, CMat, Module.finrank_matrix, Complex.finrank_real_complex] at he hd ⊢
  omega
end GS.UnitaryManifold
