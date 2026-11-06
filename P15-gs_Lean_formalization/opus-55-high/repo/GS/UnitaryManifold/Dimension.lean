module

public import GS.UnitaryManifold.CayleyCharts
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section


/-!
# The real dimension of the full unitary Cayley model

An explicit real-linear coordinate equivalence identifies skew-Hermitian
q-by-q matrices with arbitrary real q-by-q matrices. Above the diagonal we
store real parts; on and below the diagonal we store imaginary parts. In
particular the imaginary diagonal contributes q independent real dimensions.
-/
noncomputable section
namespace GS.UnitaryManifold
/-- The full supported skew-Hermitian model is a real vector space of q² coordinates.
Above the diagonal we store real parts; on and below it imaginary parts. -/
def fullSkewCoordinateEquiv (q : ℕ) : Mat q ≃ₗ[ℝ] Model (fun _ : Fin q => 0) where
  toFun R := ⟨.of fun i j => ⟨if i < j then R i j else if j < i then -R j i else 0, if i < j then R j i else R i j⟩,
    by tauto, by ext i j <;> simp [Complex.ext_iff] <;> grind⟩
  invFun A i j := if i < j then (A.1 i j).re else (A.1 i j).im
  left_inv R := by ext i j; by_cases hij : i < j <;> simp [hij]
  right_inv A := by ext i j <;> have := congrFun₂ A.2.2 i j <;> simp [Complex.ext_iff] at this ⊢ <;> grind
  map_add' R S := by ext i j <;> simp [Complex.ext_iff] <;> grind
  map_smul' r R := by ext i j; simp [Complex.ext_iff]

theorem finrank_fullModel (q : ℕ) :
    Module.finrank ℝ (Model (fun _ : Fin q => 0)) = q * q := by
  rw [← (fullSkewCoordinateEquiv q).finrank_eq]
  simp [Mat, Module.finrank_matrix]

end GS.UnitaryManifold
