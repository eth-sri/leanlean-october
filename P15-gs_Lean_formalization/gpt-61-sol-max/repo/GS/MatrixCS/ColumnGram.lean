import Mathlib.Tactic
import Mathlib.Algebra.Star.Unitary

import GS.MatrixGeometry.Base
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Spectrum



/-! # Unitary completion of matrices with real diagonal column Gram matrices

Normalized nonzero columns extend to an orthonormal basis. Zero columns are
included, so the subsequent cosine-sine theorem includes both endpoints.
-/

open Matrix InnerProductSpace GS.MatrixBase
namespace GS.MatrixCS
variable {𝕜 : Type} [RCLike 𝕜]

theorem exists_unitary_conjugation {n : ℕ} {A B : KMat 𝕜 n}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hc : A.charpoly = B.charpoly) :
    ∃ U : KMat 𝕜 n, Unitary U ∧ Uᴴ * A * U = B := by
  have he := (hA.eigenvalues_eq_eigenvalues_iff hB).mpr hc
  let S := hA.eigenvectorUnitary * star hB.eigenvectorUnitary
  refine ⟨(S : KMat 𝕜 n), S.property, ?_⟩
  have h : _root_.Unitary.conjStarAlgAut 𝕜 _ (star S) A = B := by
    
    rw [star_mul, star_star, _root_.Unitary.conjStarAlgAut_mul_apply,
      hA.conjStarAlgAut_star_eigenvectorUnitary, he, ← hB.spectral_theorem]
  simpa only [_root_.Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose] using h

/-- A square complex matrix with real diagonal Gram matrix has a unitary
left factor, including at zero diagonal entries. -/
theorem exists_unitary_mul_diagonal {n : ℕ} (A : KMat 𝕜 n) (d : Fin n → ℝ)
    (hA : Aᴴ * A = diagonal (fun i => (d i : 𝕜) ^ 2)) :
    ∃ U : KMat 𝕜 n, Unitary U ∧ A = U * diagonal (fun i => (d i : 𝕜)) := by

  let e₀ := EuclideanSpace.basisFun (Fin n) 𝕜
  let f : Fin n → EuclideanSpace 𝕜 (Fin n) := fun j => WithLp.toLp 2 (fun i => A i j)
  have hcoords (i j : Fin n) : ⟪e₀ i, f j⟫_𝕜 = A i j :=
    EuclideanSpace.basisFun_inner (Fin n) 𝕜 (f j) i
  have hgram (i j : Fin n) : ⟪f i, f j⟫_𝕜 = if i = j then (d i : 𝕜) ^ 2 else 0 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
    change (Aᴴ * A) i j = _
    rw [hA]
    simp [Matrix.diagonal_apply]
  let v : Fin n → EuclideanSpace 𝕜 (Fin n) := fun j => ((d j : 𝕜))⁻¹ • f j
  let s : Set (Fin n) := {i | d i ≠ 0}
  have hv : Orthonormal 𝕜 (s.restrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    change ⟪((d i : 𝕜))⁻¹ • f i, ((d j : 𝕜))⁻¹ • f j⟫_𝕜 = _
    rw [inner_smul_left, inner_smul_right, hgram]
    by_cases hij : i = j
    · aesop (add norm [pow_two])
    · aesop
  obtain ⟨e, he⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = Fintype.card (Fin n))
  let U := e₀.toBasis.toMatrix e
  have hU := e₀.toMatrix_orthonormalBasis_mem_unitary e
  refine ⟨U, hU, ?_⟩
  ext i j
  rw [Matrix.mul_diagonal]
  simp only [U, Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply]
  by_cases hd : d j = 0
  · have hf : f j = 0 := by
      apply (inner_self_eq_zero (𝕜 := 𝕜)).mp
      exact (hgram j j).trans (by aesop)
    rw [hd]
    simp only [RCLike.ofReal_zero, mul_zero, ← hcoords, hf, inner_zero_right]
  · have hj := hd
    
    rw [he j hj]
    
    rw [inner_smul_right, hcoords]
    have hd' : (d j : 𝕜) ≠ 0 := by exact_mod_cast hd
    field_simp

end GS.MatrixCS
