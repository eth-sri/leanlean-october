
import GS.MatrixCS.ColumnGram
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Sqrt



/-! # Complex thin cosine-sine decomposition via the Hermitian spectral theorem -/

open Matrix GS.MatrixBase
open scoped ComplexOrder
namespace GS.MatrixCS
variable {𝕜 : Type} [RCLike 𝕜]

theorem gram_diagonal_nonneg {n : ℕ} (A : KMat 𝕜 n) (d : Fin n → ℝ)
    (h : Aᴴ * A = diagonal (fun i => (d i : 𝕜))) (i : Fin n) : 0 ≤ d i := by
  have hp := Matrix.posSemidef_conjTranspose_mul_self A
  rw [h] at hp
  simpa using (Matrix.posSemidef_diagonal_iff.mp hp) i

/-- Simultaneous unitary reduction of two square blocks with orthonormal
stacked columns, including repeated eigenvalues and zero columns. -/
theorem exists_thin_cs {n : ℕ} (A B : KMat 𝕜 n)
    (h : Aᴴ * A + Bᴴ * B = 1) :
    ∃ (U₁ U₂ V : KMat 𝕜 n) (c s : Fin n → ℝ),
      Unitary U₁ ∧ Unitary U₂ ∧ Unitary V ∧
      (∀ i, 0 ≤ c i ∧ 0 ≤ s i ∧ c i ^ 2 + s i ^ 2 = 1) ∧
      A * V = U₁ * diagonal (fun i => (c i : 𝕜)) ∧
      B * V = U₂ * diagonal (fun i => (s i : 𝕜)) := by
  have hH := Matrix.isHermitian_conjTranspose_mul_self A
  let V : KMat 𝕜 n := hH.eigenvectorUnitary
  let d := hH.eigenvalues
  have hV : Unitary V := hH.eigenvectorUnitary.property
  have hAV : (A * V)ᴴ * (A * V) = diagonal (fun i => (d i : 𝕜)) := by
    simpa [Function.comp_def, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial, V, d, Matrix.conjTranspose_mul, Matrix.mul_assoc] using
      hH.conjStarAlgAut_star_eigenvectorUnitary
  have hsum : (A * V)ᴴ * (A * V) + (B * V)ᴴ * (B * V) = 1 := by
    calc
      _ = Vᴴ * (Aᴴ * A + Bᴴ * B) * V := by
        simp [Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 1 := by rw [h, Matrix.mul_one, hV.1]
  have hBV : (B * V)ᴴ * (B * V) = diagonal (fun i => ((1 - d i : ℝ) : 𝕜)) := by
    rw [hAV] at hsum
    simpa only [← Matrix.diagonal_one, ← Matrix.diagonal_sub, Pi.sub_apply,
      RCLike.ofReal_sub, RCLike.ofReal_one] using eq_sub_of_add_eq' hsum
  let c : Fin n → ℝ := fun i => Real.sqrt (d i)
  let s : Fin n → ℝ := fun i => Real.sqrt (1 - d i)
  have hc (i) := Real.sq_sqrt (gram_diagonal_nonneg _ _ hAV i)
  have hs (i) := Real.sq_sqrt (gram_diagonal_nonneg _ _ hBV i)
  have hcC (i) : (c i : 𝕜) ^ 2 = (d i : 𝕜) := by exact_mod_cast hc i
  have hsC (i) : (s i : 𝕜) ^ 2 = ((1-d i : ℝ) : 𝕜) := by exact_mod_cast hs i
  obtain ⟨U₁, hU₁, he₁⟩ := exists_unitary_mul_diagonal (A * V) c (by aesop)
  obtain ⟨U₂, hU₂, he₂⟩ := exists_unitary_mul_diagonal (B * V) s (by aesop)
  refine ⟨U₁, U₂, V, c, s, hU₁, hU₂, hV, ?_, he₁, he₂⟩
  intro i
  exact ⟨Real.sqrt_nonneg _, Real.sqrt_nonneg _, by aesop⟩

end GS.MatrixCS
