module

public import GS.UnitaryCS.ColumnGram
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section


/-! # Thin cosine-sine decomposition via the Hermitian spectral theorem -/

noncomputable section
open Matrix
open scoped ComplexOrder
namespace GS.UnitaryCS

variable {𝕜 : Type*} [RCLike 𝕜]

section
variable {n : ℕ}
theorem gram_diagonal_nonneg (A : Matrix (Fin n) (Fin n) 𝕜) (d : Fin n → ℝ)
    (h : Aᴴ * A = diagonal (fun i => (d i : 𝕜))) (i : Fin n) : 0 ≤ d i := by
  simpa [h] using (posSemidef_conjTranspose_mul_self A).diag_nonneg (i := i)

/-- Simultaneous unitary reduction of two square blocks with orthonormal
stacked columns, including repeated eigenvalues and zero columns. -/
theorem exists_thin_cs (A B : Matrix (Fin n) (Fin n) 𝕜)
    (h : Aᴴ * A + Bᴴ * B = 1) :
    ∃ (U₁ U₂ V : Matrix (Fin n) (Fin n) 𝕜) (c s : Fin n → ℝ),
      IsUnitary U₁ ∧ IsUnitary U₂ ∧ IsUnitary V ∧
      (∀ i, 0 ≤ c i ∧ 0 ≤ s i ∧ c i ^ 2 + s i ^ 2 = 1) ∧
      A * V = U₁ * diagonal (fun i => (c i : 𝕜)) ∧
      B * V = U₂ * diagonal (fun i => (s i : 𝕜)) := by
  have hH : (Aᴴ * A).IsHermitian := isHermitian_conjTranspose_mul_self A
  let V : Matrix (Fin n) (Fin n) 𝕜 := hH.eigenvectorUnitary
  let d := hH.eigenvalues
  have hV : IsUnitary V := IsUnitary.of_conjTranspose_mul <| by
    simpa only [V, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hAV : (A * V)ᴴ * (A * V) = diagonal (fun i => (d i : 𝕜)) := by
    simpa [Function.comp_def, Unitary.conjStarAlgAut_star_apply, Matrix.star_eq_conjTranspose, V, d,
      Matrix.conjTranspose_mul, Matrix.mul_assoc] using hH.conjStarAlgAut_star_eigenvectorUnitary
  have hBV : (B * V)ᴴ * (B * V) = diagonal (fun i => ((1 - d i : ℝ) : 𝕜)) := by
    have : (A * V)ᴴ * (A * V) + (B * V)ᴴ * (B * V) = Vᴴ * (Aᴴ * A + Bᴴ * B) * V := by
      simp [Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    rw [h, Matrix.mul_one, hV.1, hAV] at this
    rw [eq_sub_of_add_eq' this]
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hc i := Real.sq_sqrt (gram_diagonal_nonneg _ _ hAV i)
  have hs i := Real.sq_sqrt (gram_diagonal_nonneg _ _ hBV i)
  obtain ⟨U₁, hU₁, he₁⟩ := exists_unitary_mul_diagonal (A * V) (fun i => √(d i))
    (hAV.trans (by grind))
  obtain ⟨U₂, hU₂, he₂⟩ := exists_unitary_mul_diagonal (B * V) (fun i => √(1 - d i))
    (hBV.trans (by grind))
  refine ⟨U₁, U₂, V, _, _, hU₁, hU₂, hV, fun i => ⟨Real.sqrt_nonneg _, Real.sqrt_nonneg _, ?_⟩, he₁, he₂⟩
  grind

end

end GS.UnitaryCS
