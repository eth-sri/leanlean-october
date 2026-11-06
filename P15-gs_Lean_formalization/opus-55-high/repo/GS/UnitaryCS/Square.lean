module

public import GS.UnitaryCS.Thin

@[expose] public section


/-!
# The complete complex square cosine-sine decomposition

The thin decomposition is completed using the unitary complement. No
invertibility or distinctness is imposed on the singular values.
-/

noncomputable section
open Matrix
namespace GS.UnitaryCS

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The two large blocks viewed either as a product or as a disjoint sum. -/
def twoProdSumEquiv (p : ℕ) : (Fin 2 × Fin p) ≃ (Fin p ⊕ Fin p) where
  toFun x := if x.1 = 0 then Sum.inl x.2 else Sum.inr x.2
  invFun x := Sum.elim (fun i => (0, i)) (fun i => (1, i)) x
  left_inv := by grind
  right_inv := by grind

section
variable {n : ℕ}
def split (A B : Matrix (Fin n) (Fin n) 𝕜) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) 𝕜 :=
  fromBlocks A 0 0 B

@[simp] theorem split_mul (A B C D : Matrix (Fin n) (Fin n) 𝕜) :
    split A B * split C D = split (A * C) (B * D) := by
  simp [split, Matrix.fromBlocks_multiply]

@[simp] theorem split_conjTranspose (A B : Matrix (Fin n) (Fin n) 𝕜) :
    (split A B)ᴴ = split Aᴴ Bᴴ := by simp [split, Matrix.fromBlocks_conjTranspose]

end

@[simp] theorem split_one (n : ℕ) : split (1 : Matrix (Fin n) (Fin n) 𝕜) 1 = 1 := Matrix.fromBlocks_one

section
variable {n : ℕ}
theorem split_unitary {A B : Matrix (Fin n) (Fin n) 𝕜}
    (hA : IsUnitary A) (hB : IsUnitary B) : IsUnitary (split A B) := by
  constructor <;> simp [hA.1, hA.2, hB.1, hB.2]

/-- Canonical CS matrix, with the upper-right sine block negative. -/
def csMatrix (c s : Fin n → ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) 𝕜 :=
  fromBlocks (diagonal (fun i => (c i : 𝕜))) (-diagonal (fun i => (s i : 𝕜))) (diagonal (fun i => (s i : 𝕜))) (diagonal (fun i => (c i : 𝕜)))

theorem csMatrix_unitary (c s : Fin n → ℝ)
    (h : ∀ i, c i ^ 2 + s i ^ 2 = 1) : IsUnitary (csMatrix (𝕜 := 𝕜) c s) := by
  refine .of_conjTranspose_mul ?_
  simp [csMatrix, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one, diagonal_mul_diagonal, funext_iff]
  and_intros <;> intro i <;> norm_cast <;> first | grind

/-- Every square complex unitary matrix has a complete cosine-sine
decomposition into two unitary blocks on each side and a canonical CS
matrix in the middle. The result includes all degenerate singular values. -/
theorem exists_square_cs (Q : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) 𝕜) (hQ : IsUnitary Q) :
    ∃ (U₁ U₂ V₁ V₂ : Matrix (Fin n) (Fin n) 𝕜) (c s : Fin n → ℝ),
      IsUnitary U₁ ∧ IsUnitary U₂ ∧ IsUnitary V₁ ∧ IsUnitary V₂ ∧
      (∀ i, 0 ≤ c i ∧ 0 ≤ s i ∧ c i ^ 2 + s i ^ 2 = 1) ∧
      Q = split U₁ U₂ * csMatrix c s * split V₁ V₂ := by
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, Q = fromBlocks A B C D := by aesop
  have h1 := hQ.1
  simp only [fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at h1
  obtain ⟨U₁, U₂, V, c, s, hU₁, hU₂, hV, hcs, he₁, he₂⟩ := exists_thin_cs A C h1.1
  have hX : diagonal (fun i => (c i : 𝕜)) * (U₁ᴴ * B) + diagonal (fun i => (s i : 𝕜)) * (U₂ᴴ * D) = 0 := by
    have h₁ := congrArg conjTranspose he₁
    have h₂ := congrArg conjTranspose he₂
    simp [Pi.star_def] at h₁ h₂
    rw [← Matrix.mul_assoc, ← h₁, ← Matrix.mul_assoc, ← h₂, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_add, h1.2.1, Matrix.mul_zero]
  have hK := csMatrix_unitary (𝕜 := 𝕜) c s (by grind)
  have hH : (csMatrix c s)ᴴ * ((split U₁ U₂)ᴴ * fromBlocks A B C D * split V 1) =
      split 1 (-diagonal (fun i => (s i : 𝕜)) * (U₁ᴴ * B) + diagonal (fun i => (c i : 𝕜)) * (U₂ᴴ * D)) := by
    simp [split, csMatrix, fromBlocks_conjTranspose, fromBlocks_multiply, Matrix.mul_assoc, he₁, he₂, ← Matrix.mul_assoc U₁ᴴ U₁, ← Matrix.mul_assoc U₂ᴴ U₂, hU₁.1, hU₂.1, hX, funext_iff, Pi.star_def]
    all_goals norm_cast; grind
  have hW := hK.conjTranspose.mul (((split_unitary hU₁ hU₂).conjTranspose.mul hQ).mul (split_unitary hV .one))
  rw [hH] at hW
  have hW' : IsUnitary (-diagonal (fun i => (s i : 𝕜)) * (U₁ᴴ * B) + diagonal (fun i => (c i : 𝕜)) * (U₂ᴴ * D)) := by
    constructor <;> [have := hW.1; have := hW.2] <;> simpa [split, fromBlocks_conjTranspose, fromBlocks_multiply, ← fromBlocks_one] using this
  refine ⟨U₁, U₂, Vᴴ, _, c, s, hU₁, hU₂, hV.conjTranspose, hW', hcs, ?_⟩
  rw [show ∀ W, split Vᴴ W = split 1 W * (split V 1)ᴴ by simp, ← hH]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc _ _ (csMatrix c s)ᴴ, hK.2, Matrix.mul_one, (split_unitary hU₁ hU₂).2, Matrix.one_mul,
    Matrix.mul_assoc, (split_unitary hV .one).2, Matrix.mul_one]

end

end GS.UnitaryCS
