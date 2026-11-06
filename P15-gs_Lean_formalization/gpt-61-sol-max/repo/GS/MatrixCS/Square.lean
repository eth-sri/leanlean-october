
import GS.MatrixCS.Thin




/-!
# The complete complex square cosine-sine decomposition

The thin decomposition is completed using the unitary complement. No
invertibility or distinctness is imposed on the singular values.
-/

open Matrix GS.MatrixBase
namespace GS.MatrixCS
abbrev SumMat (𝕜 : Type) (n : ℕ) := Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) 𝕜
variable {𝕜 : Type} [RCLike 𝕜]




variable (A B C D : KMat 𝕜 n)

def split  : SumMat 𝕜 n :=
  fromBlocks A 0 0 B

@[simp] theorem split_mul  :
    split A B * split C D = split (A * C) (B * D) := by
  simp [split, Matrix.fromBlocks_multiply]

@[simp] theorem split_conjTranspose  :
    (split A B)ᴴ = split Aᴴ Bᴴ := by simp [split, Matrix.fromBlocks_conjTranspose]

variable (c s : Fin n → ℝ)

@[simp] theorem split_one (n : ℕ) : split (1 : KMat 𝕜 n) 1 = 1 := Matrix.fromBlocks_one

theorem split_unitary {A B : KMat 𝕜 n}
    (hA : Unitary A) (hB : Unitary B) : Unitary (split A B) := by
  constructor <;> simp [hA.1, hA.2, hB.1, hB.2]

/-- Canonical CS matrix, with the upper-right sine block negative. -/
def csMatrix  :
    SumMat 𝕜 n :=
  fromBlocks (diagonal (fun i => (c i : 𝕜))) (-diagonal (fun i => (s i : 𝕜))) (diagonal (fun i => (s i : 𝕜))) (diagonal (fun i => (c i : 𝕜)))

theorem csMatrix_unitary 
    (h : ∀ i, c i ^ 2 + s i ^ 2 = 1) : Unitary (csMatrix (𝕜 := 𝕜) c s) := by
  apply Unitary.of_conjTranspose_mul
  rw [csMatrix, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one]
  apply Matrix.fromBlocks_inj.mpr
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> by_cases hij : i = j
  all_goals simp [Matrix.diagonal_conjTranspose, 
    Matrix.diagonal_mul_diagonal,  
     Matrix.one_apply, hij]
  all_goals try ring1
  all_goals
    have hc : (c j : 𝕜)^2 + (s j : 𝕜)^2 = 1 := by exact_mod_cast h j
    linear_combination hc

/-- Every square complex unitary matrix has a complete cosine-sine
decomposition into two unitary blocks on each side and a canonical CS
matrix in the middle. The result includes all degenerate singular values. -/
theorem exists_square_cs (Q : SumMat 𝕜 n) (hQ : Unitary Q) :
    ∃ (U₁ U₂ V₁ V₂ : KMat 𝕜 n) (c s : Fin n → ℝ),
      Unitary U₁ ∧ Unitary U₂ ∧ Unitary V₁ ∧ Unitary V₂ ∧
      (∀ i, 0 ≤ c i ∧ 0 ≤ s i ∧ c i ^ 2 + s i ^ 2 = 1) ∧
      Q = split U₁ U₂ * csMatrix c s * split V₁ V₂ := by
  let A := Q.toBlocks₁₁
  let B := Q.toBlocks₁₂
  let C := Q.toBlocks₂₁
  let D := Q.toBlocks₂₂
  have hblocks : Q = fromBlocks A B C D := (Matrix.fromBlocks_toBlocks Q).symm
  have hfirst : Aᴴ * A + Cᴴ * C = 1 := by
    have hh := congrArg Matrix.toBlocks₁₁ hQ.1
    simpa [hblocks, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one] using hh
  obtain ⟨U₁, U₂, V, c, s, hU₁, hU₂, hV, hcs, he₁, he₂⟩ :=
    exists_thin_cs A C hfirst
  let L := split U₁ U₂
  let T := split V (1 : KMat 𝕜 n)
  let K : SumMat 𝕜 n := csMatrix c s
  let E := U₁ᴴ * B
  let F := U₂ᴴ * D
  let R := fromBlocks (diagonal (fun i => (c i : 𝕜))) E (diagonal (fun i => (s i : 𝕜))) F
  have hL : Unitary L := split_unitary hU₁ hU₂
  have hT : Unitary T := split_unitary hV Unitary.one
  have hK : Unitary K := csMatrix_unitary c s (fun i => (hcs i).2.2)
  have hleft₁ : U₁ᴴ * (A * V) = diagonal (fun i => (c i : 𝕜)) := by
    rw [he₁, ← Matrix.mul_assoc, hU₁.1, Matrix.one_mul]
  have hleft₂ : U₂ᴴ * (C * V) = diagonal (fun i => (s i : 𝕜)) := by
    rw [he₂, ← Matrix.mul_assoc, hU₂.1, Matrix.one_mul]
  have hR : R = Lᴴ * Q * T := by
    rw [hblocks]
    simp [R, L, T, split, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply, Matrix.mul_assoc, hleft₁, hleft₂, E, F]
  have hRo : Unitary R := by rw [hR]; exact (hL.conjTranspose.mul hQ).mul hT
  let H := Kᴴ * R
  have hHo : Unitary H := hK.conjTranspose.mul hRo
  let X := diagonal (fun i => (c i : 𝕜)) * E + diagonal (fun i => (s i : 𝕜)) * F
  let W := -diagonal (fun i => (s i : 𝕜)) * E + diagonal (fun i => (c i : 𝕜)) * F
  have hH : H = fromBlocks 1 X 0 W := by
    have hk := hK.1
    dsimp [K, csMatrix] at hk
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      ← Matrix.fromBlocks_one] at hk
    dsimp [H, K, R, csMatrix, X, W]
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    apply Matrix.fromBlocks_inj.mpr
    exact ⟨(Matrix.fromBlocks_inj.mp hk).1, by bound,
      (Matrix.fromBlocks_inj.mp hk).2.2.1, by bound⟩
  have hh := hHo.1
  simp [hH, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    ← Matrix.fromBlocks_one] at hh
  have hH' : H = split 1 W := by simp_all [split]
  have hW : Unitary W := Unitary.of_conjTranspose_mul
    (by grind)
  have hKR : R = K * split 1 W := by
    rw [← hH']
    
    rw [← Matrix.mul_assoc, hK.2, Matrix.one_mul]
  refine ⟨U₁, U₂, Vᴴ, W, c, s, hU₁, hU₂, GS.MatrixBase.Unitary.conjTranspose hV, hW, hcs, ?_⟩
  calc
    Q = L * R * Tᴴ := by
      simp only [hR, Matrix.mul_assoc, ← Matrix.mul_assoc L Lᴴ,
         hL.2, hT.2, Matrix.one_mul, Matrix.mul_one]
    _ = L * K * (split (1 : KMat 𝕜 n) W * Tᴴ) := by grind
    _ = _ := by simp [T, L, K]

end GS.MatrixCS
