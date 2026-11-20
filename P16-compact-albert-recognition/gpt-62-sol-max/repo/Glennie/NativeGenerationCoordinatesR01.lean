/- Coordinate bridge toward native unital generation.
This module does not assume full generation or classification. -/
module

public import Glennie.Sector

@[expose] public section
namespace Glennie.NativeGenerationCoordinatesR01
noncomputable section

/-- A division-free spectral projector numerator. This uses powers under the
native Jordan operation, so membership follows from native product closure. -/
theorem diagonal_projector_first_numerator (a b c : ℝ) :
    jordan (diagonalAlbert a b c) (diagonalAlbert a b c) -
      (b + c) • diagonalAlbert a b c + (b * c) • (1 : Albert) =
      ((a - b) * (a - c)) • diagonalAlbert 1 0 0 := by
  apply Albert.ext
  all_goals simp [diagonalAlbert, unit, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octDot, octRe, octMul, octConj]
  all_goals ring

/-- Distinctness of the first eigenvalue puts its coordinate idempotent in
any unital real submodule closed under the native Jordan product. -/
theorem diagonal_projector_first_mem
    (K : Submodule ℝ Albert)
    (h1 : (1 : Albert) ∈ K)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (a b c : ℝ) (hx : diagonalAlbert a b c ∈ K)
    (hab : a - b ≠ 0) (hac : a - c ≠ 0) :
    diagonalAlbert 1 0 0 ∈ K := by
  have hn : jordan (diagonalAlbert a b c) (diagonalAlbert a b c) -
      (b + c) • diagonalAlbert a b c + (b * c) • (1 : Albert) ∈ K :=
    K.add_mem (K.sub_mem (hJ _ hx _ hx) (K.smul_mem _ hx))
      (K.smul_mem _ h1)
  rw [diagonal_projector_first_numerator] at hn
  have hp := K.smul_mem (((a - b) * (a - c))⁻¹) hn
  simpa only [smul_smul, inv_mul_cancel₀ (mul_ne_zero hab hac), one_smul] using hp

/-- Once two coordinate idempotents belong to K, the off-diagonal
Peirce component is obtained by a native Jordan polynomial. -/
theorem peirce01_extract (z : Albert) :
    (4 : ℝ) • jordan (diagonalAlbert 1 0 0)
      (jordan (diagonalAlbert 0 1 0) z) =
      (⟨0, 0, 0, z.o01, 0, 0⟩ : Albert) := by
  apply Albert.ext
  all_goals norm_num [diagonalAlbert, jordan_d0, jordan_d1, jordan_d2,
    jordan_o01, jordan_o02, jordan_o12, octDot, octRe, octMul, octConj,
    smul_smul]
  all_goals apply Prod.ext <;> apply Quaternion.ext <;> norm_num

/-- This membership conclusion requires no spectral or generation axiom. -/
theorem peirce01_mem (K : Submodule ℝ Albert)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (h0 : diagonalAlbert 1 0 0 ∈ K)
    (h1 : diagonalAlbert 0 1 0 ∈ K)
    (z : Albert) (hz : z ∈ K) :
    (⟨0, 0, 0, z.o01, 0, 0⟩ : Albert) ∈ K := by
  rw [← peirce01_extract]
  exact K.smul_mem 4 (hJ _ h0 _ (hJ _ h1 _ hz))

end
end Glennie.NativeGenerationCoordinatesR01
