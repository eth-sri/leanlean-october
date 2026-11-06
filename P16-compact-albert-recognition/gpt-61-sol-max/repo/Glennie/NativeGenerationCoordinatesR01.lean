/- Coordinate bridge toward native unital generation.
This module does not assume full generation or classification. -/
module
public import Glennie.Native.CoordinateSimp

public import Glennie.Sector

@[expose] public section
namespace Glennie.NativeGenerationCoordinatesR01
section



/-- Distinctness of the first eigenvalue puts its coordinate idempotent in
any unital real submodule closed under the native Jordan product. -/
theorem diagonal_projector_first_mem
    (K : Submodule ℝ Albert)
    (h1 : (1 : Albert) ∈ K)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (a b c : ℝ) (hx : diagonalAlbert a b c ∈ K)
    (hab : a - b ≠ 0) (hac : a - c ≠ 0) :
    diagonalAlbert 1 0 0 ∈ K := by
  apply (K.smul_mem_iff (mul_ne_zero hab hac)).mp
  convert K.add_mem (K.sub_mem (hJ _ hx _ hx) (K.smul_mem (b + c) hx))
    (K.smul_mem (b * c) h1) using 1
  ext <;> simp [albert_coords, diagonalAlbert, octDot] <;> ring



/-- This membership conclusion requires no spectral or generation axiom. -/
theorem peirce01_mem (K : Submodule ℝ Albert)
    (hJ : ∀ p ∈ K, ∀ q ∈ K, jordan p q ∈ K)
    (h0 : diagonalAlbert 1 0 0 ∈ K)
    (h1 : diagonalAlbert 0 1 0 ∈ K)
    (z : Albert) (hz : z ∈ K) :
    (⟨0, 0, 0, z.o01, 0, 0⟩ : Albert) ∈ K := by
  convert K.smul_mem 4 (hJ _ h0 _ (hJ _ h1 _ hz)) using 1
  apply Albert.ext
  all_goals norm_num [albert_coords, diagonalAlbert, octDot, smul_smul]
  all_goals apply Prod.ext <;> apply Quaternion.ext <;> norm_num

end
end Glennie.NativeGenerationCoordinatesR01
