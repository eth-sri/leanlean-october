module

public import GS.NonmanifoldCompletion.BlockRealization
public import GS.Continuation.PointedCompactImage

@[expose] public section


/-!
# Membership of the original exponential parametrization in the GS family

This closes an actual definition-level gap: originalF takes values in the
unchanged localFamily, with its scalar perfect shuffle and consecutive blocks.
The result holds for all skew c,z, not just on a sufficiently small compact K.
No manifold, local-coverage, or same-fibres assumption is used.

-/
noncomputable section
open Matrix GS GS.Extensions GS.Continuation
namespace GS.NonmanifoldCompletion

/-- The middle q-by-q blocks are orthogonal globally in the skew coordinates. -/
theorem originalPsi_orthogonal (Q₀ H : Mat q)
    (hQ₀ : Orthogonal Q₀) (hH : IsSkew H) : Orthogonal (originalPsi Q₀ H) :=
  hQ₀.mul (matrixExp_orthogonal hH)

section
variable {q : ℕ} (Q₀ : Mat q)
/-- Original f has a genuine three-factor GS representation without smallness. -/
theorem originalF_mem_localFamily (hQ₀ : Orthogonal Q₀)
    (ell r : Fin q → ℝ) (c z : Mat q) (u : CircleVector)
    (hc : IsSkew c) (hz : IsSkew z) (hu : OnCircle u) :
    originalF Q₀ (ell,r,c,z,u) ∈ localFamily q := by
  obtain ⟨S,hS,hdiag⟩ := exists_common_middle_diagonalizer u hu
  let A := originalPsi Q₀ (c+z)
  let B := originalPsi Q₀ (c-z)
  let U := fun i => rotation (ell i) * S
  let V := fun j => Sᵀ * rotation (r j)
  have hA := originalPsi_orthogonal Q₀ (c+z) hQ₀ (by simp_all [IsSkew, add_comm])
  have hB := originalPsi_orthogonal Q₀ (c-z) hQ₀ (by simp_all [IsSkew, add_comm, sub_eq_add_neg])
  have he : originalF Q₀ (ell,r,c,z,u) =
      flattenBlocks (blockMatrix U * centralPair A B * blockMatrix V) := by
    ext i j
    let x := finProdFinEquiv.symm i
    let y := finProdFinEquiv.symm j
    change (rotation (ell x.1) * middleBlock (A x.1 y.1) (B x.1 y.1) u *
      rotation (r y.1)) x.2 y.2 =
      (blockMatrix U * centralPair A B * blockMatrix V) x y
    rw [small_block_sandwich,hdiag]
    simp only [U,V,x,y,Matrix.mul_assoc]
  exact (mem_localFamily_iff_block_sandwich (𝕜 := ℝ) _).2 ⟨U, V, A, B, fun i => (rotation_orthogonal (ell i)).mul hS, fun j => hS.transpose.mul (rotation_orthogonal (r j)), hA, hB, he⟩

/-- Every point of every original K_eta maps into the original family. -/
theorem originalF_mem_of_mem_K (hQ₀ : Orthogonal Q₀)
    {η : ℝ} {p : OriginalParameters q} (hp : p ∈ originalK q η) :
    originalF Q₀ p ∈ localFamily q := by
  obtain ⟨-,-,-,hc,hz,-,-,hu⟩ := hp
  exact originalF_mem_localFamily Q₀ hQ₀ _ _ _ _ _ hc hz hu

/-- In particular the distinguished base point belongs to the actual family. -/
theorem basePoint_mem_localFamily (hQ₀ : Orthogonal Q₀) :
    basePoint Q₀ ∈ localFamily q := by
  have h := originalF_mem_of_mem_K Q₀ hQ₀ (originalBaseParameters_mem q (by rfl))
  rwa [originalF_basePoint] at h

end

end GS.NonmanifoldCompletion
