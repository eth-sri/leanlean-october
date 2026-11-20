module

public import Mathlib.LinearAlgebra.Matrix.Rank

public import Mathlib.LinearAlgebra.Dimension.Free

@[expose] public section

namespace GS
open Matrix
variable {𝕜 ι κ τ : Type*} [Field 𝕜] [Fintype κ] [Fintype τ]

/-- Factor through the range, embedding it in the prescribed intermediate space. -/
theorem rank_le_card_iff_factorization (A : Matrix ι κ 𝕜) :
    A.rank ≤ Fintype.card τ ↔ ∃ U : Matrix ι τ 𝕜, ∃ V : Matrix τ κ 𝕜, A = U * V := by
  classical
  refine ⟨?_, fun ⟨U,V,h⟩ => h ▸ (rank_mul_le_left U V).trans (rank_le_card_width U)⟩
  intro h
  let F := A.mulVecLin
  let S := LinearMap.range F
  have hr : Module.finrank 𝕜 S ≤ Module.finrank 𝕜 (τ → 𝕜) := by simpa [S, F, Matrix.rank] using h
  obtain ⟨i,hi⟩ := finrank_le_iff_exists_linearMap.mp hr
  obtain ⟨r,hr⟩ := i.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
  refine ⟨LinearMap.toMatrix' (S.subtype.comp r), LinearMap.toMatrix' (i.comp F.rangeRestrict), ?_⟩
  rw [← LinearMap.toMatrix'_comp, LinearMap.comp_assoc, ← LinearMap.comp_assoc F.rangeRestrict i r, hr, LinearMap.id_comp]
  exact (Matrix.toLin'.symm_apply_apply A).symm

end GS
