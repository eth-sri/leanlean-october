module

public import GS.GlobalGeometry.OriginalGImage

@[expose] public section


/-!
# Polynomial equations and radial algebra for the actual rank-one cone

This module uses Matrix.rank, the inherited Frobenius sum, and the induced
matrix topology. In particular it does not replace the determinantal cone by
a formal type with assumed topological properties.

The two-column-minor lemma and normalized outer-factor existence are reused
from OriginalGImage.
-/
noncomputable section
open Matrix GS GS.Extensions GS.GlobalGeometry
namespace GS.Nonmanifold

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

section
variable (W : Matrix (Fin 2) κ ℝ)
/-- The converse to the two-column-minor lemma, including the zero first row. -/
theorem rank_le_one_of_two_column_minors (h : ∀ j k, W 0 j * W 1 k = W 0 k * W 1 j) : W.rank ≤ 1 := by
  suffices ∃ u v, W = outer u v by obtain ⟨u,v,rfl⟩ := this; exact rank_outer_le_one _ _
  by_cases hz : ∀ j, W 0 j = 0
  · exact ⟨![0,1], W 1, by ext i j; fin_cases i <;> simp [outer, hz]⟩
  · obtain ⟨j,hj⟩ := not_forall.mp hz
    exact ⟨![1, W 1 j / W 0 j], W 0, by ext i k; fin_cases i <;> simp [outer]; grind⟩

theorem rank_le_one_iff_minors :
    W.rank ≤ 1 ↔ ∀ j k, W 0 j * W 1 k = W 0 k * W 1 j :=
  ⟨fun h => rank_le_one_minor W h 0 1, rank_le_one_of_two_column_minors W⟩

end

theorem frobSq_pos_of_ne_zero {ι : Type*} [Fintype ι]
    {W : Matrix ι κ ℝ} (hW : W ≠ 0) : 0 < frobSq W :=
  (frobSq_nonneg W).lt_of_ne fun h => hW ((frobSq_eq_zero_iff W).mp h.symm)

end GS.Nonmanifold
