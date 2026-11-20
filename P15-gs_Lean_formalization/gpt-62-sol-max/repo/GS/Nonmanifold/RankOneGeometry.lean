module

public import GS.GlobalGeometry.OriginalGImage

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

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
open scoped BigOperators
namespace GS.Nonmanifold

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The converse to the two-column-minor lemma, including the zero first row. -/
theorem rank_le_one_of_two_column_minors (W : Matrix (Fin 2) κ ℝ)
    (h : ∀ j k, W 0 j * W 1 k = W 0 k * W 1 j) : W.rank ≤ 1 := by
  by_cases hz : ∀ j, W 0 j = 0
  · have he : W = outer ![0,1] (W 1) := by
      ext i j
      fin_cases i <;> simp [outer, hz]
    rw [he]
    exact rank_outer_le_one _ _
  · obtain ⟨j,hj⟩ := not_forall.mp hz
    let a : ℝ := W 1 j / W 0 j
    have hrow (k : κ) : W 1 k = a * W 0 k := by
      have hm := h j k
      dsimp [a]
      field_simp [hj]
      nlinarith [hm]
    have he : W = outer ![1,a] (W 0) := by
      ext i k
      fin_cases i <;> simp [outer, hrow]
    rw [he]
    exact rank_outer_le_one _ _

theorem rank_le_one_iff_minors (W : Matrix (Fin 2) κ ℝ) :
    W.rank ≤ 1 ↔ ∀ j k, W 0 j * W 1 k = W 0 k * W 1 j :=
  ⟨fun h => rank_le_one_two_column_minor W h, rank_le_one_of_two_column_minors W⟩

theorem frobSq_pos_of_ne_zero {ι : Type*} [Fintype ι]
    {W : Matrix ι κ ℝ} (hW : W ≠ 0) : 0 < frobSq W := by
  have hne : frobSq W ≠ 0 := fun h => hW ((frobSq_eq_zero_iff W).mp h)
  exact lt_of_le_of_ne (frobSq_nonneg W) (Ne.symm hne)

end GS.Nonmanifold
