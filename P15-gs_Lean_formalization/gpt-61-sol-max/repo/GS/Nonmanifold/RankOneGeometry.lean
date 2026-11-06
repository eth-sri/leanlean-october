
import GS.GlobalGeometry.OriginalGImage



/-!
# Polynomial equations and radial algebra for the actual rank-one cone

This module uses Matrix.rank, the inherited Frobenius sum, and the induced
matrix topology. In particular it does not replace the determinantal cone by
a formal type with assumed topological properties.

The two-column-minor lemma and normalized outer-factor existence are reused
from OriginalGImage.
-/
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
    let a := W 1 j / W 0 j
    have hrow (k : κ) : W 1 k = a * W 0 k := by grind
    have he : W = outer ![1,a] (W 0) := by
      ext i k
      fin_cases i <;> simp [outer, hrow]
    rw [he]
    exact rank_outer_le_one _ _





end GS.Nonmanifold
