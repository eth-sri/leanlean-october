module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Instances.Real.Lemmas
public import GS.CompactFibres
public import GS.Core
public import GS.Extensions.FiniteTopology
public import GS.Fibres
public import GS.Frobenius
public import GS.GlobalGeometry.OriginalGImage
public import GS.OriginalLocalModel
public import GS.Projection
public import GS.Shuffle


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
