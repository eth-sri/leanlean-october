module

public import GS.ComplexAlgebra
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Diagonal
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section


/-!
# Exact row and column dephasing of unitary matrices

The distinguished anchor index is arbitrary. Nonzero entries in its row and
column suffice; no assumption is made on the other matrix entries. The output
stays unitary and has positive real anchor ratios relative to the reference.
This is an algebraic ingredient of the local model, not a neighbourhood theorem.
-/
noncomputable section
open Matrix
namespace GS.UnitaryLocalModel

/-- The unit-modulus factor of a nonzero scalar; its value at zero is zero. -/
def phase (z : ℂ) : ℂ := z / (‖z‖ : ℂ)

section
variable {z : ℂ}
theorem norm_phase (hz : z ≠ 0) : ‖phase z‖ = 1 := by
  simp [phase, Complex.norm_real, hz]

theorem conj_phase_mul_phase (hz : z ≠ 0) :
    star (phase z) * phase z = 1 := by
  simp [Complex.conj_mul', norm_phase hz]

end

section
variable (z : ℂ)
theorem conj_phase_mul : star (phase z) * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · simp_all
  · simp [phase, div_mul_eq_mul_div, Complex.conj_mul', sq, hz]

end

variable {q : ℕ}

section
variable (Q A : CMat q) (o : Fin q)
/-- Both reference and variable matrix are nonzero on the anchor row and column. -/
def AnchorNonzero : Prop :=
  (∀ i, Q i o ≠ 0 ∧ A i o ≠ 0) ∧ (∀ j, Q o j ≠ 0 ∧ A o j ≠ 0)

def rowPhase (i : Fin q) : ℂ := phase (A i o / Q i o)
def colPhase (j : Fin q) : ℂ := phase (A o j / Q o j)


/-- Remove the row and column phases, retaining one anchor phase to avoid
counting the shared row/column gauge twice. -/
def dephase : CMat q := fun i j =>
  star (rowPhase Q A o i) * A i j * star (colPhase Q A o j) * rowPhase Q A o o

end

theorem diagonal_unitary_of_norm_one (u : Fin q → ℂ) (hu : ∀ i, ‖u i‖ = 1) :
    GS.Unitary (Matrix.diagonal u) := by
  have h : (Matrix.diagonal u)ᴴ * Matrix.diagonal u = 1 := by
    simp [diagonal_mul_diagonal, ← Matrix.diagonal_one, Complex.conj_mul', hu]
  exact ⟨h, mul_eq_one_comm.mp h⟩

section
variable {Q A : CMat q} {o : Fin q}
theorem dephase_unitary (hA : GS.Unitary A) (ha : AnchorNonzero Q A o) : GS.Unitary (dephase Q A o) := by
  have hr : ∀ i, ‖rowPhase Q A o i‖ = 1 := fun i =>
    norm_phase (div_ne_zero (ha.1 i).2 (ha.1 i).1)
  have hc : ∀ j, ‖colPhase Q A o j‖ = 1 := fun j =>
    norm_phase (div_ne_zero (ha.2 j).2 (ha.2 j).1)
  rw [show dephase Q A o = diagonal (fun i => star (rowPhase Q A o i)) * A *
      diagonal (fun j => star (colPhase Q A o j) * rowPhase Q A o o) by
    ext i j; simp [dephase, Matrix.diagonal_mul, Matrix.mul_diagonal, mul_assoc]]
  exact ((diagonal_unitary_of_norm_one _ (by simp_all)).mul hA).mul (diagonal_unitary_of_norm_one _ (by simp_all))

theorem dephase_anchor_column_positive (ha : AnchorNonzero Q A o) (i : Fin q) :
    ∃ r : ℝ, 0 < r ∧ dephase Q A o i o / Q i o = r :=
  ⟨‖A i o / Q i o‖, norm_pos_iff.mpr (div_ne_zero (ha.1 i).2 (ha.1 i).1), by
    simp only [dephase, rowPhase, colPhase]
    linear_combination star (phase (A i o / Q i o)) * (A i o / Q i o) *
      conj_phase_mul_phase (div_ne_zero (ha.1 o).2 (ha.1 o).1) + conj_phase_mul (A i o / Q i o)⟩

theorem dephase_anchor_row_positive (ha : AnchorNonzero Q A o) (j : Fin q) :
    ∃ r : ℝ, 0 < r ∧ dephase Q A o o j / Q o j = r :=
  ⟨‖A o j / Q o j‖, norm_pos_iff.mpr (div_ne_zero (ha.2 j).2 (ha.2 j).1), by
    simp only [dephase, rowPhase, colPhase]
    linear_combination star (phase (A o j / Q o j)) * (A o j / Q o j) *
      conj_phase_mul_phase (div_ne_zero (ha.1 o).2 (ha.1 o).1) + conj_phase_mul (A o j / Q o j)⟩

end

end GS.UnitaryLocalModel
