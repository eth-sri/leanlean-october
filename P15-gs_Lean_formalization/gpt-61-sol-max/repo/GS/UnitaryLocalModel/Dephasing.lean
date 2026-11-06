import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Linarith

import GS.ComplexAlgebra
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum



/-!
# Exact row and column dephasing of unitary matrices

The distinguished anchor index is arbitrary. Nonzero entries in its row and
column suffice; no assumption is made on the other matrix entries. The output
stays unitary and has positive real anchor ratios relative to the reference.
This is an algebraic ingredient of the local model, not a neighbourhood theorem.
-/
noncomputable section
namespace GS.UnitaryLocalModel

variable (z : ℂ)

/-- The unit-modulus factor of a nonzero scalar; its value at zero is zero. -/
def phase  : ℂ := z / (‖z‖ : ℂ)

theorem norm_phase {z : ℂ} (hz : z ≠ 0) : ‖phase z‖ = 1 := by simp_all [phase,Complex.norm_real]

theorem conj_phase_mul_phase {z : ℂ} (hz : z ≠ 0) :
    star (phase z) * phase z = 1 := by
  simpa [Complex.normSq_eq_norm_sq,norm_phase hz] using
    (Complex.normSq_eq_conj_mul_self (z := phase z)).symm

theorem norm_mul_phase  : (‖z‖ : ℂ) * phase z = z := by
  by_cases hz : z = 0
  · aesop
  · exact mul_div_cancel₀ z (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))

theorem conj_phase_mul  : star (phase z) * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · aesop
  · grind [conj_phase_mul_phase,norm_mul_phase]

variable (Q A : CMat q) (o : Fin q)

/-- Both reference and variable matrix are nonzero on the anchor row and column. -/
def AnchorNonzero : Prop :=
  (∀ i, Q i o ≠ 0 ∧ A i o ≠ 0) ∧ (∀ j, Q o j ≠ 0 ∧ A o j ≠ 0)

def rowPhase (i : Fin q) : ℂ := phase (A i o / Q i o)
def colPhase (j : Fin q) : ℂ := phase (A o j / Q o j)



/-- Remove the row and column phases, retaining one anchor phase to avoid
counting the shared row/column gauge twice. -/
def dephase := fun i j =>
  star (rowPhase Q A o i) * A i j * star (colPhase Q A o j) * rowPhase Q A o o

theorem diagonal_unitary_of_norm_one (u : Fin q → ℂ) (hu : ∀ i, ‖u i‖ = 1) :
    GS.Unitary (Matrix.diagonal u) := by
  apply GS.MatrixBase.Unitary.of_conjTranspose_mul
  simp [Matrix.diagonal_conjTranspose,Matrix.diagonal_mul_diagonal,
    ← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,hu]

theorem dephase_unitary {Q A : CMat q} {o : Fin q}
    (hA : GS.Unitary A) (ha : AnchorNonzero Q A o) : GS.Unitary (dephase Q A o) := by
  have hr : ∀ i, ‖rowPhase Q A o i‖ = 1 := fun i =>
    norm_phase (div_ne_zero (ha.1 i).2 (ha.1 i).1)
  have hc : ∀ j, ‖colPhase Q A o j‖ = 1 := fun j =>
    norm_phase (div_ne_zero (ha.2 j).2 (ha.2 j).1)
  have he : dephase Q A o = Matrix.diagonal (fun i => star (rowPhase Q A o i)) * A *
      Matrix.diagonal (fun j => star (colPhase Q A o j) * rowPhase Q A o o) := by ext <;> simp_all [dephase,Matrix.diagonal_mul,Matrix.mul_diagonal] <;> ring
  rw [he]
  have hL := diagonal_unitary_of_norm_one (fun i => star (rowPhase Q A o i))
    (fun i => by aesop)
  have hR := diagonal_unitary_of_norm_one
    (fun j => star (colPhase Q A o j) * rowPhase Q A o o)
    (fun j => by aesop)
  exact (hL.mul hA).mul hR

theorem dephase_anchor_column_positive {Q A : CMat q} {o : Fin q}
    (ha : AnchorNonzero Q A o) (i : Fin q) :
    ∃ r : ℝ, 0 < r ∧ dephase Q A o i o / Q i o = r :=
  by
  refine ⟨‖A i o / Q i o‖, norm_pos_iff.mpr (div_ne_zero (ha.1 i).2 (ha.1 i).1), ?_⟩
  grind [dephase,rowPhase,colPhase,conj_phase_mul_phase,conj_phase_mul,mul_ne_zero,inv_ne_zero,AnchorNonzero]

theorem dephase_anchor_row_positive {Q A : CMat q} {o : Fin q}
    (ha : AnchorNonzero Q A o) (j : Fin q) :
    ∃ r : ℝ, 0 < r ∧ dephase Q A o o j / Q o j = r :=
  by
  refine ⟨‖A o j / Q o j‖, norm_pos_iff.mpr (div_ne_zero (ha.2 j).2 (ha.2 j).1), ?_⟩
  grind [dephase,rowPhase,colPhase,conj_phase_mul_phase,conj_phase_mul,mul_ne_zero,inv_ne_zero,AnchorNonzero]

/-- Column phases with their anchor fixed to zero. -/
def zeroAnchorSpace (o : Fin q) : Submodule ℝ (Fin q → ℝ) := (LinearMap.proj o).ker

/-- The derivative of the anchor constraints along row and column phase directions. -/
def phaseConstraintMap (o : Fin q) :
    ((Fin q → ℝ) × zeroAnchorSpace o) →ₗ[ℝ]
      ((Fin q → ℝ) × ({j : Fin q // j ≠ o} → ℝ)) where
  toFun x := (x.1, fun j => x.1 o + x.2.val j.val)
  map_add' x y := by ext <;> simp_all <;> nlinarith
  map_smul' r x := by ext <;> simp_all <;> nlinarith

/-- Every set of infinitesimal anchor constraints is attained, with no
unproved rank assertion or dimensional counting. -/
theorem phaseConstraintMap_surjective (o : Fin q) :
    Function.Surjective (phaseConstraintMap o) := by
  rintro ⟨a, b⟩
  let β : Fin q → ℝ := fun j => if hj : j = o then 0 else b ⟨j, hj⟩ - a o
  have hβ : β ∈ zeroAnchorSpace o := by simp [β, zeroAnchorSpace]
  refine ⟨(a, ⟨β, hβ⟩), ?_⟩
  apply Prod.ext
  · rfl
  · funext j
    change a o + β j.val = b j
    simp [β, j.property]

end GS.UnitaryLocalModel
