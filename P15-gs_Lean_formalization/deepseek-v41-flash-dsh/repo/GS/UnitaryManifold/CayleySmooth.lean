module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import GS.ComplexAlgebra
public import GS.Core
public import GS.Frobenius
public import GS.Unitary.Frobenius
public import GS.Unitary.GeometryAlgebra
public import GS.Unitary.Projection
public import GS.Unitary.Support
public import GS.UnitaryManifold.CayleyAlgebra
public import GS.UnitaryManifold.CayleyModel


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Smooth rational matrix formulas with the inherited matrix topology

The explicitly selected entrywise supremum norm on `CMat n` is not assumed to make it a
normed algebra under matrix multiplication. Smoothness of multiplication is
proved entrywise; smoothness of inverse follows from det and adjugate.
No matrix determinant nonvanishing assumption is dropped.

The calculus is over real scalars throughout.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix
namespace GS.UnitaryManifold
variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Coordinatewise proof avoids a noncanonical matrix norm. -/
theorem smooth_mul_at {A B : E → CMat n} {x : E}
    (hA : ContDiffAt ℝ ⊤ A x) (hB : ContDiffAt ℝ ⊤ B x) :
    ContDiffAt ℝ ⊤ (fun y => A y * B y) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  simp only [Matrix.mul_apply]
  apply ContDiffAt.sum
  intro k _
  exact (contDiffAt_pi.mp (contDiffAt_pi.mp hA i) k).mul
    (contDiffAt_pi.mp (contDiffAt_pi.mp hB k) j)

theorem smooth_conjTranspose_at {A : E → CMat n} {x : E}
    (hA : ContDiffAt ℝ ⊤ A x) :
    ContDiffAt ℝ ⊤ (fun y => (A y)ᴴ) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact Complex.conjCLE.contDiff.contDiffAt.comp x
    (contDiffAt_pi.mp (contDiffAt_pi.mp hA j) i)

theorem smooth_det : ContDiff ℝ ⊤ (fun A : CMat n => A.det) := by
  simp only [Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  apply ContDiff.mul contDiff_const
  apply contDiff_prod
  intro i _
  exact contDiff_apply_apply ℝ ℂ (σ i) i

theorem smooth_adjugate : ContDiff ℝ ⊤ (fun A : CMat n => A.adjugate) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp only [Matrix.adjugate_apply]
  apply smooth_det.comp
  apply contDiff_pi.mpr
  intro a
  apply contDiff_pi.mpr
  intro b
  by_cases ha : a = j
  · subst a
    simp only [Matrix.updateRow, Matrix.of_apply, Function.update_self]
    exact contDiff_const
  · simpa only [Matrix.updateRow, Matrix.of_apply, Function.update_of_ne ha, id_eq] using
      (contDiff_pi.mp (contDiff_pi.mp (contDiff_id : ContDiff ℝ ⊤ (fun A : CMat n => A)) a) b)

/-- Inverse is smooth exactly where it is needed in all subsequent charts. -/
theorem smooth_inverse_at (A : CMat n) (hA : A.det ≠ 0) :
    ContDiffAt ℝ ⊤ (fun B : CMat n => B⁻¹) A := by
  have h : ContDiffAt ℝ ⊤
      (fun B : CMat n => B.det⁻¹ • B.adjugate) A := by
    apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    exact (smooth_det.contDiffAt.inv hA).mul
      (contDiffAt_pi.mp (contDiffAt_pi.mp smooth_adjugate.contDiffAt i) j)
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv] using h

theorem smooth_inverse_comp_at {A : E → CMat n} {x : E}
    (hA : ContDiffAt ℝ ⊤ A x) (hd : (A x).det ≠ 0) :
    ContDiffAt ℝ ⊤ (fun y => (A y)⁻¹) x :=
  (smooth_inverse_at (A x) hd).comp x hA

theorem smooth_cayley_at (A : CMat n) (hA : admissible A) :
    ContDiffAt ℝ ⊤ cayley A := by
  exact smooth_mul_at (contDiffAt_const.sub contDiffAt_id)
    (smooth_inverse_comp_at (contDiffAt_const.add contDiffAt_id) hA)

theorem smooth_cayley_comp_at {A : E → CMat n} {x : E}
    (hA : ContDiffAt ℝ ⊤ A x) (hd : admissible (A x)) :
    ContDiffAt ℝ ⊤ (fun y => cayley (A y)) x :=
  (smooth_cayley_at (A x) hd).comp x hA

theorem admissible_open : IsOpen {A : CMat n | admissible A} := by
  exact isOpen_ne.preimage (smooth_det.continuous.comp
    (continuous_const.add continuous_id))

end GS.UnitaryManifold
