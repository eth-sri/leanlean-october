module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.Block
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
public import GS.Unitary.Support
public import GS.UnitaryManifold.FrobeniusDual


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Smooth real Frobenius duality for complex matrices

Both real and imaginary coordinates participate. This is a real continuous
linear map, not complex differentiation of a real-valued objective.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS GS.UnitaryGeometry GS.UnitaryManifold
open scoped ContDiff
namespace GS.UnitarySharing
variable {n : ℕ}

/-- The already proved Riesz representative varies real-linearly. -/
def dualMatrixCLM : (CMat n →L[ℝ] ℝ) →L[ℝ] CMat n :=
  ({ toFun := dualMatrix
     map_add' := by
       intro D E
       have h : frobDual (dualMatrix D + dualMatrix E) = D + E := by
         ext A
         rw [frobDual_apply, cFrobInner_add_left,
           ← functional_eq_cFrobInner, ← functional_eq_cFrobInner]
         rfl
       rw [← h, dualMatrix_frobDual]
     map_smul' := by
       intro a D
       have h : frobDual (a • dualMatrix D) = a • D := by
         ext A
         rw [frobDual_apply, cFrobInner_real_smul_left, ← functional_eq_cFrobInner]
         rfl
       rw [← h, dualMatrix_frobDual]
       rfl
   } : (CMat n →L[ℝ] ℝ) →ₗ[ℝ] CMat n).toContinuousLinearMap

theorem ambientGradient_contDiff_of_loss (f : CMat n → ℝ) {r s : WithTop ℕ∞}
    (hf : ContDiff ℝ s f) (hrs : r + 1 ≤ s) : ContDiff ℝ r (ambientGradient f) :=
  (dualMatrixCLM (n := n)).contDiff.comp (hf.fderiv_right hrs)

end GS.UnitarySharing
