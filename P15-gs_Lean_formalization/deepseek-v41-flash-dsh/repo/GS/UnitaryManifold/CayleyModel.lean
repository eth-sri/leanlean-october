module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
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


@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! The real supported skew-Hermitian coordinate model and its ambient projection. -/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS.UnitaryGeometry
namespace GS.UnitaryManifold
variable {n : ℕ}

abbrev modelSpace (block : Fin n → ℕ) := supportedSkewSpace block
abbrev Model (block : Fin n → ℕ) := ↥(modelSpace block)

theorem admissible_model {block : Fin n → ℕ} (x : Model block) :
    admissible x.val := admissible_of_isSkew x.val x.property.2

def modelInclusion (block : Fin n → ℕ) : Model block →L[ℝ] CMat n :=
  (modelSpace block).subtypeL

theorem masked_skew_model (block : Fin n → ℕ) (A : CMat n) :
    cBlockProjection block (GS.skewHermitianPart A) ∈ modelSpace block := by
  refine ⟨?_, cMask_isSkewHermitian (fun i j => eq_comm) (isSkewHermitian_skewHermitianPart A)⟩
  intro i j hij
  simp [cBlockProjection, cMask, hij]

def modelProjectionLinear (block : Fin n → ℕ) : CMat n →ₗ[ℝ] Model block where
  toFun A := ⟨cBlockProjection block (GS.skewHermitianPart A), masked_skew_model block A⟩
  map_add' A B := by
    apply Subtype.ext
    exact (maskedSkewHermitianMap (fun i j => block i = block j)).map_add A B
  map_smul' c A := by
    apply Subtype.ext
    exact (maskedSkewHermitianMap (fun i j => block i = block j)).map_smul c A

def modelProjection (block : Fin n → ℕ) : CMat n →L[ℝ] Model block :=
  (modelProjectionLinear block).toContinuousLinearMap

@[simp] theorem modelProjection_val (block : Fin n → ℕ) (A : CMat n) :
    (modelProjection block A).val = cBlockProjection block (GS.skewHermitianPart A) := rfl

theorem modelProjection_val_of_mem (block : Fin n → ℕ) (A : CMat n)
    (hA : A ∈ modelSpace block) : (modelProjection block A).val = A := by
  rw [modelProjection_val, skewHermitianPart_fixed hA.2]
  exact blockProjection_eq_self block A hA.1

@[simp] theorem modelProjection_inclusion (block : Fin n → ℕ) (x : Model block) :
    modelProjection block x.val = x := by
  apply Subtype.ext
  exact modelProjection_val_of_mem block x.val x.property

end GS.UnitaryManifold
