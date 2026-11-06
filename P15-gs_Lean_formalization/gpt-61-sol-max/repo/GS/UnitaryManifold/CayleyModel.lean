
import GS.UnitaryManifold.CayleyAlgebra
import GS.MatrixGeometry.Inner
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Matrix.Normed



/-! The real supported skew-Hermitian coordinate model and its ambient projection. -/
noncomputable section
open GS.UnitaryGeometry
namespace GS.UnitaryManifold

variable (block : Fin n → ℕ)

abbrev modelSpace := supportedSkewSpace block
abbrev Model := ↥(modelSpace block)

theorem admissible_model {block : Fin n → ℕ} (x : Model block) :
    admissible x.val := admissible_of_isSkew x.val x.property.2

def modelInclusion := (modelSpace block).subtypeL



/-- Use the same physical Frobenius projection as the shared-factor charts. -/
def modelProjection := (GS.MatrixBase.cFrobProjection (modelSpace block)).codRestrict _
    (GS.MatrixBase.cFrobProjection_mem _)

theorem modelProjection_val_of_mem (A : CMat n)
    (hA : A ∈ modelSpace block) : (modelProjection block A).val = A :=
  GS.MatrixBase.cFrobProjection_of_mem _ _ hA

@[simp] theorem modelProjection_inclusion (x : Model block) :
    modelProjection block x.val = x := by
  grind [modelProjection_val_of_mem]

end GS.UnitaryManifold
