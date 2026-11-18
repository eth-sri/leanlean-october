module

public import GS.Unitary.FrobeniusProjection
public import Mathlib.Analysis.InnerProductSpace.Dual

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS.UnitaryGeometry InnerProductSpace
open scoped BigOperators
namespace GS.UnitaryManifold
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ}

theorem cFrobInner_real_smul_right (a : ℝ) (A B : Matrix (Fin n) (Fin n) 𝕂) :
    cFrobInner A (a • B) = a * cFrobInner A B := by
  rw [cFrobInner_comm A, cFrobInner_real_smul_left, cFrobInner_comm B]

def frobDualLinear (Z : Matrix (Fin n) (Fin n) 𝕂) : Matrix (Fin n) (Fin n) 𝕂 →ₗ[ℝ] ℝ where
  toFun A := cFrobInner Z A
  map_add' A B := cFrobInner_add_right Z A B
  map_smul' c A := cFrobInner_real_smul_right c Z A

def frobDual (Z : Matrix (Fin n) (Fin n) 𝕂) : Matrix (Fin n) (Fin n) 𝕂 →L[ℝ] ℝ :=
  (frobDualLinear Z).toContinuousLinearMap

@[simp] theorem frobDual_apply (Z A : Matrix (Fin n) (Fin n) 𝕂) :
    frobDual Z A = cFrobInner Z A := rfl

def dualMatrix (D : Matrix (Fin n) (Fin n) 𝕂 →L[ℝ] ℝ) : Matrix (Fin n) (Fin n) 𝕂 :=
  decodeCFrob ((InnerProductSpace.toDual ℝ (KFrobCoordinates 𝕂 n)).symm
    (D.comp (decodeCFrob (𝕂 := 𝕂) (n := n)).toContinuousLinearMap))

theorem functional_eq_cFrobInner (D : Matrix (Fin n) (Fin n) 𝕂 →L[ℝ] ℝ)
    (A : Matrix (Fin n) (Fin n) 𝕂) : D A = cFrobInner (dualMatrix D) A := by
  rw [← encodeCFrob_inner]
  have h := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := KFrobCoordinates 𝕂 n)
    (x := encodeCFrob A) (y := D.comp (decodeCFrob (𝕂 := 𝕂) (n := n)).toContinuousLinearMap)
  simpa [dualMatrix] using h.symm

@[simp] theorem dualMatrix_frobDual (Z : Matrix (Fin n) (Fin n) 𝕂) :
    dualMatrix (frobDual Z) = Z := by
  apply sub_eq_zero.mp; apply (cFrobSq_eq_zero_iff _).mp
  change cFrobInner (dualMatrix (frobDual Z) - Z) (dualMatrix (frobDual Z) - Z) = 0
  rw [cFrobInner_sub_left, ← functional_eq_cFrobInner, frobDual_apply, sub_self]

def ambientGradient (f : Matrix (Fin n) (Fin n) 𝕂 → ℝ) (X : Matrix (Fin n) (Fin n) 𝕂) :
    Matrix (Fin n) (Fin n) 𝕂 :=
  dualMatrix (fderiv ℝ f X)

theorem ambientGradient_represents (f : Matrix (Fin n) (Fin n) 𝕂 → ℝ)
    (X A : Matrix (Fin n) (Fin n) 𝕂) : fderiv ℝ f X A = cFrobInner (ambientGradient f X) A :=
  functional_eq_cFrobInner (fderiv ℝ f X) A

end GS.UnitaryManifold
