module

public import GS.Unitary.Frobenius
public import GS.Unitary.GeometryAlgebra

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Matrix
namespace GS.UnitaryGeometry
variable {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}

theorem skewHermitianPart_eq_real_smul (A : Matrix (Fin n) (Fin n) 𝕂) :
    skewHermitianPart A = (1 / 2 : ℝ) • (A - Aᴴ) := rfl

theorem isSkewHermitian_skewHermitianPart (A : Matrix (Fin n) (Fin n) 𝕂) :
    IsSkewHermitian (skewHermitianPart A) := by
  unfold skewHermitianPart IsSkewHermitian
  rw [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose, ← smul_neg]
  congr 1; abel

theorem skewHermitianPart_fixed {A : Matrix (Fin n) (Fin n) 𝕂} (h : IsSkewHermitian A) :
    skewHermitianPart A = A := by
  change Aᴴ = -A at h
  simp only [skewHermitianPart, h, sub_neg_eq_add, ← two_smul ℝ A, smul_smul]
  norm_num

theorem skewHermitianPart_add (A B : Matrix (Fin n) (Fin n) 𝕂) :
    skewHermitianPart (A + B) = skewHermitianPart A + skewHermitianPart B := by
  simp only [skewHermitianPart, Matrix.conjTranspose_add]
  have he : A + B - (Aᴴ + Bᴴ) = (A - Aᴴ) + (B - Bᴴ) := by abel
  rw [he, smul_add]

theorem skewHermitianPart_real_smul (a : ℝ) (A : Matrix (Fin n) (Fin n) 𝕂) :
    skewHermitianPart (a • A) = a • skewHermitianPart A := by
  simp only [skewHermitianPart, Matrix.conjTranspose_smul, star_trivial, ← smul_sub, smul_smul, mul_comm]

theorem cMask_isSkewHermitian {p : Fin n → Fin n → Prop} [DecidableRel p]
    (hp : CMaskSymmetric p) {A : Matrix (Fin n) (Fin n) 𝕂} (hA : IsSkewHermitian A) :
    IsSkewHermitian (cMask p A) := by
  change Aᴴ = -A at hA; change (cMask p A)ᴴ = -cMask p A
  rw [cMask_conjTranspose hp, hA]
  ext i j; by_cases h : p i j <;> simp [cMask, h]

def maskedSkewHermitian (p : Fin n → Fin n → Prop) [DecidableRel p]
    (A : Matrix (Fin n) (Fin n) 𝕂) : Matrix (Fin n) (Fin n) 𝕂 :=
  cMask p (skewHermitianPart A)

def maskedSkewHermitianMap (p : Fin n → Fin n → Prop) [DecidableRel p] :
    Matrix (Fin n) (Fin n) 𝕂 →ₗ[ℝ] Matrix (Fin n) (Fin n) 𝕂 where
  toFun := maskedSkewHermitian p
  map_add' A B := by simp only [maskedSkewHermitian, skewHermitianPart_add, cMask_add]
  map_smul' a A := by simp only [maskedSkewHermitian, skewHermitianPart_real_smul, cMask_real_smul, RingHom.id_apply]

end GS.UnitaryGeometry
