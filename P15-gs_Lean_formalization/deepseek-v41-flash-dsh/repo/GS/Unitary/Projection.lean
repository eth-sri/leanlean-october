module

public import GS.Unitary.Frobenius
public import GS.Unitary.GeometryAlgebra

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Actual least-squares projection in the real Frobenius geometry onto
symmetric masks of skew-Hermitian matrices, including the imaginary diagonal. -/
noncomputable section
open Matrix
namespace GS.UnitaryGeometry
variable {n : ℕ}

theorem skewHermitianPart_eq_real_smul (A : CMat n) :
    skewHermitianPart A = (1/2 : ℝ) • (A-Aᴴ) := by
  ext i j
  simp [skewHermitianPart, Complex.real_smul]

theorem isSkewHermitian_skewHermitianPart (A : CMat n) :
    IsSkewHermitian (skewHermitianPart A) := by
  rw [skewHermitianPart_eq_real_smul]
  unfold IsSkewHermitian
  rw [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose, ← smul_neg]
  congr 1
  abel

theorem skewHermitianPart_fixed {A : CMat n} (h : IsSkewHermitian A) :
    skewHermitianPart A = A := by
  change Aᴴ = -A at h
  ext i j
  simp only [skewHermitianPart, h, Matrix.smul_apply, Matrix.sub_apply, Matrix.neg_apply,
    smul_eq_mul]
  ring

theorem skewHermitianPart_add (A B : CMat n) :
    skewHermitianPart (A+B) = skewHermitianPart A + skewHermitianPart B := by
  simp only [skewHermitianPart_eq_real_smul, Matrix.conjTranspose_add]
  have he : A+B-(Aᴴ+Bᴴ) = (A-Aᴴ)+(B-Bᴴ) := by abel
  rw [he, smul_add]
theorem skewHermitianPart_real_smul (a : ℝ) (A : CMat n) :
    skewHermitianPart (a • A) = a • skewHermitianPart A := by
  simp only [skewHermitianPart_eq_real_smul, Matrix.conjTranspose_smul, star_trivial,
    ← smul_sub, smul_smul]
  rw [mul_comm]

theorem cMask_isSkewHermitian {p : Fin n → Fin n → Prop} [DecidableRel p]
    (hp : CMaskSymmetric p) {A : CMat n} (hA : IsSkewHermitian A) :
    IsSkewHermitian (cMask p A) := by
  change Aᴴ = -A at hA
  change (cMask p A)ᴴ = -cMask p A
  rw [cMask_conjTranspose hp, hA]
  ext i j; by_cases h : p i j <;> simp [cMask, h]

def maskedSkewHermitian (p : Fin n → Fin n → Prop) [DecidableRel p]
    (A : CMat n) : CMat n := cMask p (skewHermitianPart A)

def maskedSkewHermitianMap (p : Fin n → Fin n → Prop) [DecidableRel p] :
    CMat n →ₗ[ℝ] CMat n where
  toFun := maskedSkewHermitian p
  map_add' A B := by
    simp only [maskedSkewHermitian, skewHermitianPart_add, cMask_add]
  map_smul' a A := by
    simp only [maskedSkewHermitian, skewHermitianPart_real_smul, cMask_real_smul,
      RingHom.id_apply]

theorem maskedSkewHermitian_hasSupport (p : Fin n → Fin n → Prop) [DecidableRel p]
    (A : CMat n) : CHasSupport p (maskedSkewHermitian p A) := cMask_hasSupport _ _
theorem maskedSkewHermitian_isSkewHermitian {p : Fin n → Fin n → Prop} [DecidableRel p]
    (hp : CMaskSymmetric p) (A : CMat n) : IsSkewHermitian (maskedSkewHermitian p A) :=
  cMask_isSkewHermitian hp (isSkewHermitian_skewHermitianPart A)

theorem maskedSkewHermitian_fixed {p : Fin n → Fin n → Prop} [DecidableRel p]
    {A : CMat n} (hs : CHasSupport p A) (hk : IsSkewHermitian A) :
    maskedSkewHermitian p A = A := by
  rw [maskedSkewHermitian, skewHermitianPart_fixed hk, cMask_fixed hs]
@[simp] theorem maskedSkewHermitian_idempotent {p : Fin n → Fin n → Prop} [DecidableRel p]
    (hp : CMaskSymmetric p) (A : CMat n) :
    maskedSkewHermitian p (maskedSkewHermitian p A) = maskedSkewHermitian p A :=
  maskedSkewHermitian_fixed (maskedSkewHermitian_hasSupport _ _)
    (maskedSkewHermitian_isSkewHermitian hp _)

end GS.UnitaryGeometry
