module

public import GS.Unitary.Support
public import GS.Frobenius

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Matrix
open scoped BigOperators
namespace GS.UnitaryGeometry
variable {𝕂 : Type*} [RCLike 𝕂] {n : ℕ}

def cFrobInner (A B : Matrix (Fin n) (Fin n) 𝕂) : ℝ :=
  ∑ i, ∑ j, RCLike.re (star (A i j) * B i j)
def cFrobSq (A : Matrix (Fin n) (Fin n) 𝕂) : ℝ := cFrobInner A A

theorem cFrobInner_eq_re_trace (A B : Matrix (Fin n) (Fin n) 𝕂) :
    cFrobInner A B = RCLike.re (Matrix.trace (Aᴴ * B)) := by
  simp only [cFrobInner, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, map_sum]
  exact Finset.sum_comm

theorem cFrobInner_comm (A B : Matrix (Fin n) (Fin n) 𝕂) : cFrobInner A B = cFrobInner B A := by
  unfold cFrobInner
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have : star (B i j) * A i j = star (star (A i j) * B i j) := by simp [mul_comm]
  rw [this, RCLike.star_def, RCLike.conj_re]

@[simp] theorem cFrobInner_zero_left (A : Matrix (Fin n) (Fin n) 𝕂) : cFrobInner 0 A = 0 := by
  simp [cFrobInner]
@[simp] theorem cFrobInner_zero_right (A : Matrix (Fin n) (Fin n) 𝕂) : cFrobInner A 0 = 0 := by
  simp [cFrobInner]

theorem cFrobInner_add_left (A B C : Matrix (Fin n) (Fin n) 𝕂) :
    cFrobInner (A + B) C = cFrobInner A C + cFrobInner B C := by
  simp only [cFrobInner, Matrix.add_apply, star_add, add_mul, map_add, Finset.sum_add_distrib]

theorem cFrobInner_add_right (A B C : Matrix (Fin n) (Fin n) 𝕂) :
    cFrobInner A (B + C) = cFrobInner A B + cFrobInner A C := by
  rw [cFrobInner_comm, cFrobInner_add_left, cFrobInner_comm B, cFrobInner_comm C]

theorem cFrobInner_neg_left (A B : Matrix (Fin n) (Fin n) 𝕂) :
    cFrobInner (-A) B = -cFrobInner A B := by
  simp only [cFrobInner, Matrix.neg_apply, star_neg, neg_mul, map_neg, Finset.sum_neg_distrib]

theorem cFrobInner_sub_left (A B C : Matrix (Fin n) (Fin n) 𝕂) :
    cFrobInner (A - B) C = cFrobInner A C - cFrobInner B C := by
  rw [sub_eq_add_neg, cFrobInner_add_left, cFrobInner_neg_left, sub_eq_add_neg]

theorem cFrobInner_real_smul_left (a : ℝ) (A B : Matrix (Fin n) (Fin n) 𝕂) :
    cFrobInner (a • A) B = a * cFrobInner A B := by
  simp only [cFrobInner, Matrix.smul_apply, star_smul, star_trivial, smul_mul_assoc,
    RCLike.smul_re, smul_eq_mul, Finset.mul_sum]

private theorem entry_self_eq_norm_sq (x : 𝕂) : RCLike.re (star x * x) = ‖x‖ ^ 2 := by
  rw [RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

theorem cFrobSq_nonneg (A : Matrix (Fin n) (Fin n) 𝕂) : 0 ≤ cFrobSq A := by
  unfold cFrobSq cFrobInner
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  rw [entry_self_eq_norm_sq]; positivity

theorem cFrobSq_eq_zero_iff (A : Matrix (Fin n) (Fin n) 𝕂) : cFrobSq A = 0 ↔ A = 0 := by
  constructor
  · intro h
    simp only [cFrobSq, cFrobInner, entry_self_eq_norm_sq] at h
    have hr := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => sq_nonneg ‖A i j‖).mp h
    ext i j
    have he := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg ‖A i j‖).mp
      (hr i (Finset.mem_univ i)) j (Finset.mem_univ j)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp he)
  · rintro rfl; simp [cFrobSq]

theorem cFrobInner_conjTranspose (A B : Matrix (Fin n) (Fin n) 𝕂) :
    cFrobInner Aᴴ Bᴴ = cFrobInner A B := by
  unfold cFrobInner
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.conjTranspose_apply, star_star]
  have : A i j * star (B i j) = star (star (A i j) * B i j) := by simp [mul_comm]
  rw [this, RCLike.star_def, RCLike.conj_re]

theorem cFrobInner_mul_left (A B C : Matrix (Fin n) (Fin n) 𝕂) :
    cFrobInner (A * B) C = cFrobInner B (Aᴴ * C) := by
  simp only [cFrobInner_eq_re_trace, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem cFrobInner_left_unitary (U : Matrix (Fin n) (Fin n) 𝕂) (hU : GS.KUnitary U)
    (A B : Matrix (Fin n) (Fin n) 𝕂) :
    cFrobInner (U * A) (U * B) = cFrobInner A B := by
  rw [cFrobInner_mul_left, ← Matrix.mul_assoc, hU.1]; simp

theorem cFrobInner_right_unitary (U : Matrix (Fin n) (Fin n) 𝕂) (hU : GS.KUnitary U)
    (A B : Matrix (Fin n) (Fin n) 𝕂) :
    cFrobInner (A * U) (B * U) = cFrobInner A B := by
  calc _ = cFrobInner (A * U)ᴴ (B * U)ᴴ := (cFrobInner_conjTranspose _ _).symm
    _ = cFrobInner (Uᴴ * Aᴴ) (Uᴴ * Bᴴ) := by rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    _ = cFrobInner Aᴴ Bᴴ := cFrobInner_left_unitary _ hU.conjTranspose _ _
    _ = cFrobInner A B := cFrobInner_conjTranspose _ _

end GS.UnitaryGeometry
