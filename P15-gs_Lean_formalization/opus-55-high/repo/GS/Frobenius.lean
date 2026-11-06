module

public import GS.Core

@[expose] public section


/-! Explicit Frobenius geometry. We do NOT use the default norm on `Matrix`,
which need not be the Frobenius norm.  -/

noncomputable section
open Matrix
namespace GS

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def frobInner (A B : Matrix ι κ ℝ) : ℝ := ∑ i, ∑ j, A i j * B i j

def frobSq (A : Matrix ι κ ℝ) : ℝ := frobInner A A

theorem frobInner_comm (A B : Matrix ι κ ℝ) : frobInner A B = frobInner B A := by
  simp [frobInner, mul_comm]



section
variable (A B C : Matrix ι κ ℝ)
theorem frobInner_add_left :
    frobInner (A + B) C = frobInner A C + frobInner B C := by
  simp [frobInner, add_mul, Finset.sum_add_distrib]

theorem frobInner_add_right :
    frobInner A (B + C) = frobInner A B + frobInner A C := by
  simp [frobInner, mul_add, Finset.sum_add_distrib]

theorem frobInner_sub_left :
    frobInner (A - B) C = frobInner A C - frobInner B C := by
  simp [frobInner, sub_mul, Finset.sum_sub_distrib]

theorem frobInner_sub_right :
    frobInner A (B - C) = frobInner A B - frobInner A C := by
  simp [frobInner, mul_sub, Finset.sum_sub_distrib]

end

theorem frobInner_neg_left (A B : Matrix ι κ ℝ) :
    frobInner (-A) B = -frobInner A B := by
  simp [frobInner, Finset.sum_neg_distrib]

theorem frobInner_smul_left (a : ℝ) (A B : Matrix ι κ ℝ) :
    frobInner (a • A) B = a * frobInner A B := by
  simp [frobInner, mul_assoc, Finset.mul_sum]

section
variable (A : Matrix ι κ ℝ)
theorem frobSq_nonneg : 0 ≤ frobSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _

theorem frobSq_eq_zero_iff : frobSq A = 0 ↔ A = 0 := by
  simp [frobSq, frobInner, Finset.sum_eq_zero_iff_of_nonneg, Finset.sum_nonneg, mul_self_nonneg, ← Matrix.ext_iff]

end

section
variable (A B : Matrix ι κ ℝ)
theorem frobSq_add :
    frobSq (A + B) = frobSq A + 2 * frobInner A B + frobSq B := by
  unfold frobSq
  rw [frobInner_add_left, frobInner_add_right, frobInner_add_right,
    frobInner_comm B A]
  ring

theorem frobSq_sub :
    frobSq (A - B) = frobSq A - 2 * frobInner A B + frobSq B := by
  unfold frobSq
  rw [frobInner_sub_left, frobInner_sub_right, frobInner_sub_right,
    frobInner_comm B A]
  ring

theorem frobInner_transpose :
    frobInner Aᵀ Bᵀ = frobInner A B :=
  Finset.sum_comm

theorem frobInner_eq_zero_of_disjoint (h : ∀ i j, A i j = 0 ∨ B i j = 0) : frobInner A B = 0 :=
  Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero (by grind)

end

/-- Matrix multiplication adjoint; the finite-sum proof fixes the convention. -/
theorem frobInner_mul_left {ν : Type*} [Fintype ν]
    (A : Matrix ι κ ℝ) (B : Matrix κ ν ℝ) (C : Matrix ι ν ℝ) :
    frobInner (A * B) C = frobInner B (Aᵀ * C) := by
  simp only [frobInner, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum, mul_comm, mul_left_comm]
  rw [Finset.sum_comm_cycle]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem frobInner_left_orthogonal [DecidableEq ι]
    (U : Matrix ι ι ℝ) (hU : Orthogonal U) (A B : Matrix ι κ ℝ) :
    frobInner (U * A) (U * B) = frobInner A B := by
  rw [frobInner_mul_left, ← Matrix.mul_assoc, hU.1]
  simp

theorem frobInner_right_orthogonal [DecidableEq κ]
    (V : Matrix κ κ ℝ) (hV : Orthogonal V) (A B : Matrix ι κ ℝ) :
    frobInner (A * V) (B * V) = frobInner A B := by
  rw [← frobInner_transpose, transpose_mul, transpose_mul, frobInner_left_orthogonal _ hV.transpose,
    frobInner_transpose]

end GS
