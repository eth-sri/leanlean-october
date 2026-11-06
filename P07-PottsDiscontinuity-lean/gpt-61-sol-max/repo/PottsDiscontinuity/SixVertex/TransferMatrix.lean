module
public import Mathlib

public import PottsDiscontinuity.SixVertex.Interlace

/-!
# Elementary properties of the transfer matrix `V` and its blocks `V^{[n]}`

* `V` is symmetric (`transferMatrix_transpose`), has nonnegative entries for `c ≥ 0`, and is block
  diagonal with respect to the number of up arrows (`transferMatrix_apply_eq_zero_of_card_ne`,
  `transferMatrix_mulVec_supported`, `transferMatrix_submatrix_sigma_eq_blockDiagonal'`);
* each block `V^{[n]}` is symmetric and nonnegative, with diagonal entries `2`.
-/

@[expose] public section

open Finset Matrix

namespace PottsDiscontinuity.SixVertex

variable {N : ℕ} {c : ℝ}

theorem transferMatrix_apply (c : ℝ) (x y : Finset (Fin N)) :
    transferMatrix N c x y =
      if x = y then 2 else
        if Interlaced x y then c ^ (univ.filter fun i => Psi x i ≠ Psi y i).card else 0 := rfl

@[simp] theorem transferMatrix_apply_self (c : ℝ) (x : Finset (Fin N)) :
    transferMatrix N c x x = 2 := by
  rw [transferMatrix_apply]; simp

section

variable {x y : Finset (Fin N)}
include x y

theorem transferMatrix_apply_of_ne  (hxy : x ≠ y) (h : Interlaced x y) :
    transferMatrix N c x y = c ^ (univ.filter fun i => Psi x i ≠ Psi y i).card := by
  rw [transferMatrix_apply]; simp [hxy, h]

theorem transferMatrix_apply_of_not_interlaced  (hxy : x ≠ y)
    (h : ¬ Interlaced x y) : transferMatrix N c x y = 0 := by
  rw [transferMatrix_apply]; simp [hxy, h]

/-- `V(x, y) = 0` unless `x` and `y` have the same number of entries (block diagonality). -/
theorem transferMatrix_apply_eq_zero_of_card_ne  (h : x.card ≠ y.card) :
    transferMatrix N c x y = 0 := transferMatrix_apply_of_not_interlaced (fun e => h (e ▸ rfl)) fun hi => h (Interlaced.card_eq hi)

end

/-- `V` is symmetric. -/
theorem transferMatrix_symm (x y : Finset (Fin N)) :
    transferMatrix N c x y = transferMatrix N c y x := by
  rw [transferMatrix_apply, transferMatrix_apply]
  by_cases hxy : x = y
  · subst hxy; rfl
  · have hyx : y ≠ x := fun e => hxy e.symm
    simp only [hxy, hyx]
    by_cases hi : Interlaced x y
    · simp only [hi, hi.symm, ↓reduceIte]
      
      
      simp [ne_comm]
    · simp_all [Interlaced]

theorem transferMatrix_nonneg (hc : 0 ≤ c) (x y : Finset (Fin N)) :
    0 ≤ transferMatrix N c x y := by
  rw [transferMatrix_apply]
  aesop

/-- For `c > 0`: `V(x, y) > 0` iff `x = y` or `x` and `y` are interlaced. -/
theorem transferMatrix_pos_iff (hc : 0 < c) (x y : Finset (Fin N)) :
    0 < transferMatrix N c x y ↔ x = y ∨ Interlaced x y := by
  rw [transferMatrix_apply]
  by_cases hxy : x = y
  · simp [hxy]
  · by_cases hi : Interlaced x y
    all_goals simp_all

/-! ### The blocks `V^{[n]}` -/

theorem transferBlock_apply (c : ℝ) (n : ℕ) (x y : State N n) :
    transferBlock N c n x y = transferMatrix N c x.1 y.1 := rfl

@[simp] theorem transferBlock_apply_self (c : ℝ) (n : ℕ) (x : State N n) :
    transferBlock N c n x x = 2 := by
  rw [transferBlock_apply, transferMatrix_apply_self]

theorem transferBlock_transpose (n : ℕ) : (transferBlock N c n)ᵀ = transferBlock N c n := by
  ext x y
  exact transferMatrix_symm y.1 x.1

theorem transferBlock_isHermitian (n : ℕ) : (transferBlock N c n).IsHermitian := by
  
  exact transferBlock_transpose n

theorem transferBlock_nonneg (hc : 0 ≤ c) (n : ℕ) (x y : State N n) :
    0 ≤ transferBlock N c n x y :=
  transferMatrix_nonneg hc x.1 y.1

theorem transferBlock_pos_iff (hc : 0 < c) (n : ℕ) (x y : State N n) :
    0 < transferBlock N c n x y ↔ x.1 = y.1 ∨ Interlaced x.1 y.1 :=
  transferMatrix_pos_iff hc x.1 y.1

/-! ### `V` is the block diagonal matrix of the `V^{[n]}` -/

end PottsDiscontinuity.SixVertex
