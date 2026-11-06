module

public import PottsDiscontinuity.SixVertex.Interlace

/-!
# Elementary properties of the transfer matrix `V` and its blocks `V^{[n]}`

* `V` is symmetric (`transferMatrix_transpose`), has nonnegative entries for `c ≥ 0`, and is block
  diagonal with respect to the number of up arrows (`transferMatrix_apply_eq_zero_of_card_ne`,
  `transferMatrix_mulVec_supported`, `transferMatrix_submatrix_sigma_eq_blockDiagonal'`);
* each block `V^{[n]}` is symmetric and nonnegative, with diagonal entries `2`.
-/

public section

open Finset Matrix

namespace PottsDiscontinuity.SixVertex

variable {N : ℕ} {c : ℝ}

section
variable (c : ℝ)
theorem transferMatrix_apply (x y : Finset (Fin N)) :
    transferMatrix N c x y =
      if x = y then 2 else
        if Interlaced x y then c ^ (univ.filter fun i => Psi x i ≠ Psi y i).card else 0 := by
  rfl

@[simp] theorem transferMatrix_apply_self (x : Finset (Fin N)) :
    transferMatrix N c x x = 2 := by
  rw [transferMatrix_apply]; simp
end

section
variable {x y : Finset (Fin N)}
theorem transferMatrix_apply_of_ne (hxy : x ≠ y) (h : Interlaced x y) :
    transferMatrix N c x y = c ^ (univ.filter fun i => Psi x i ≠ Psi y i).card := by
  simp_all [transferMatrix_apply]

theorem transferMatrix_apply_of_not_interlaced (hxy : x ≠ y)
    (h : ¬ Interlaced x y) : transferMatrix N c x y = 0 := by
  simp_all [transferMatrix_apply]

/-- `V(x, y) = 0` unless `x` and `y` have the same number of entries (block diagonality). -/
theorem transferMatrix_apply_eq_zero_of_card_ne (h : x.card ≠ y.card) :
    transferMatrix N c x y = 0 :=
  transferMatrix_apply_of_not_interlaced (by grind) (fun hi => h hi.card_eq)
end

/-- `V` is symmetric. -/
theorem transferMatrix_symm (x y : Finset (Fin N)) :
    transferMatrix N c x y = transferMatrix N c y x := by
  rw [transferMatrix_apply, transferMatrix_apply]
  by_cases hxy : x = y
  · simp_all
  · have hyx : y ≠ x := by grind
    simp only [hxy, hyx, ↓reduceIte]
    by_cases hi : Interlaced x y
    · simp only [hi, hi.symm, ↓reduceIte]
      congr 2
      grind
    simp_all [Interlaced]

theorem transferMatrix_nonneg (hc : 0 ≤ c) (x y : Finset (Fin N)) :
    0 ≤ transferMatrix N c x y := by
  rw [transferMatrix_apply]
  positivity

/-- For `c > 0`: `V(x, y) > 0` iff `x = y` or `x` and `y` are interlaced. -/
theorem transferMatrix_pos_iff (hc : 0 < c) (x y : Finset (Fin N)) :
    0 < transferMatrix N c x y ↔ x = y ∨ Interlaced x y := by
  rw [transferMatrix_apply]
  by_cases hxy : x = y
  · simp_all
  aesop

/-! ### The blocks `V^{[n]}` -/

section
variable (c : ℝ) (n : ℕ)
theorem transferBlock_apply (x y : State N n) :
    transferBlock N c n x y = transferMatrix N c x.1 y.1 := rfl

@[simp] theorem transferBlock_apply_self (x : State N n) :
    transferBlock N c n x x = 2 := by
  rw [transferBlock_apply, transferMatrix_apply_self]
end

section
variable (n : ℕ)
theorem transferBlock_transpose  : (transferBlock N c n)ᵀ = transferBlock N c n := by
  ext x y
  exact transferMatrix_symm y.1 x.1

theorem transferBlock_isHermitian  : (transferBlock N c n).IsHermitian :=
  transferBlock_transpose n
end

theorem transferBlock_nonneg (hc : 0 ≤ c) (n : ℕ) (x y : State N n) :
    0 ≤ transferBlock N c n x y :=
  transferMatrix_nonneg hc x.1 y.1

theorem transferBlock_pos_iff (hc : 0 < c) (n : ℕ) (x y : State N n) :
    0 < transferBlock N c n x y ↔ x.1 = y.1 ∨ Interlaced x.1 y.1 :=
  transferMatrix_pos_iff hc x.1 y.1

/-! ### `V` is the block diagonal matrix of the `V^{[n]}` -/

end PottsDiscontinuity.SixVertex
