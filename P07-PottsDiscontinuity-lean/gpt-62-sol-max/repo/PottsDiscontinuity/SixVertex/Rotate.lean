module

public import PottsDiscontinuity.SixVertex.Defs

@[expose] public section

namespace PottsDiscontinuity.SixVertex

variable {N : ℕ}

theorem nxt_val_mod (i : Fin N) : (nxt i).val = (i.val + 1) % N := by
  cases N with
  | zero => exact i.elim0
  | succ N =>
    rw [nxt, coe_finRotate]
    split_ifs with h
    · simp_all
    simp_all [Nat.mod_eq_of_lt, Fin.val_lt_last]

theorem prv_val_of_pos (i : Fin N) (hi : 0 < i.val) : (prv i).val = i.val - 1 := by
  cases N with
  | zero => exact i.elim0
  | succ k =>
    rw [prv, finRotate_symm_apply, Fin.val_sub_one_of_ne_zero]
    aesop

theorem prv_val_zero (i : Fin N) (hi : i.val = 0) : (prv i).val + 1 = N := by
  cases N with
  | zero => exact i.elim0
  | succ k => simp_all

end PottsDiscontinuity.SixVertex
