import GS.MatrixGeometry.Base
namespace GS.GlobalGeometry
/-- The index with prescribed local coordinate in the physical block of `i`. -/
def localBlockIndex (hb : 0 < b) (hbn : b ∣ n) (i : Fin n) (k : Fin b) : Fin n :=
  ⟨i.val / b * b + k.val, by
    have hin : i.val / b < n / b := (Nat.div_lt_iff_lt_mul hb).mpr (by simp_all [Nat.div_mul_cancel])
    calc
      i.val / b * b + k.val < i.val / b * b + b := Nat.add_lt_add_left k.isLt _
      _ = (i.val / b + 1) * b := by noncomm_ring
      _ ≤ n / b * b := Nat.mul_le_mul_right b hin
      _ = n := Nat.div_mul_cancel hbn⟩

@[simp] theorem localBlockIndex_div (hb : 0 < b) (hbn : b ∣ n)
    (i : Fin n) (k : Fin b) : (localBlockIndex hb hbn i k).val / b = i.val / b := by
  change (i.val / b * b + k.val) / b = i.val / b
  rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ hb,
    Nat.div_eq_of_lt k.isLt, Nat.zero_add]

@[simp] theorem localBlockIndex_mod (hb : 0 < b) (hbn : b ∣ n)
    (i : Fin n) (k : Fin b) : (localBlockIndex hb hbn i k).val % b = k.val := by simp_all [localBlockIndex,Nat.mod_eq_of_lt,Nat.add_mod]

end GS.GlobalGeometry
