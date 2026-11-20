module

public import PottsDiscontinuity.SixVertex.InfinityLiftedChoices

/-! # Integer endpoint lifts of admissible defect choices -/

@[expose] public section

open Finset

namespace PottsDiscontinuity.SixVertex

variable {N : ℕ}

variable {x : Finset (Fin N)} (hN : 0 < N) (hx : NoConsecutiveUp x)
    (d : Fin (defects x).card → Bool) (ha : AdmissibleDefectChoice (indexedDefectChoice d))
    (a : Fin (defects x).card)

theorem prv_val_zero {i : Fin N} (hi : i.val = 0) : (prv i).val + 1 = N := by
  cases N with
  | zero => exact Fin.elim0 i
  | succ k =>
    simp_all

end PottsDiscontinuity.SixVertex
