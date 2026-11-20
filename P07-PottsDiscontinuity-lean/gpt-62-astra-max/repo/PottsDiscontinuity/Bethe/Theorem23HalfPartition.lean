module

public import PottsDiscontinuity.Bethe.AsymptoticPartition
public import PottsDiscontinuity.Bethe.DiscreteJacobian

/-! # The half-root partition and its endpoints -/

@[expose] public section

open Set

namespace PottsDiscontinuity.Bethe

variable {n : ℕ} (hn : 2 ≤ n)

include hn in
/-- The first half of the root partition, including the next root after it. -/
def discreteHalfPartitionIndex (j : Fin (n / 2 + 1)) : Fin n :=
  ⟨j.val, by omega⟩

/-- The last point of the half partition is nonnegative and is within one
mesh width of zero. This includes both parities of the root count. -/
theorem discreteHalfPartition_endpoint
    (p : Fin n → ℝ) (hp : p ∈ S_n n) {d : ℝ}
    (hmesh : ∀ j : Fin (n / 2), p (discreteHalfNextIndex j) -
      p (discreteHalfIndex j) ≤ d) :
    0 ≤ p (discreteHalfPartitionIndex hn (Fin.last (n / 2))) ∧
    p (discreteHalfPartitionIndex hn (Fin.last (n / 2))) ≤ d := by
  let e := discreteHalfPartitionIndex hn (Fin.last (n / 2))
  have hrev : Fin.rev e ≤ e := by
    change (Fin.rev e).val ≤ e.val
    simp only [Fin.val_rev, e, discreteHalfPartitionIndex, Fin.val_mk, Fin.val_last]
    omega
  have he := hp.2.1.monotone hrev
  rw [hp.2.2 e] at he
  have hpos : 0 ≤ p e := by linarith
  let j : Fin (n / 2) := ⟨n / 2 - 1, by omega⟩
  have hnext : discreteHalfNextIndex j = e := by
    apply Fin.ext
    change n / 2 - 1 + 1 = n / 2
    omega
  have hneg := discreteS_n_half_coord_neg hp j
  grind

/-- Every interior root gap is a cell of the cyclic partition. -/
theorem discreteHalf_gap_le_of_cyclic_mesh {hn : 0 < n}
    (p : Fin n → ℝ) {d : ℝ}
    (hmesh : ∀ j : Fin (n + 1),
      rootPartitionPoint p hn j.succ - rootPartitionPoint p hn j.castSucc ≤ d)
    (j : Fin (n / 2)) :
    p (discreteHalfNextIndex j) - p (discreteHalfIndex j) ≤ d := by
  let cell : Fin (n + 1) := ⟨j.val + 1, by omega⟩
  have ha : rootPartitionPoint p hn cell.castSucc = p (discreteHalfIndex j) := by
    convert rootPartitionPoint_root p hn (discreteHalfIndex j) using 1
    congr 1
  have hb : rootPartitionPoint p hn cell.succ = p (discreteHalfNextIndex j) := by
    convert rootPartitionPoint_root p hn (discreteHalfNextIndex j) using 1
    congr 1
  grind

end PottsDiscontinuity.Bethe
