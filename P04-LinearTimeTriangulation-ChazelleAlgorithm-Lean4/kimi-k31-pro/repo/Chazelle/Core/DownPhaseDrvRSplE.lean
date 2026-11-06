module

public import Chazelle.Core.DownPhaseDrvRSplD

/-!
# Down-phase driver (RAM side): the splice, part 4 (cost)

`splB2Cost_le`: the cost of the bucket part is `O ((n + A + 1) (⌈log₂ Mb⌉ + 1))` for buckets of
at most `Mb` codes.
-/

namespace Chazelle.Core

namespace DrvR

open Machine Machine.Stmt Programs SortL BuildRam SignK

@[expose] public section

/-- The cost of one bucket, against the bucket bound. -/
theorem bsCost_le {bk : ℕ → ℕ} {n b Mb : ℕ} (h : bcnt bk n b ≤ Mb) :
    bsCost bk n b + 2 ≤ 11047 * bcnt bk n b * (Nat.clog 2 Mb + 1) + 11054 := by
  unfold bsCost SortR.sortCost
  have hc := Nat.clog_mono_right 2 h
  have : bcnt bk n b * (Nat.clog 2 (bcnt bk n b) + 1) ≤ bcnt bk n b * (Nat.clog 2 Mb + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : bcnt bk n b ≤ bcnt bk n b * (Nat.clog 2 Mb + 1) := Nat.le_mul_of_pos_right _ (by omega)
  nlinarith

/-- **The cost of the bucket part.** -/
theorem splB2Cost_le {bk : ℕ → ℕ} {n A Mb : ℕ} (hA : ∀ q, q < n → bk q ≤ A)
    (hM : ∀ b, bcnt bk n b ≤ Mb) :
    splB2Cost bk n A ≤ 11200 * (n + A + 1) * (Nat.clog 2 Mb + 1) := by
  unfold splB2Cost
  have hsum : ∑ b ∈ Finset.range (A + 1), (bsCost bk n b + 2) ≤
      ∑ b ∈ Finset.range (A + 1), (11047 * bcnt bk n b * (Nat.clog 2 Mb + 1) + 11054) :=
    Finset.sum_le_sum fun b _ => bsCost_le (hM b)
  have e : ∑ b ∈ Finset.range (A + 1), (11047 * bcnt bk n b * (Nat.clog 2 Mb + 1) + 11054) =
      11047 * (∑ b ∈ Finset.range (A + 1), bcnt bk n b) * (Nat.clog 2 Mb + 1) + 11054 * (A + 1) := by
    simp [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
      ← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have hb : ∑ b ∈ Finset.range (A + 1), bcnt bk n b = n := bstart_all hA
  rw [e, hb] at hsum
  have h1 : 1 ≤ Nat.clog 2 Mb + 1 := by omega
  have h3 : (n + A + 1) ≤ (n + A + 1) * (Nat.clog 2 Mb + 1) := Nat.le_mul_of_pos_right _ (by omega)
  nlinarith

end

end DrvR

end Chazelle.Core
