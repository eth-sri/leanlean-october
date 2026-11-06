module

public import ThreeSumApsp.Util.Types
public import Mathlib.Tactic
public import ImprovedExponents.MinPlus.Comparison
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring.RingNF

@[expose] public section

/-!
# Min-plus products by Exact Triangle, through comparisons as equalities

Let `A`, `B` be `n × n` integer matrices with entries of absolute value at most `W`, and let `t` be
a matrix of thresholds. By `add_lt_iff_shiftDiff`, applied to `x = A i k + W`, `y = B k j + W` and
`u = t i j + 2W`, the question "is there a `k` with `A i k + B k j < t i j`?" is, for all pairs
`(i, j)` at once, the disjunction of `2b + 3` Exact Triangle questions "is there a `k` with
`wIK i k + wKJ k j + wJI j i = 0`?" (`exists_lt_iff_exists_exactTriangle`). The instances are
indexed by the pairs `(ℓ, r)` of `lemmaFInstances b`: `r = 1` at `ℓ = 0`, and `r ∈ {2, 3}` at each
`ℓ ≤ b`; the weights are `etIK`, `etKJ` and `etJI`.

The entries of the min-plus product `C i j = min_k (A i k + B k j)` (`minPlus`) are found from
these answers by a binary search that runs for all pairs in parallel: `search` makes `R` rounds
when `4W + 1 ≤ 2^R`, each round asking one matrix of thresholds (`search_eq_minPlus`,
`search_exactTriangle`).
-/

namespace ImprovedExponents

open Finset

variable {n : ℕ}

/-! ### The Exact Triangle instances -/

/-- The weight of the edge `(i, k)` in the instance of level `ℓ`: `⌊(A i k + W)/2^ℓ⌋`. -/
def etIK (A : Fin n → Fin n → ℤ) (W ℓ : ℕ) i k := (A i k + W) / 2 ^ ℓ

/-- The weight of the edge `(k, j)` in the instance of level `ℓ`: `⌊(B k j + W)/2^ℓ⌋`. -/
def etKJ (B : Fin n → Fin n → ℤ) (W ℓ : ℕ) k j := (B k j + W) / 2 ^ ℓ

/-- The weight of the edge `(j, i)` in the instance `(ℓ, r)`: `r - ⌊(t i j + 2W)/2^ℓ⌋`. -/
def etJI (t : Fin n → Fin n → ℤ) (W ℓ : ℕ) r j i :=
  r - (t i j + 2 * W) / 2 ^ ℓ

/-- The instances `(ℓ, r)`: `(0, 1)`, and `(ℓ, 2)` and `(ℓ, 3)` for `ℓ ≤ b`. -/
def lemmaFInstances (b : ℕ) : Finset (ℕ × ℤ) := insert (0, 1) (range (b + 1) ×ˢ {2, 3})

/-- The disjunction of Lemma F as a statement about the instances. -/
theorem exists_mem_lemmaFInstances_iff b (f : Light.Memory) :
    (∃ c ∈ lemmaFInstances b, f c.1 = c.2) ↔ f 0 = 1 ∨ ∃ ℓ ≤ b, f ℓ = 2 ∨ f ℓ = 3 := by
  simp_all [lemmaFInstances]

/-- Lemma F for integers `p, q` of absolute value at most `W` and a threshold `t` with
`0 ≤ t + 2W < 2^b`, where `2W < 2^b`. -/
theorem lt_iff_exists_instance {b W : ℕ} {p q t : ℤ} (hp : |p| ≤ W) (hq : |q| ≤ W)
    (hW : 2 * W < 2 ^ b) (ht : -(2 * W : ℤ) ≤ t) (ht' : t + 2 * W < 2 ^ b) :
    p + q < t ↔ ∃ c ∈ lemmaFInstances b,
      (p + W) / 2 ^ c.1 + (q + W) / 2 ^ c.1 + (c.2 - (t + 2 * W) / 2 ^ c.1) = 0 := by
  have  := abs_le.mp hp
  have  := abs_le.mp hq
  obtain ⟨x, hx⟩ := Int.eq_ofNat_of_zero_le (by linarith : 0 ≤ p + W)
  obtain ⟨y, hy⟩ := Int.eq_ofNat_of_zero_le (by linarith : 0 ≤ q + W)
  obtain ⟨u, hu⟩ := Int.eq_ofNat_of_zero_le (by linarith : 0 ≤ t + 2 * W)





  rw [(by omega : p + q < t ↔ x + y < u), add_lt_iff_shiftDiff (by
    omega
  ) (by
    omega
  ) (by
    grind
   : u < 2 ^ b), ← exists_mem_lemmaFInstances_iff, hx, hy, hu]
  refine exists_congr fun c => and_congr_right fun _ => ?_
  simp_all [shiftDiff] <;> omega

/-- **Lemma F for matrices: threshold questions as Exact Triangle instances.** Let `A`, `B` have
entries of absolute value at most `W`, let `2W < 2^b`, and let the thresholds satisfy
`-2W ≤ t i j` and `t i j + 2W < 2^b`. Then there is a `k` with `A i k + B k j < t i j` if and only
if, in one of the `2b + 3` instances `(ℓ, r)`, there is a `k` whose triangle `i, k, j` has weight
`0`. The weights of an instance depend on `(A, ℓ)`, `(B, ℓ)` and `(t, ℓ, r)` only. -/
theorem exists_lt_iff_exists_exactTriangle (A B t : Fin n → Fin n → ℤ) {W b : ℕ}
    (hA : ∀ i k, |A i k| ≤ W) (hB : ∀ k j, |B k j| ≤ W) (hW : 2 * W < 2 ^ b)
    (ht : ∀ i j, -2 * W ≤ t i j ∧ t i j + 2 * W < 2 ^ b) i j :
    (∃ k, A i k + B k j < t i j) ↔ ∃ c ∈ lemmaFInstances b,
      ∃ k, etIK A W c.1 i k + etKJ B W c.1 k j + etJI t W c.1 c.2 j i = 0 := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨c, hc, h⟩ :=
      (lt_iff_exists_instance (hA i k) (hB k j) hW (ht i j).1 (ht i j).2).mp hk
    exact ⟨c, hc, k, h⟩
  · rintro ⟨c, hc, k, h⟩
    exact ⟨k, (lt_iff_exists_instance (hA i k) (hB k j) hW (ht i j).1 (ht i j).2).mpr
      ⟨c, hc, h⟩⟩

/-! ### The min-plus product and the binary search -/

end ImprovedExponents
