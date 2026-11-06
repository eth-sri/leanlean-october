module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.ClusterMap

/-!
# WP-I, part 11: binary lifting, the invariants

* **Lower bound** in a sorted segment (`LbInv`): the position `pos` moves forward by `2^j` for
  `j = J - 1, …, 0` while the key at `pos + 2^j - 1` is below the target; at the end `pos` is the
  partition point (`LbInv.final`: every key before `pos` is below the target, none from `pos` on).
* **Climb** (`ClimbInv`): starting from a node `x` failing an upward-closed predicate `Good`
  whose `2^J`-th ancestor satisfies it, jump by `2^j` for `j = J - 1, …, 0` whenever the target
  still fails `Good`; at the end `x` fails `Good` and its parent satisfies it (`ClimbInv.final`).
-/

namespace Chazelle.Core.Cluster

@[expose] public section

/-! ## Lower bound -/

/-- **The invariant of the lower-bound search** at level `j`: keys before `pos` are below `x`,
and the key at `pos + 2^j - 1` (if in range) is not. -/
structure LbInv (κ : ℕ → ℕ) (lo hi x pos j : ℕ) : Prop where
  lo_le : lo ≤ pos
  le_hi : pos ≤ hi
  below : ∀ i, lo ≤ i → i < pos → κ i < x
  above : pos + 2 ^ j ≤ hi → x ≤ κ (pos + 2 ^ j - 1)

/-- Sorted keys (nondecreasing on `[lo, hi)`). -/
def Sorted (κ : ℕ → ℕ) (lo hi : ℕ) : Prop := ∀ i i', lo ≤ i → i ≤ i' → i' < hi → κ i ≤ κ i'

section
variable {κ : ℕ → ℕ}
/-- The start: `pos = lo` and `2^J > hi - lo`. -/
theorem LbInv.init {lo hi x J : ℕ} (hlh : lo ≤ hi) (hJ : hi - lo < 2 ^ J) :
    LbInv κ lo hi x lo J :=
  ⟨le_rfl, hlh, fun i h1 h2 => by omega, fun h => by omega⟩

/-- **One step** at level `j + 1 → j`: jump by `2^j` iff the jump stays in range and the key at
the new `pos - 1` is below the target. -/
theorem LbInv.step {lo hi x pos j : ℕ} (hs : Sorted κ lo hi)
    (hI : LbInv κ lo hi x pos (j + 1)) :
    (pos + 2 ^ j ≤ hi ∧ κ (pos + 2 ^ j - 1) < x → LbInv κ lo hi x (pos + 2 ^ j) j) ∧
    (¬ (pos + 2 ^ j ≤ hi ∧ κ (pos + 2 ^ j - 1) < x) → LbInv κ lo hi x pos j) := by
  have hp := Nat.one_le_two_pow (n := j)
  have hpow : 2 ^ (j + 1) = 2 ^ j + 2 ^ j := by omega
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by have := hI.lo_le; omega, h1, fun i hi1 hi2 => ?_, fun h => ?_⟩
    · by_cases hip : i < pos
      · exact hI.below i hi1 hip
      · exact lt_of_le_of_lt (hs i (pos + 2 ^ j - 1) hi1 (by omega) (by omega)) h2
    · have := hI.above (by omega)
      grind
  · intro h
    grind [Chazelle.Core.Cluster.LbInv]

/-- **The end**: at level `0`, `pos` is the partition point. -/
theorem LbInv.final {lo hi x pos : ℕ} (hs : Sorted κ lo hi)
    (hI : LbInv κ lo hi x pos 0) :
    (∀ i, lo ≤ i → i < pos → κ i < x) ∧ (∀ i, pos ≤ i → i < hi → x ≤ κ i) := by
  ram_grind

/-! ## Climb -/


end

/-- **The invariant of the climb** at level `j`: `x` fails `Good` and its `2^j`-th ancestor
satisfies it. -/
structure ClimbInv (up : ℕ → ℕ) (Good : ℕ → Prop) (x j : ℕ) : Prop where
  bad : ¬ Good x
  good : Good (up^[2 ^ j] x)

section
variable {up : ℕ → ℕ} {Good : ℕ → Prop}
/-- **One step** of the climb at level `j + 1 → j`. -/
theorem ClimbInv.step {x j : ℕ} (hI : ClimbInv up Good x (j + 1)) :
    (¬ Good (up^[2 ^ j] x) → ClimbInv up Good (up^[2 ^ j] x) j) ∧
    (Good (up^[2 ^ j] x) → ClimbInv up Good x j) := by
  constructor
  · intro h
    refine ⟨h, ?_⟩
    rw [← Function.iterate_add_apply, show 2 ^ j + 2 ^ j = 2 ^ (j + 1) by omega]
    exact hI.good
  ram_grind

/-- **The end** of the climb: `x` fails `Good`, its parent satisfies it. -/
theorem ClimbInv.final {x : ℕ} (hI : ClimbInv up Good x 0) :
    ¬ Good x ∧ Good (up x) := ⟨hI.bad, by simpa using hI.good⟩


end

end

end Chazelle.Core.Cluster
