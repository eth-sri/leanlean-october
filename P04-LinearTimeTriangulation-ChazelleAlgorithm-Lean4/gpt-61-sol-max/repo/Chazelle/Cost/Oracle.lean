module

public import Chazelle.Cost.UpPhase

/-!
# The arithmetic of Lemma 3.6 (ray-shooting oracle via planar separators, §3.4)

Lemma 3.6 (p. 516): "Let `C` be a connected vertex-to-vertex piece of the input polygonal curve
`P` and let `m` be its number of vertices.  Let `S` be a normal-form `γ`-granular conformal
submap of `V(C)`.  Then it is possible to preprocess `S` in `O(m(log m)/γ + 1)` time so that
ray-shooting within `S` can be done in time `O(γ^(1/3) m^(2/3))`."

The derivation (pp. 513–516): `S*` has `μ ≤ K(m/γ + 1)` faces (Lemma 2.3), each with `O(γ)`
edges; a query scans naively the `O(μ^(2/3))` separator regions and one cluster of at most
`μ^(2/3)` regions (`O(γμ^(2/3))` each), plus an `O(log μ)` binary search; preprocessing is
`O(μ log m)`.  If `μ = 1` the query is naive, `O(m)`.

## Main results (explicit constants, real powers `Real.rpow`)
* `oracle_query_le`: `μ ≤ K(m/γ + 1)`, `0 < γ ≤ m` ⟹ `γ μ^(2/3) ≤ (2K)^(2/3) γ^(1/3) m^(2/3)`.
* `clog_le_eight_rpow`: `⌈log₂ μ⌉ ≤ 8 μ^(2/3)` (the binary search is dominated).
* `oracle_query_total_le`: `2γμ^(2/3) + ⌈log₂ μ⌉ ≤ 10 (2K)^(2/3) γ^(1/3) m^(2/3)` for `γ ≥ 1`.
* `oracle_naive_le`: if `m ≤ K γ` (the case `μ = 1`: one face with `O(γ)` edges) then
  `m ≤ K^(1/3) γ^(1/3) m^(2/3)`.
* `oracle_prep_le`: `μ L ≤ 2K · m L / γ` for `L ≥ 0` (preprocessing `O(μ log m) = O(m log m/γ)`).
* `oracle_chain_cost_le`: in Lemma 4.1, shooting toward a chain of grade `μ ≤ ⌈βλ⌉ + 11` (with
  the revised granularity `γ ≤ 1201 · 2^⌈βμ⌉`, `m = 2^μ + 1`) costs
  `γ^(1/3) m^(2/3) ≤ 11264 · 2^(β²λ/3 + 2βλ/3)` (consolidated revision, design doc §10).
-/

namespace Chazelle.Cost

public section

/-- The binary search of the query is dominated: `⌈log₂ μ⌉ ≤ 8 μ^(2/3)` for every natural `μ`. -/
theorem clog_le_eight_rpow (μ : ℕ) : (Nat.clog 2 μ : ℝ) ≤ 8 * (μ : ℝ) ^ ((2 : ℝ) / 3) := by
  rcases Nat.lt_or_ge μ 2 with hμ | hμ
  · have : Nat.clog 2 μ = 0 := Nat.clog_of_right_le_one (by omega) 2
    rw [this, Nat.cast_zero]
    positivity
  · set k := Nat.clog 2 μ with hk
    have hlt : 2 ^ k.pred < μ := Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
    have hk1 : 1 ≤ k := by
      by_contra hcon
      
      have := Nat.le_pow_clog (b := 2) (by norm_num) μ
      grind
    -- k ≤ 4 · 2^(k/2)
    have h1 := nat_le_two_rpow 2 (by norm_num) k
    push_cast at h1
    -- 2^(k/2) ≤ 2 · 2^(2(k-1)/3)
    have h2 : (2 : ℝ) ^ ((k : ℝ) / 2) ≤ 2 * (2 : ℝ) ^ (2 * ((k : ℝ) - 1) / 3) := by
      have hk1R : (1 : ℝ) ≤ k := by simp_all
      calc (2 : ℝ) ^ ((k : ℝ) / 2) ≤ (2 : ℝ) ^ (1 + 2 * ((k : ℝ) - 1) / 3) :=
            two_rpow_le_two_rpow (by linarith)
        _ = 2 * (2 : ℝ) ^ (2 * ((k : ℝ) - 1) / 3) := by
            rw [← two_rpow_mul_two_rpow, Real.rpow_one]
    -- 2^(2(k-1)/3) ≤ μ^(2/3)
    have h3 : (2 : ℝ) ^ (2 * ((k : ℝ) - 1) / 3) ≤ (μ : ℝ) ^ ((2 : ℝ) / 3) := by
      have hpred : ((k.pred : ℕ) : ℝ) = (k : ℝ) - 1 := by
        simp_all
      have hltR : (2 : ℝ) ^ (k.pred) ≤ (μ : ℝ) := by exact_mod_cast hlt.le
      calc (2 : ℝ) ^ (2 * ((k : ℝ) - 1) / 3) = ((2 : ℝ) ^ (k.pred)) ^ ((2 : ℝ) / 3) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), hpred]
            grind
        _ ≤ (μ : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_le_rpow (by positivity) hltR (by norm_num)
    grind

end

end Chazelle.Cost
