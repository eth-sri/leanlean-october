module
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

@[expose] public section
/-!
# The plastic number

`plasticNumber` is the unique real root `> 1` of `x³ − x − 1`.  Existence is the intermediate
value theorem on `[1, 2]` (the cubic is `−1` at `1` and `5` at `2`); uniqueness holds because
`x³ − x` is strictly increasing on `[1, ∞)` (in fact the cubic has no other real root at all,
`plasticNumber_unique'`).
-/

namespace CoxeterGrowth

theorem exists_plastic_root : ∃ x ∈ Set.Icc (1 : ℝ) 2, x ^ 3 - x - 1 = 0 := by
  have h := intermediate_value_Icc (by norm_num : (1 : ℝ) ≤ 2)
    (show ContinuousOn (fun x : ℝ => x ^ 3 - x - 1) (Set.Icc 1 2) by fun_prop)
  exact h (by constructor <;> norm_num)

theorem plastic_unique {x y : ℝ} (hx : 1 < x) (hy : 1 < y)
    (h : x ^ 3 = x + 1) (h' : y ^ 3 = y + 1) : x = y := by
  have key : (x - y) * (x ^ 2 + x * y + y ^ 2 - 1) = 0 := by
    calc _ = (x ^ 3 - x) - (y ^ 3 - y) := by ring
      _ = 0 := by rw [h, h']; ring
  rcases mul_eq_zero.1 key with h0 | h0
  · linarith
  · nlinarith

theorem plastic_exists_unique : ∃! ρ : ℝ, 1 < ρ ∧ ρ ^ 3 = ρ + 1 := by
  obtain ⟨x, hx, h3⟩ := exists_plastic_root
  have h1 : 1 < x := by
    rcases hx.1.lt_or_eq with h | h
    · exact h
    · rw [← h] at h3; norm_num at h3
  exact ⟨x, ⟨h1, by linarith⟩, fun y hy =>
    plastic_unique hy.1 h1 (by linarith [hy.2]) (by linarith [h3])⟩

end CoxeterGrowth
