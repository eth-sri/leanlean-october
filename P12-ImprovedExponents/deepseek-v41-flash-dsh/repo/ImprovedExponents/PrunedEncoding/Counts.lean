module

public import PaperStatements
public import ThreeSumApsp.TacticsShort

@[expose] public section

/-!
# Pruned encodings: the sizes of the staged arrays

The encodings `Φ_τ(a)` of an array `a` on the left strings of length `L` are computed by Yates'
algorithm, one level at a time. The pruned algorithm keeps, at stage `k`, only the entries indexed
by a string of `k` terms with at most `m` symbols `P₀` followed by a string of `L - k` left
variables with at most `m` inner variables. This file has the numbers of such strings,

* `prefCount k m = ∑_{j ≤ m} C(k, j) 9^{k-j}` and
* `sufCount n m = ∑_{i ≤ m} C(n, i) 4^i 3^{n-i}`,

and the bounds on them: `9 prefCount k m ≤ prefCount (k+1) m`, `sufCount (n+1) m ≤ 7 sufCount n m`,
hence `∑_k prefCount k m * sufCount (L-k) m ≤ (9/2) prefCount L m`, and
`prefCount L m ≤ M/(1 - ρ)` for `10 m ≤ L`, where `M = C(L, m) 9^{L-m}` and `ρ = 9m/(L-m+1)`.
-/

namespace ImprovedExponents

open Finset ThreeSumApsp

/-- `prefCount k m = ∑_{j ≤ m} C(k, j) 9^{k-j}`: the number of strings of `k` terms with at most
`m` symbols `P₀` (see `card_termStrings`). -/
def prefCount (k m : ℕ) : ℕ := ∑ j ∈ range (m + 1), k.choose j * 9 ^ (k - j)

/-- A string of terms that is longer by one symbol can be chosen in at least `9` times as many
ways: `9 |P_k| ≤ |P_{k+1}|`. -/
theorem nine_mul_prefCount_le (k m : ℕ) : 9 * prefCount k m ≤ prefCount (k + 1) m := by
  unfold prefCount
  rw [mul_sum]
  refine sum_le_sum fun j _ => ?_
  rcases Nat.lt_or_ge k j with hj | hj
  · simp [Nat.choose_eq_zero_of_lt hj]
  · have h1 : k + 1 - j = (k - j) + 1 := by omega
    rw [h1, pow_succ]
    nlinarith [Nat.choose_le_succ k j, Nat.zero_le (9 ^ (k - j)),
      Nat.mul_le_mul_right (9 ^ (k - j)) (Nat.choose_le_succ k j)]

/-- `9^d |P_k| ≤ |P_{k+d}|`. -/
theorem pow_mul_prefCount_le (k d m : ℕ) : 9 ^ d * prefCount k m ≤ prefCount (k + d) m := by
  induction d with
  | zero => simp
  | succ d ih => calc
      9 ^ (d + 1) * prefCount k m = 9 * (9 ^ d * prefCount k m) := by ring
      _ ≤ 9 * prefCount (k + d) m := by gcongr
      _ ≤ prefCount (k + d + 1) m := nine_mul_prefCount_le _ _

/-- The last term of `prefCount L m` is `M = C(L, m) 9^{L-m}`. -/
theorem M_eq_choose_mul (L m : ℕ) : M L m = L.choose m * 9 ^ (L - m) := by
  unfold M K N0
  rw [← pow_mul, mul_comm (L - m) 2, pow_mul]
  norm_num

/-- The ratio of consecutive terms of `prefCount L m`:
`(L - j) C(L, j) 9^{L-j} = 9 (j+1) C(L, j+1) 9^{L-(j+1)}`. -/
theorem prefCount_term_ratio (L j : ℕ) :
    (L - j) * (L.choose j * 9 ^ (L - j))
      = 9 * (j + 1) * (L.choose (j + 1) * 9 ^ (L - (j + 1))) := by
  rcases Nat.lt_or_ge j L with hj | hj
  · have h1 : L - j = (L - (j + 1)) + 1 := by omega
    have h2 := Nat.choose_succ_right_eq L j
    rw [h1, pow_succ, ← h1]
    calc (L - j) * (L.choose j * (9 ^ (L - (j + 1)) * 9))
        = 9 * (L.choose j * (L - j)) * 9 ^ (L - (j + 1)) := by ring
      _ = 9 * (L.choose (j + 1) * (j + 1)) * 9 ^ (L - (j + 1)) := by rw [h2]
      _ = 9 * (j + 1) * (L.choose (j + 1) * 9 ^ (L - (j + 1))) := by ring
  · rw [Nat.sub_eq_zero_of_le hj, Nat.choose_eq_zero_of_lt (by omega : L < j + 1)]
    simp

/-- The terms of `prefCount L m` decay at rate `ρ = 9m/(L-m+1)` below the last one, so the sum is
at most `1/(1 - ρ)` times the last term. Without fractions:
`(L - m + 1 - 9m) ∑_{i ≤ j} C(L, i) 9^{L-i} ≤ (L - m + 1) C(L, j) 9^{L-j}` for `j ≤ m`. -/
theorem sub_mul_prefCount_le_aux (L m : ℕ) (h : 9 * m ≤ L - m + 1) :
    ∀ j ≤ m, (L - m + 1 - 9 * m) * prefCount L j ≤ (L - m + 1) * (L.choose j * 9 ^ (L - j)) := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [prefCount, zero_add, range_one, sum_singleton]
    exact Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  | succ j ih =>
    intro hj
    have ih' := ih tac_omega
    have hratio := prefCount_term_ratio L j
    have hstep := calc
      (L - m + 1) * (L.choose j * 9 ^ (L - j)) ≤ (L - j) * (L.choose j * 9 ^ (L - j)) :=
        Nat.mul_le_mul_right _ tac_omega
      _ = 9 * (j + 1) * (L.choose (j + 1) * 9 ^ (L - (j + 1))) := hratio
      _ ≤ 9 * m * (L.choose (j + 1) * 9 ^ (L - (j + 1))) :=
        Nat.mul_le_mul_right _ tac_omega
    have hsplit : prefCount L (j + 1)
        = prefCount L j + L.choose (j + 1) * 9 ^ (L - (j + 1)) := by
      unfold prefCount
      rw [sum_range_succ]
    rw [hsplit, mul_add]
    calc (L - m + 1 - 9 * m) * prefCount L j
          + (L - m + 1 - 9 * m) * (L.choose (j + 1) * 9 ^ (L - (j + 1)))
        ≤ 9 * m * (L.choose (j + 1) * 9 ^ (L - (j + 1)))
          + (L - m + 1 - 9 * m) * (L.choose (j + 1) * 9 ^ (L - (j + 1))) :=
          Nat.add_le_add_right (ih'.trans hstep) _
      _ = (L - m + 1) * (L.choose (j + 1) * 9 ^ (L - (j + 1))) := by
          rw [← add_mul, Nat.add_sub_cancel' h]

/-- `|P_L| ≤ M/(1 - ρ)` without fractions: `(L - m + 1 - 9m) |P_L| ≤ (L - m + 1) M` for
`10 m ≤ L`. (Here `L - m + 1 - 9m` is positive.) -/
theorem sub_mul_prefCount_le {L m : ℕ} (h : 10 * m ≤ L) :
    (L - m + 1 - 9 * m) * prefCount L m ≤ (L - m + 1) * M L m := by
  rw [M_eq_choose_mul]
  exact sub_mul_prefCount_le_aux L m tac_omega m le_rfl

/-- `|P_L| ≤ M/(1 - ρ)` for `10 m ≤ L`: the number of leaves with at most `m` symbols `P₀`. -/
theorem prefCount_le_M_div {L m : ℕ} (h : 10 * m ≤ L) :
    (prefCount L m : ℝ) ≤ (M L m : ℝ) / (1 - rho L m) := by
  have h' : (10 : ℝ) * m ≤ L := by exact_mod_cast h
  have hnat := sub_mul_prefCount_le h
  have hcast : ((L : ℝ) - m + 1 - 9 * m) * prefCount L m ≤ ((L : ℝ) - m + 1) * M L m := by
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub tac_omega, Nat.cast_add, Nat.cast_sub tac_omega]
      at this
    simpa using this
  have hpos : (0 : ℝ) < (L : ℝ) - m + 1 := by linarith
  have hrho : 1 - rho L m = ((L : ℝ) - m + 1 - 9 * m) / ((L : ℝ) - m + 1) := by
    unfold rho
    field_simp
  rw [hrho, div_div_eq_mul_div, le_div_iff₀ tac_linarith]
  linarith

end ImprovedExponents