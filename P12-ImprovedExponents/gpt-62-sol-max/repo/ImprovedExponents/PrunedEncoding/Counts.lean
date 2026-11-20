module

public import PaperStatements

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
  · grind
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
    grind
  grind

/-- The terms of `prefCount L m` decay at rate `ρ = 9m/(L-m+1)` below the last one, so the sum is
at most `1/(1 - ρ)` times the last term. Without fractions:
`(L - m + 1 - 9m) ∑_{i ≤ j} C(L, i) 9^{L-i} ≤ (L - m + 1) C(L, j) 9^{L-j}` for `j ≤ m`. -/
theorem sub_mul_prefCount_le_aux (L m : ℕ) (h : 9 * m ≤ L - m + 1) :
    ∀ j ≤ m, (L - m + 1 - 9 * m) * prefCount L j ≤ (L - m + 1) * (L.choose j * 9 ^ (L - j)) := by
  let a k := L.choose k * 9 ^ (L - k)
  intro j hj
  change (L - m + 1 - 9 * m) * ∑ k ∈ range (j + 1), a k ≤ (L - m + 1) * a j
  induction j with
  | zero =>
    simpa only [Nat.zero_add, sum_range_one] using Nat.mul_le_mul_right (a 0) (Nat.sub_le ..)
  | succ j ih =>
    have hstep : (L - m + 1) * a j ≤ 9 * m * a (j + 1) :=
      (Nat.mul_le_mul_right _ (show L - m + 1 ≤ L - j by omega)).trans
        ((prefCount_term_ratio L j).le.trans (Nat.mul_le_mul_right _ (by omega)))
    rw [sum_range_succ, mul_add]
    apply (Nat.add_le_add_right ((ih (by omega)).trans hstep) _).trans
    rw [← add_mul, Nat.add_sub_cancel' h]

/-- `|P_L| ≤ M/(1 - ρ)` without fractions: `(L - m + 1 - 9m) |P_L| ≤ (L - m + 1) M` for
`10 m ≤ L`. (Here `L - m + 1 - 9m` is positive.) -/
theorem sub_mul_prefCount_le {L m : ℕ} (h : 10 * m ≤ L) :
    (L - m + 1 - 9 * m) * prefCount L m ≤ (L - m + 1) * M L m := by
  rw [M_eq_choose_mul]
  exact sub_mul_prefCount_le_aux L m (by omega) m le_rfl

/-- `|P_L| ≤ M/(1 - ρ)` for `10 m ≤ L`: the number of leaves with at most `m` symbols `P₀`. -/
theorem prefCount_le_M_div {L m : ℕ} (h : 10 * m ≤ L) :
    (prefCount L m : ℝ) ≤ (M L m : ℝ) / (1 - rho L m) := by
  have h' : (10 : ℝ) * m ≤ L := by exact_mod_cast h
  have hnat := sub_mul_prefCount_le h
  have hcast : ((L : ℝ) - m + 1 - 9 * m) * prefCount L m ≤ ((L : ℝ) - m + 1) * M L m := by
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_sub (by omega)]
      at this
    simp_all
  have hpos : (0 : ℝ) < (L : ℝ) - m + 1 := by linarith
  have hrho : 1 - rho L m = ((L : ℝ) - m + 1 - 9 * m) / ((L : ℝ) - m + 1) := by
    unfold rho
    field_simp
  rw [hrho, div_div_eq_mul_div, le_div_iff₀ (by linarith)]
  linarith

end ImprovedExponents
