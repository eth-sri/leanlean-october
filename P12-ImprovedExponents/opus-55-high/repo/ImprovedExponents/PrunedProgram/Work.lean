
import ImprovedExponents.PrunedEncoding.Counts


/-!
# The work of the pruned encoder

The pruned encoder (`ImprovedExponents.PrunedProgram.Encode`) is upstream's recursive encoder with a
budget of symbols `P₀`: below a vertex with `k` terms it forms the ten slices of `7^{L-k}` entries
each, but it does not enter the term `P₀` once `m` of them have been used.  So it visits the
vertices with at most `m` symbols `P₀` only, `prefCount k m` of them at depth `k`, and its work is

  `encWorkP L m = ∑_{k ≤ L} prefCount k m · 7^{L-k}`

up to a constant.  Since `9 |P_k| ≤ |P_{k+1}|` (`nine_mul_prefCount_le`), the summands decay like
`(7/9)^{L-k}` from the last one, so the work is at most `(9/2) |P_L|` (`encWorkP_le`) and at most
`(9/2) M/(1 - ρ)` (`encWorkP_le_M_div`), as the paper's count of the pruned recursion.
-/

namespace ImprovedExponents

open Finset ThreeSumApsp

/-- The work of the pruned encoder on one band: the number of entries of all the slices it forms,
`∑_{k ≤ L} |P_k| 7^{L-k}`. -/
def encWorkP (L m : ℕ) : ℕ := ∑ k ∈ range (L + 1), prefCount k m * 7 ^ (L - k)

/-- `∑_{d < n} (7/9)^d = (9/2)(1 - (7/9)^n)`. -/
theorem geom_sum_seven_ninths_real (n : ℕ) :
    ∑ d ∈ range n, ((7 : ℝ) / 9) ^ d = 9 / 2 * (1 - (7 / 9) ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => grind [sum_range_succ]

/-- The work of the pruned encoder is at most `(9/2) |P_L|`. -/
theorem encWorkP_le (L m : ℕ) : (encWorkP L m : ℝ) ≤ 9 / 2 * prefCount L m := by
  have hterm : ∀ k ∈ range (L + 1),
      (prefCount k m * 7 ^ (L - k) : ℕ) ≤ prefCount L m * ((7 : ℝ) / 9) ^ (L - k) := by
    intro k hk
    have hk' : k ≤ L := by simp_all
    have h := pow_mul_prefCount_le k (L - k) m
    rw [Nat.add_sub_cancel' hk'] at h
    have h' : (9 : ℝ) ^ (L - k) * prefCount k m ≤ prefCount L m := by exact_mod_cast h
    have h7 : (0 : ℝ) < 7 ^ (L - k) := by positivity
    have h9 : (0 : ℝ) < 9 ^ (L - k) := by positivity
    push_cast
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ h9]
    nlinarith
  have hsum : ∑ k ∈ range (L + 1), ((7 : ℝ) / 9) ^ (L - k) ≤ 9 / 2 := by
    have hrefl : ∑ k ∈ range (L + 1), (7 / 9) ^ (L - k)
        = ∑ d ∈ range (L + 1), ((7 : ℝ) / 9) ^ d := by
      grind [sum_range_reflect]
    rw [hrefl, geom_sum_seven_ninths_real]
    norm_num
  calc encWorkP L m = ∑ k ∈ range _, ((prefCount k m * 7 ^ (L - k) : ℕ) : ℝ) := by
        unfold encWorkP; simp
    _ ≤ ∑ k ∈ range _, prefCount L m * ((7 : ℝ) / 9) ^ (L - k) := sum_le_sum hterm
    _ = prefCount L m * ∑ k ∈ range _, (7 / 9) ^ (L - k) := by rw [mul_sum]
    _ ≤ prefCount L m * (9 / 2) := by gcongr
    _ = 9 / 2 * prefCount L m := by ring

/-- The work of the pruned encoder is at most `(9/2) M/(1 - ρ)` for `10 m ≤ L`. -/
theorem encWorkP_le_M_div {L m : ℕ} (h : 10 * m ≤ L) :
    (encWorkP L m : ℝ) ≤ 9 / 2 * (M L m : ℝ) / (1 - rho L m) := by
  grind [encWorkP_le, prefCount_le_M_div]

/-- `7^L ≤ encWorkP L m`: the slice at the root alone. -/
theorem pow_seven_le_encWorkP (L m : ℕ) : 7 ^ L ≤ encWorkP L m := by
  calc 7 ^ L = prefCount 0 m * 7 ^ L - 0 := by
        simp [prefCount, sum_range_succ']
    _ ≤ ∑ k ∈ range _, prefCount k m * 7 ^ (L - k) :=
      single_le_sum (f := fun k => prefCount k m * 7 ^ (L - k)) (by omega)
        (by simp)
