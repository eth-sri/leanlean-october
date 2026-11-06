
import ImprovedExponents.Pipeline.HostBound


/-!
# The solver of Lop-AE-SparseTri from a thin-product claim

Corollary 16 for arbitrary exponents: "This is Corollary 26 with N = n, applied to the two
biadjacency matrices". The matrices have entries 0 and 1; writing them down and copying the answers
costs `O(nD + w + 1)`, and telling which counts are nonzero `O(w + 1)`. Both are absorbed by the
bound `n² (log D + 1)²/D^γ + w D^q (log D + 1)` when `D ≤ n^ε` with `ε (1 + γ) ≤ 1`, because then
`D^{1+γ} ≤ n`, that is `n D ≤ n²/D^γ`.
-/

namespace ImprovedExponents

open ThreeSumApsp Light.Sec4

variable {ε γ : ℝ}

/-- For `1 ≤ D ≤ n^ε` with `ε (1 + γ) ≤ 1`, the size `n D` of the two matrices is at most the bound
on the preprocessing. -/
theorem mul_le_preBound31 {n D : ℕ} (hn : 1 ≤ n) (hD : 1 ≤ D) (hγ : 0 ≤ γ)
    (hε : ε * (1 + γ) ≤ 1) (hDn : (D : ℝ) ≤ (n : ℝ) ^ ε) :
    (n : ℝ) * D ≤ preBound31 γ n D := by
  have hNR : (1 : ℝ) ≤ n := by simp_all
  have hDR : (1 : ℝ) ≤ D := by simp_all
  have hpow : (D : ℝ) ^ (1 + γ) ≤ n := by
    calc D ^ (1 + γ) ≤ ((n : ℝ) ^ ε) ^ (1 + γ) :=
          by grind [Real.rpow_le_rpow]
      _ = n ^ (ε * (1 + γ)) := by grind [Real.rpow_mul]
      _ ≤ n ^ 1 := Real.rpow_le_rpow_of_exponent_le hNR hε
      _ = n := Real.rpow_one _
  have hsplit : D ^ (1 + γ) = D * (D : ℝ) ^ γ := by grind [Real.rpow_add, Real.rpow_one]
  have hlog := Real.log_nonneg hDR
  have hDγ : 0 < (D : ℝ) ^ γ := by positivity
  rw [preBound31, le_div_iff₀ hDγ]
  calc n * D * D ^ γ = n * (D * (D : ℝ) ^ γ) := by ring
    _ ≤ n * n := by grind [mul_le_mul_of_nonneg_left]
    _ = n ^ 2 * 1 := by ring
    _ ≤ n ^ 2 * (Real.log D + 1) ^ 2 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ (by linarith)) (by positivity)

/-- **Corollary 16 for arbitrary exponents**: a thin-product claim gives a solver of
Lop-AE-SparseTri with the same bound, by the two transfer claims of the proof of Corollary 15. -/
theorem lopClaim_of_thinClaim (M : DetTimeModel) {q : ℝ} (hγ : 0 ≤ γ) (hq : 0 ≤ q)
    (hε : ε * (1 + γ) ≤ 1) (h : ThinClaim M ε γ q) (hlop : Claim.LopCountFromThinProduct M)
    (hdet : Claim.LopDetectFromCount M) : LopClaim M ε γ q := by
  obtain ⟨C, T, hT, hb⟩ := h
  obtain ⟨C₁, hlop⟩ := hlop
  obtain ⟨C₃, hdet⟩ := hdet
  refine ⟨|C| + 2 * |C₁| + |C₃|, _, by aesop, fun n D w hn hD hDn => ?_⟩
  have hNR : (1 : ℝ) ≤ n := by simp_all
  have hDR : (1 : ℝ) ≤ D := by simp_all
  have hnD1 := one_le_mul_of_one_le_of_one_le hNR hDR
  have hnD := mul_le_preBound31 hn hD hγ hε hDn
  have hw0 : (0 : ℝ) ≤ w := Nat.cast_nonneg _
  have hwq := le_mul_of_one_le_right hw0 (one_le_queryBound31 hD hq)
  have hB0 : 0 ≤ preBound31 γ n D + w * queryBound31 q D := by linarith
  have h1 :=
    (hb n D w 1 hn hD hDn).trans (mul_le_mul_of_nonneg_right (le_abs_self C) hB0)
  have h2 : C₁ * (n * D + w + 1)
      ≤ |C₁| * (2 * (preBound31 γ n D + w * queryBound31 q D)) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C₁) (by linarith)).trans
      (by grind [mul_le_mul_of_nonneg_left, abs_nonneg])
  have h3 : C₃ * (w + 1) ≤ |C₃| * (preBound31 γ n D + w * queryBound31 q D) :=
    (mul_le_mul_of_nonneg_right (le_abs_self C₃) (by linarith)).trans
      (by grind [mul_le_mul_of_nonneg_left, abs_nonneg])
  linarith
