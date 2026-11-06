module

public import GradedNear.Defs

/-!
# Basic identities for the graded near lemma

* `primeSum` as a finite sum over `1 ≤ n ≤ q^X` when the test function vanishes on `[X, ∞)`;
* the factorization `n^{-((A:ℝ) + iγ)} = e^{-A log n} e^{-iγ log n}`;
* a weighted Cauchy–Schwarz inequality for finite sums.
-/

@[expose] public section

open Complex
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GradedNear

/-- `t_n = log n / log q`. -/
def tn (q n : ℕ) : ℝ := Real.log n / Real.log q

lemma log_q_pos {q : ℕ} (hq : 2 ≤ q) : 0 < Real.log q :=
  Real.log_pos (mod_cast (show 1 < q by omega))

lemma tn_nonneg (q n : ℕ) (hq : 2 ≤ q) : 0 ≤ tn q n :=
  div_nonneg (Real.log_natCast_nonneg n) (log_q_pos hq).le

/-- For `n ≥ 1` and real `A, γ`: `n^{-(A + iγ)} = e^{-A log n} · e^{-i γ log n}`. -/
lemma natCast_cpow_neg {n : ℕ} (hn : n ≠ 0) (A γ : ℝ) :
    (n : ℂ) ^ (-((A : ℂ) + (γ : ℂ) * I)) =
      (Real.exp (-A * Real.log n) : ℂ) * cexp (-((γ * Real.log n : ℝ) : ℂ) * I) := by
  have hn' : (n : ℂ) ≠ 0 := mod_cast hn
  rw [cpow_def_of_ne_zero hn', ← natCast_log, ofReal_exp, ← Complex.exp_add]
  push_cast
  ring

/-- Indices beyond `q^X` have `t_n ≥ X`. -/
lemma tn_ge_of_gt {q n : ℕ} (hq : 2 ≤ q) {X : ℝ} (hn : ⌊(q : ℝ) ^ X⌋₊ < n) : X ≤ tn q n := by
  have hq0 : (0 : ℝ) < q := by positivity
  rw [tn, le_div_iff₀ (log_q_pos hq), ← Real.log_rpow hq0]
  exact Real.log_le_log (Real.rpow_pos_of_pos hq0 X) (Nat.lt_of_floor_lt hn).le

/-- `primeSum` is a finite sum when the test function vanishes on `[X, ∞)`. -/
lemma primeSum_eq_sum {q : ℕ} (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q) (f : ℝ → ℝ) {X : ℝ}
    (hf : ∀ t, X ≤ t → f t = 0) (s : ℂ) :
    primeSum χ f s = ∑ n ∈ Finset.Icc 1 ⌊(q : ℝ) ^ X⌋₊,
      (Λ n : ℂ) * χ n * (n : ℂ) ^ (-s) * (f (tn q n) : ℂ) := by
  refine tsum_eq_sum fun n hn => ?_
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp
  simp at hn
  simp [show f (Real.log n / Real.log q) = 0 from hf _ (tn_ge_of_gt hq (hn h))]

/-- Weighted Cauchy–Schwarz: `(Σ |c_n| y_n)² ≤ (Σ c_n²/w_n)(Σ w_n y_n²)` when `w ≥ 0`
and `c_n ≠ 0 → w_n > 0`. -/
lemma weighted_cs {β : Type*} (N : Finset β) (c w y : β → ℝ) (hw : ∀ n ∈ N, 0 ≤ w n)
    (hcw : ∀ n ∈ N, c n ≠ 0 → 0 < w n) :
    (∑ n ∈ N, |c n| * y n) ^ 2 ≤ (∑ n ∈ N, c n ^ 2 / w n) * (∑ n ∈ N, w n * y n ^ 2) := by
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun n hn => div_nonneg (sq_nonneg _)
    (hw n hn)) (fun n hn => mul_nonneg (hw n hn) (sq_nonneg _)) fun n hn => ?_
  by_cases hc : c n = 0
  · simp_all
  grind [mul_comm]

end GradedNear
