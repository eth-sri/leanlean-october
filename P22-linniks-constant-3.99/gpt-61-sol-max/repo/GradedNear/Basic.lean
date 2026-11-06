import GradedNear.Tactics

import GradedNear.Defs

/-!
# Basic identities for the graded near lemma

* `primeSum` as a finite sum over `1 ≤ n ≤ q^X` when the test function vanishes on `[X, ∞)`;
* the factorization `n^{-((A:ℝ) + iγ)} = e^{-A log n} e^{-iγ log n}`;
* a weighted Cauchy–Schwarz inequality for finite sums.
-/

open Complex
open scoped ArithmeticFunction.vonMangoldt

namespace GradedNear

/-- `t_n = log n / log q`. -/
noncomputable def tn (q n : ℕ) : ℝ := Real.log n / Real.log q

lemma log_q_pos {q : ℕ} (hq : 2 ≤ q) : 0 < Real.log q :=
  Real.log_pos (by aesop)

/-- The power at an anchored Gram point splits into the real weight and its phase. -/
lemma natCast_cpow_anchor {q n : ℕ} (hn : n ≠ 0) (σ γ : ℝ) :
    ↑n ^ (- testPoint q σ γ ) =
      ((Real.exp (σ * tn q n) / n : ℝ) : ℂ) *
        cexp (-↑(γ * Real.log n) * I) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast hn), ← natCast_log, ofReal_div,
    ofReal_exp, ofReal_natCast, ← Complex.exp_log (x := (n : ℂ)) (by exact_mod_cast hn), ← Complex.exp_sub,
    ← Complex.exp_add]
  unfold tn
  push_cast

  ring

/-- `primeSum` is a finite sum when the test function vanishes on `[X, ∞)`. -/
lemma primeSum_eq_sum {q : ℕ} (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q) (f : ℝ → ℝ) {X : ℝ}
    (hf : ∀ t, X ≤ t → f t = 0) (s : ℂ) {N : ℕ}
    (hN : ⌊(q : ℝ) ^ X⌋₊ ≤ N) :
    primeSum χ f s = ∑ n ∈ Finset.Icc 1 N,
      ↑(Λ n) * χ n * ↑n ^ (-s) * ↑(f (tn q n)) := by
  unfold primeSum
  rw [tsum_eq_sum (s := Finset.Icc 1 N)]
  · rfl
  · intro n hn
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with hn | hn
    · simp_all
    · have := hf _ (le_of_lt ((lt_div_iff₀ (log_q_pos hq)).mpr
        (Real.lt_log_of_rpow_lt (by positivity) (Nat.lt_of_floor_lt (hN.trans_lt hn)))))
      aesop

end GradedNear
