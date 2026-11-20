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

open MeasureTheory Set in
/-- Truncate a half-line integral where its integrand vanishes. -/
lemma truncate_Ioi {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {F : ℝ → V} {X : ℝ}
    (h : ∀ t ≥ X, F t = 0) : ∫ t in Ioi 0, F t = ∫ t in Ioc 0 X, F t :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    fun t ht => h t (by grind)

open Filter in
lemma log_level_atTop : Tendsto (fun q : ℕ => Real.log q) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- The prime mass and the detector amplitude in the two Cauchy–Schwarz factors. -/
abbrev primeMass (n : ℕ) : ℝ := Λ n / n

@[simp, bound] lemma primeMass_nonneg (n : ℕ) : 0 ≤ primeMass n :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)

def amplitude (D : NearData) (t : ℝ) := Real.exp (D.s*t) * D.f t

lemma amplitude_sq (D : NearData) (t : ℝ) : amplitude D t ^ 2 = Real.exp (2*D.s*t) * D.f t ^ 2 := by
  rw [amplitude, mul_pow, ← Real.exp_nat_mul]; congr 2; ring

/-- `t_n = log n / log q`. -/
def tn (q n : ℕ) : ℝ := Real.log n / Real.log q

lemma log_q_pos {q : ℕ} (hq : 2 ≤ q) : 0 < Real.log q :=
  Real.log_pos (by exact_mod_cast hq)

lemma tn_nonneg (q n : ℕ) (hq : 2 ≤ q) : 0 ≤ tn q n :=
  div_nonneg (Real.log_natCast_nonneg n) (log_q_pos hq).le

/-- For `n ≥ 1` and real `A, γ`: `n^{-(A + iγ)} = e^{-A log n} · e^{-i γ log n}`. -/
lemma natCast_cpow_neg {n : ℕ} (hn : n ≠ 0) (A γ : ℝ) :
    (n : ℂ) ^ (-xy[A, γ]) =
      (Real.exp (-A * Real.log n) : ℂ) * cexp (-((γ * Real.log n : ℝ) : ℂ) * I) := by
  rw [cpow_def_of_ne_zero (by exact_mod_cast hn), ← natCast_log, ofReal_exp, ← Complex.exp_add]
  congr 1; push_cast; ring

/-- Converting an exponent to the `t_n` coordinate. -/
lemma le_tn_iff {q n : ℕ} (hq : 2 ≤ q) (hn : 1 ≤ n) {x : ℝ} :
    x ≤ tn q n ↔ (q : ℝ) ^ x ≤ n :=
  Real.le_logb_iff_rpow_le (by exact_mod_cast hq) (by exact_mod_cast hn)

/-- Indices beyond `q^X` have `t_n ≥ X`. -/
lemma tn_ge_of_gt {q n : ℕ} (hq : 2 ≤ q) {X : ℝ} (hn : ⌊(q : ℝ) ^ X⌋₊ < n) : X ≤ tn q n :=
  (le_tn_iff hq (by omega)).2 (Nat.lt_of_floor_lt hn).le

/-- A common cutoff for the detector and Gram test. With this cutoff both
Cauchy–Schwarz factors and the original responses have exactly the same range. -/
abbrev NearData.horizon (D : NearData) := max D.xf D.xg
noncomputable abbrev samples (q : ℕ) (X : ℝ) := Finset.Icc 1 ⌊(q:ℝ)^X⌋₊

end GradedNear
