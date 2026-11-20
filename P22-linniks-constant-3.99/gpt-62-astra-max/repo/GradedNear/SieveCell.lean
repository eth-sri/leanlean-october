module

public import GradedNear.Bookkeeping
public import GradedNear.Gram
public import GradedNear.SieveMajorant

/-!
# One sieve cell

For a cell `𝒞` above the sieve level with `t_n ≥ t₀`, use
* `Λ(n) ≤ log n · ν(n) + pp(n)` on `𝒞`,
* `Σ_{𝒞} (log n / n) ν(n) ≤ m log q + u`,
* `‖Σ_{𝒞} ν(n) ψ_{jj'}(n) log n · n^{-((1+β) + iτ)}‖ ≤ u` for every pair `j ≠ j'`,
* `Σ_{𝒞} pp(n)/n ≤ ppMass`.

Only the main diagonal `m log q` retains its damping factor. The remaining
contributions total at most `(u + ppMass)(Σ a)²`.
-/

@[expose] public section

open Complex
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GradedNear

variable {q : ℕ} {ι : Type*} [Fintype ι]

variable (E : Entries q ι) (a : ι → ℝ) (ha : ∀ j, 0 ≤ a j)

omit [Fintype ι] in
lemma norm_entrySignal_le (j : ι) (n : ℕ) : ‖entrySignal E j n‖ ≤ Real.exp (-E.δ j * tn q n) := by
  rw [entrySignal, signal, twist, norm_mul, norm_mul, ← ofReal_neg, norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_of_nonneg (Real.exp_pos _).le]; exact mul_le_of_le_one_right (Real.exp_pos _).le (DirichletCharacter.norm_le_one ..)

include ha in
lemma norm_Yn_le (hδ : ∀ j, 0 ≤ E.δ j) {n : ℕ} (hq : 2 ≤ q) : ‖Yn E a n‖ ≤ ∑ j, a j := by
  refine norm_sum_le_of_le _ fun j _ => ?_
  rw [norm_mul, Complex.norm_of_nonneg (ha j)]; apply mul_le_of_le_one_right (ha j)
  exact (norm_entrySignal_le E j n).trans (Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg (hδ j) (tn_nonneg q n hq)]))

abbrev sievePoint (E : Entries q ι) (j k : ι) := point q (-(E.δ j + E.δ k)) (E.γ j - E.γ k)

include ha in
/-- **Bound for one sieve cell.** -/
lemma cell_bound (hδ : ∀ j, 0 ≤ E.δ j)
    (hq : 2 ≤ q) {V t₀ m u : ℝ} (C : Finset ℕ) (hV : 1 < V) (hcell : ∀ n ∈ C, V < n ∧ t₀ ≤ tn q n)
    (ht : 0 ≤ t₀) (hu : 0 ≤ u)
    (hdiag : ∑ n ∈ C, Real.log n / n * sieveNu V n ≤ m * Real.log q + u)
    (hoff : ∀ j k, j ≠ k → ‖∑ n ∈ C, sieveTerm V (E.χ j * (E.χ k)⁻¹)
        (sievePoint E j k) n‖ ≤ u) :
    ∑ n ∈ C, primeMass n * ‖Yn E a n‖ ^ 2 ≤
      (∑ j, Real.exp (-2 * E.δ j * t₀) * m * a j ^ 2) * Real.log q + (u + ppMass) * (∑ j, a j) ^ 2 := by
  classical
  let w (n : ℕ) := Real.log n / n * sieveNu V n
  have hw n : 0 ≤ w n := by dsimp [w]; positivity [Real.log_natCast_nonneg n]
  let e j := Real.exp (-2 * E.δ j * t₀)
  let B j := e j * m * Real.log q
  have hpair j k : ∑ n ∈ C, w n * (pairSignal E j k n).re ≤ (if k = j then B j else 0) + u := by
    split_ifs with h
    · subst k
      have hcorr n (hn : n ∈ C) : (pairSignal E j j n).re ≤ e j := by
        rw [pairSignal_eq, Complex.mul_conj, ofReal_re, normSq_eq_norm_sq]
        grw [norm_entrySignal_le E, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr; dsimp [e]; norm_num; nlinarith [mul_le_mul_of_nonneg_left (hcell n hn).2 (hδ j)]
      have he : e j ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg (hδ j) ht])
      grw [hcorr, ← Finset.sum_mul, hdiag] <;> try first | exact hw _ | assumption
      dsimp [B]; nlinarith only [mul_le_mul_of_nonneg_left he hu]
    · simp only [zero_add]
      apply le_trans (le_of_eq ?_) ((re_le_norm _).trans (hoff j k (Ne.symm h)))
      rw [re_sum]; refine Finset.sum_congr rfl fun n hn => ?_
      dsimp only [sieveTerm, wt, sievePoint]
      rw [mul_left_comm _ (Real.log n : ℂ), ofReal_natCast, shifted_power (by exact_mod_cast le_of_lt (hV.trans (hcell n hn).1))]
      simp only [re_ofReal_mul, w, pairSignal]; ring
  have hs : ∑ n ∈ C, w n * ‖Yn E a n‖ ^ 2 ≤ ∑ j, B j*a j^2 + (∑ j, a j)^2*u := by
    rw [observe_sq]; grw [hpair] <;> try exact mul_nonneg (ha _) (ha _)
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, ← Finset.sum_mul, ← Finset.sum_mul_sum, sq]
    simp [mul_comm]
  calc
    _ ≤ ∑ n ∈ C, (w n * ‖Yn E a n‖ ^ 2 + pp n / n * (∑ j, a j) ^ 2) := by
      refine Finset.sum_le_sum fun n hn => ?_
      unfold primeMass
      grw [vonMangoldt_le_sieve hV (hcell n hn).1, add_div, add_mul]
      gcongr
      · exact le_of_eq (by unfold w; ring)
      · exact norm_Yn_le E a ha hδ hq
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      grw [hs, pp_le_mass]; dsimp [B,e]; simp_rw [mul_right_comm (_*_) (Real.log q), ← Finset.sum_mul]; exact le_of_eq (by ring)

end GradedNear
