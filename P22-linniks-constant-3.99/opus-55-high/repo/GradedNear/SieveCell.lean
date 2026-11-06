module

public import GradedNear.GramForm
public import GradedNear.SieveBasic

/-!
# One sieve cell

For a cell `𝒞` of integers `n ≥ 1` with `t_n ≥ t₀`, if
* `Λ(n) ≤ log n · ν(n) + pp(n)` on `𝒞`,
* `Σ_{𝒞} (log n / n) ν(n) ≤ Dk`,
* `‖Σ_{𝒞} ν(n) ψ_{jj'}(n) log n · n^{-((1+β) + iτ)}‖ ≤ Ok` for every pair `j ≠ j'`,
* `Σ_{𝒞} pp(n)/n ≤ Pk`,

then `Σ_{𝒞} (Λ(n)/n) |Y_n|² ≤ Σ_j e^{-2δ_j t₀} Dk a_j² + (Ok + Pk)(Σ a)²`.
-/

@[expose] public section

open Complex
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GradedNear

variable {q : ℕ} {ι : Type*} [Fintype ι]

omit [Fintype ι] in
lemma norm_ycomp_le (E : Entries q ι) (a : ι → ℝ) (ha : ∀ j, 0 ≤ a j) (j : ι) (n : ℕ) :
    ‖ycomp E a j n‖ ≤ a j * Real.exp (-(E.δ j) * tn q n) := by
  have := ha j
  simp [ycomp, abs_of_nonneg this, Complex.norm_exp, -Complex.natCast_log]
  grw [DirichletCharacter.norm_le_one, mul_one]

/-- **Bound for one sieve cell.** -/
lemma cell_bound (E : Entries q ι) (a : ι → ℝ) (ha : ∀ j, 0 ≤ a j) (hδ : ∀ j, 0 ≤ E.δ j)
    (hq : 2 ≤ q) (V t₀ Dk Ok Pk : ℝ) (C : Finset ℕ) (hC1 : ∀ n ∈ C, 1 ≤ n)
    (hCt : ∀ n ∈ C, t₀ ≤ tn q n) (pp : ℕ → ℝ) (hpp0 : ∀ n, 0 ≤ pp n)
    (hmaj : ∀ n ∈ C, Λ n ≤ Real.log n * sieveNu V n + pp n)
    (hdiag : ∑ n ∈ C, Real.log n / n * sieveNu V n ≤ Dk)
    (hoff : ∀ j j', j ≠ j' → ‖∑ n ∈ C, (sieveNu V n : ℂ) * ((E.χ j * (E.χ j')⁻¹) n *
        (Real.log n : ℂ) * (n : ℂ) ^ (-(((1 + (E.δ j + E.δ j') / Real.log q : ℝ) : ℂ) +
          ((E.γ j - E.γ j' : ℝ) : ℂ) * I)))‖ ≤ Ok)
    (hppsum : ∑ n ∈ C, pp n / n ≤ Pk) (hOk : 0 ≤ Ok) :
    ∑ n ∈ C, Λ n / n * ‖Yn E a n‖ ^ 2 ≤
      ∑ j, Real.exp (-2 * E.δ j * t₀) * Dk * a j ^ 2 + (Ok + Pk) * (∑ j, a j) ^ 2 := by
  classical
  have hY : ∀ n, ‖Yn E a n‖ ≤ ∑ j, a j := fun n => (norm_sum_le ..).trans
    (Finset.sum_le_sum fun j _ => (norm_ycomp_le E a ha j n).trans (mul_le_of_le_one_right (ha j)
      (Real.exp_le_one_iff.2 (by nlinarith [hδ j, tn_nonneg q n hq]))))
  have key : ∀ j j', ∑ n ∈ C, Real.log n / n * sieveNu V n *
      (ycomp E a j n * (starRingEnd ℂ) (ycomp E a j' n)).re ≤
      (if j = j' then Real.exp (-2 * E.δ j * t₀) * Dk * a j ^ 2 else 0) + a j * a j' * Ok := by
    intro j j'
    split_ifs with h
    · subst h
      refine le_add_of_le_of_nonneg ?_ (by nlinarith)
      calc _ ≤ ∑ n ∈ C, Real.log n / n * sieveNu V n * (a j ^ 2 * Real.exp (-2 * E.δ j * t₀)) := by
            gcongr with n hn
            · have := sieveNu_nonneg V n; positivity
            rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
            grw [norm_ycomp_le E a ha j n, mul_pow, ← Real.exp_nat_mul]
            gcongr _ * Real.exp ?_; push_cast; nlinarith [hδ j, hCt n hn]
        _ ≤ _ := by grw [← Finset.sum_mul, hdiag]; exact (by ring : _ = _).le
    · rw [zero_add]
      refine le_of_eq_of_le ?_ (mul_le_mul_of_nonneg_left ((re_le_norm _).trans
        (hoff j j' h)) (mul_nonneg (ha j) (ha j')))
      rw [re_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      have := hC1 n hn
      rw [ycomp_mul_conj, natCast_cpow_neg (by omega), show -(1 + (E.δ j + E.δ j') / Real.log q) *
        Real.log n = -(E.δ j + E.δ j') * tn q n - Real.log n by grind [tn], Real.exp_sub,
        Real.exp_log (by positivity), ← re_ofReal_mul, ← re_ofReal_mul]
      push_cast
      ring
  calc ∑ n ∈ C, Λ n / n * ‖Yn E a n‖ ^ 2
      ≤ ∑ n ∈ C, (Real.log n * sieveNu V n / n * ‖Yn E a n‖ ^ 2 + pp n / n * (∑ j, a j) ^ 2) :=
        Finset.sum_le_sum fun n hn => by
          have := hpp0 n
          grw [hmaj n hn, add_div, add_mul]
          gcongr; exact hY n
    _ ≤ ∑ j, ∑ j', ((if j = j' then Real.exp (-2 * E.δ j * t₀) * Dk * a j ^ 2 else 0) +
        a j * a j' * Ok) + Pk * (∑ j, a j) ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      simp only [norm_Yn_sq, Finset.mul_sum]
      rw [Finset.sum_comm]
      gcongr with j
      rw [Finset.sum_comm]
      gcongr with j'
      grind
    _ = _ := by
      simp [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
      ring

end GradedNear
