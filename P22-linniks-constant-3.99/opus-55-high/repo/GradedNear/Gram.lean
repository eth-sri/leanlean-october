module

public import GradedNear.Expansion

/-!
# The Gram part of the second Cauchy–Schwarz factor

`Σ_n (Λ(n)/n) g(t_n) e^{s₁ t_n} |Y_n|² = Σ_{j,k} a_j a_k Re primeSum(χ_j χ_k⁻¹, g, s_{jk})`,
with `s_{jk} = (1 - σ_{jk}/𝓛) + i(γ_j - γ_k)` and `σ_{jk} = s₁ - δ_j - δ_k` (paper §8.5).
-/

@[expose] public section

open Complex
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GradedNear

variable {q : ℕ} {ι : Type*} [Fintype ι]

/-- The `j`-th component of `Y_n`. -/
def ycomp (E : Entries q ι) (a : ι → ℝ) (j : ι) (n : ℕ) : ℂ :=
  (a j : ℂ) * ((Real.exp (-(E.δ j) * tn q n) : ℂ) * E.χ j n *
    cexp (-((E.γ j * Real.log n : ℝ) : ℂ) * I))

omit [Fintype ι] in
/-- `ycomp_j · conj(ycomp_k) = a_j a_k e^{-(δ_j+δ_k) t_n} (χ_j χ_k⁻¹)(n) e^{-i(γ_j - γ_k) log n}`. -/
lemma ycomp_mul_conj (E : Entries q ι) (a : ι → ℝ) (j k : ι) (n : ℕ) :
    ycomp E a j n * (starRingEnd ℂ) (ycomp E a k n) =
      ((a j * a k * Real.exp (-(E.δ j + E.δ k) * tn q n) : ℝ) : ℂ) *
        ((E.χ j * (E.χ k)⁻¹) n * cexp (-(((E.γ j - E.γ k) * Real.log n : ℝ) : ℂ) * I)) := by
  unfold ycomp; generalize Real.log n = L
  simp [← exp_conj, ← MulChar.star_apply', add_mul, sub_mul, Complex.exp_add, Complex.exp_sub,
    Complex.exp_neg]
  ring_nf

/-- `|Y_n|² = Σ_{j,k} Re(ycomp_j · conj ycomp_k)`. -/
lemma norm_Yn_sq (E : Entries q ι) (a : ι → ℝ) (n : ℕ) :
    ‖Yn E a n‖ ^ 2 = ∑ j, ∑ k, (ycomp E a j n * (starRingEnd ℂ) (ycomp E a k n)).re := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.ofReal_re (Complex.normSq _), ← Complex.mul_conj,
    show Yn E a n = ∑ j, ycomp E a j n from rfl, map_sum, Finset.sum_mul_sum]
  simp_all

/-- The Gram point `s_{jk} = (1 - σ_{jk}/𝓛) + i(γ_j - γ_k)` with `σ_{jk} = s₁ - δ_j - δ_k`. -/
def sjk (D : NearData) (E : Entries q ι) (j k : ι) : ℂ :=
  (((1 - (D.s₁ - E.δ j - E.δ k) / Real.log q : ℝ)) : ℂ) + ((E.γ j - E.γ k : ℝ) : ℂ) * I

/-- The Gram part of the second factor as a quadratic form in the prime sums. -/
lemma gram_part_eq (D : NearData) (E : Entries q ι) (a : ι → ℝ) (hq : 2 ≤ q)
    (hg : ∀ t, D.xg ≤ t → D.g t = 0) {N : ℕ} (hN : ⌊(q : ℝ) ^ D.xg⌋₊ ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, Λ n / n * (D.g (tn q n) * Real.exp (D.s₁ * tn q n)) *
        ‖Yn E a n‖ ^ 2 =
      ∑ j, ∑ k, a j * a k * (primeSum (E.χ j * (E.χ k)⁻¹) D.g (sjk D E j k)).re := by
  rw [← Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hN) fun n hn hn' => by
    simp [Finset.mem_Icc, not_and, not_le] at hn hn'
    simp [hg _ (tn_ge_of_gt hq (hn' hn.1))]]
  simp only [primeSum_eq_sum hq _ _ hg, Complex.re_sum, Finset.mul_sum, norm_Yn_sq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun n hn => ?_
  have hn := (Finset.mem_Icc.1 hn).1
  rw [ycomp_mul_conj, sjk, natCast_cpow_neg (by omega), ← Complex.re_ofReal_mul,
    ← Complex.re_ofReal_mul, show Real.exp (-(1 - (D.s₁ - E.δ j - E.δ k) / Real.log q) *
      Real.log n) = Real.exp (D.s₁ * tn q n + -(E.δ j + E.δ k) * tn q n - Real.log n) by
        unfold tn; ring_nf, Real.exp_sub, Real.exp_add, Real.exp_log (Nat.cast_pos.2 hn)]
  push_cast
  ring_nf

end GradedNear
