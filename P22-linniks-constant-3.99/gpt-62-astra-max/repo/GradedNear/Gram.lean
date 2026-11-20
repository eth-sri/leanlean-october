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

lemma twist_mul_conj (χ ψ : DirichletCharacter ℂ q) (γ γ' : ℝ) (n : ℕ) :
    twist χ γ n * (starRingEnd ℂ) (twist ψ γ' n) = twist (χ * ψ⁻¹) (γ-γ') n := by
  simp only [twist, map_mul, ← Complex.exp_conj, map_neg, conj_ofReal, conj_I,
    ← MulChar.star_apply', MulChar.coeToFun_mul, Pi.mul_apply, sub_mul, ofReal_sub]
  rw [mul_mul_mul_comm, ← Complex.exp_add]
  congr 2; ring

variable (E : Entries q ι) (a : ι → ℝ)

abbrev pairSignal (j k : ι) := signal (E.χ j * (E.χ k)⁻¹) (-(E.δ j+E.δ k)) (E.γ j-E.γ k)

omit [Fintype ι] in
lemma pairSignal_eq (j k : ι) (n : ℕ) : pairSignal E j k n = entrySignal E j n * (starRingEnd ℂ) (entrySignal E k n) := by
  simp only [pairSignal, entrySignal, signal, map_mul, conj_ofReal, neg_add, add_mul, Real.exp_add]
  rw [mul_mul_mul_comm, ← ofReal_mul, twist_mul_conj]

/-- An observation of the squared response is the quadratic form of its pair kernels. -/
lemma observe_sq (C : Finset ℕ) (w : ℕ → ℝ) : ∑ n ∈ C, w n * ‖Yn E a n‖ ^ 2 =
    ∑ j, ∑ k, a j * a k * ∑ n ∈ C, w n * (pairSignal E j k n).re := by
  simp_rw [Finset.mul_sum]; rw [Finset.sum_comm_cycle (u := C)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Complex.normSq_eq_norm_sq, ← ofReal_re (normSq _), ← mul_conj]
  simp_rw [Yn, map_sum,
    Finset.sum_mul_sum, re_sum, Finset.mul_sum, pairSignal_eq]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, conj_ofReal, mul_mul_mul_comm, ← ofReal_mul, re_ofReal_mul]; ring

/-- The Gram point `s_{jk} = (1 - σ_{jk}/𝓛) + i(γ_j - γ_k)` with `σ_{jk} = s₁ - δ_j - δ_k`. -/
abbrev sjk (D : NearData) (E : Entries q ι) (j k : ι) : ℂ :=
  point q (D.s₁ - E.δ j - E.δ k) (E.γ j - E.γ k)

/-- The Gram part of the second factor as a quadratic form in the prime sums. -/
lemma gram_part_eq (D : NearData) (E : Entries q ι) (a : ι → ℝ) (hq : 2 ≤ q)
    (hD : D.Valid) :
    ∑ n ∈ samples q D.horizon, primeMass n * (D.g (tn q n) * Real.exp (D.s₁ * tn q n)) *
        ‖Yn E a n‖ ^ 2 =
      ∑ j, ∑ k, a j * a k * (primeSum (E.χ j * (E.χ k)⁻¹) D.g (sjk D E j k)).re := by
  rw [observe_sq]
  have hg t (ht : D.horizon ≤ t) := hD.g_cond1.vanish t ((le_max_right ..).trans ht)
  simp_rw [sjk, primeSum_re hq hg]
  congr! 4 with j _ k
  rw [show D.s₁-E.δ j-E.δ k = D.s₁ + -(E.δ j+E.δ k) by ring, signal_add, re_ofReal_mul]; ring

end GradedNear
