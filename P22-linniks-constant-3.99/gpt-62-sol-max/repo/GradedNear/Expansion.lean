module

public import GradedNear.Basic

@[expose] public section

open Complex Finset
open scoped ArithmeticFunction.vonMangoldt ComplexConjugate

noncomputable section

namespace GradedNear

variable {q : ℕ} {ι : Type*}

/-- The character phase with damping `exp (-δ * tn q n)`. -/
def phaseWeight (χ : DirichletCharacter ℂ q) (δ γ : ℝ) (n : ℕ) : ℂ :=
  χ n * cexp (((-δ * tn q n : ℝ) : ℂ) - ((γ * Real.log n : ℝ) : ℂ) * I)

/-- The common factorization for the response, Gram, and sieve sums. -/
lemma phaseWeight_term (χ : DirichletCharacter ℂ q) {n : ℕ} (hn : 1 ≤ n) (r δ γ : ℝ) :
    χ n * (n : ℂ) ^ (-spectralPoint q (r - δ) γ) =
      ((Real.exp (r * tn q n) / n : ℝ) : ℂ) * phaseWeight χ δ γ n := by
  have he : (Real.log n : ℂ) * -spectralPoint q (r - δ) γ =
      -((Real.log n : ℝ) : ℂ) + (r * tn q n : ℝ) +
        (((-δ * tn q n : ℝ) : ℂ) - ((γ * Real.log n : ℝ) : ℂ) * I) := by
    unfold spectralPoint tn
    push_cast
    ring
  rw [cpow_def_of_ne_zero (by simp; omega), ← natCast_log, he,
    exp_add, exp_add, exp_neg, ← ofReal_exp, Real.exp_log (by exact_mod_cast hn), phaseWeight]
  push_cast
  ring

/-- The factored, finite sum at a spectral point. Extending the cutoff adds only zeros. -/
lemma primeSum_eq_phase_sum (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q) (f : ℝ → ℝ) {X : ℝ}
    (hf : ∀ t, X ≤ t → f t = 0) {N : ℕ} (hN : ⌊(q : ℝ) ^ X⌋₊ ≤ N) (r δ γ : ℝ) :
    primeSum χ f (spectralPoint q (r - δ) γ) = ∑ n ∈ Ioc 0 N,
      ((Λ n / n * Real.exp (r * tn q n) * f (tn q n) : ℝ) : ℂ) * phaseWeight χ δ γ n := by
  unfold primeSum
  rw [tsum_eq_sum (s := Ioc 0 N)]
  · refine sum_congr rfl fun n hn => ?_
    rw [mul_assoc (Λ n : ℂ), phaseWeight_term χ (mem_Ioc.mp hn).1]
    simp only [tn]
    push_cast
    ring
  · intro n hn
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hn
    rcases hn with hn | hn
    · obtain rfl : n = 0 := by omega
      simp
    · have ht := (le_tn_iff hq (by omega)).mpr (Nat.lt_of_floor_lt (hN.trans_lt hn)).le
      simp [show f (Real.log n / Real.log q) = 0 from hf _ ht]

/-- Coefficients in the expansion of the square of `Yn`. -/
def phase (E : Entries q ι) (j : ι) := phaseWeight (E.χ j) (E.δ j) (E.γ j)

def Yn [Fintype ι] (E : Entries q ι) (a : ι → ℝ) (n : ℕ) : ℂ :=
  ∑ j, (a j : ℂ) * phase E j n

lemma phase_pair (E : Entries q ι) (j k : ι) (n : ℕ) :
    phase E j n * conj (phase E k n) =
      phaseWeight (E.χ j * (E.χ k)⁻¹) (E.δ j + E.δ k) (E.γ j - E.γ k) n := by
  simp only [phase, phaseWeight, map_mul, map_sub, Complex.conj_ofReal, ← Complex.exp_conj,
    Complex.conj_I, MulChar.coeToFun_mul, Pi.mul_apply, ← RCLike.star_def, MulChar.star_apply']
  rw [mul_mul_mul_comm, ← exp_add]
  congr 2
  push_cast
  ring

lemma weighted_Yn [Fintype ι] (E : Entries q ι) (a : ι → ℝ) (S : Finset ℕ) (w : ℕ → ℝ) (L : ℝ) :
    (∑ n ∈ S, w n * ‖Yn E a n‖ ^ 2) / L =
      ∑ j, ∑ k, a j * a k * ((∑ n ∈ S, (w n : ℂ) * (phase E j n * conj (phase E k n))).re / L) := by
  simp_rw [← mul_div_assoc, ← sum_div]
  congr 1
  have h n : ‖Yn E a n‖ ^ 2 = (Yn E a n * conj (Yn E a n)).re := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  simp_rw [h, Yn, map_sum, sum_mul_sum, Complex.re_sum, mul_sum, sum_comm (s := S)]
  refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => sum_congr rfl fun n _ => ?_
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- `c_n = (Λ(n)/n) e^{s t_n} f(t_n)`. -/
def cWeight (D : NearData) (q n : ℕ) : ℝ :=
  Λ n / n * Real.exp (D.s * tn q n) * D.f (tn q n)

lemma sum_response [Fintype ι] (D : NearData) (E : Entries q ι) (a : ι → ℝ) (hq : 2 ≤ q)
    (hf : ∀ t, D.xf ≤ t → D.f t = 0) :
    ∑ j, a j * response D E j =
      -(∑ n ∈ Ioc 0 ⌊(q : ℝ) ^ D.xf⌋₊, (cWeight D q n : ℂ) * Yn E a n).re / Real.log q := by
  simp only [response, ← spectralPoint.eq_def,
    primeSum_eq_phase_sum hq _ _ hf le_rfl, ← cWeight.eq_def, ← phase.eq_def, neg_div, mul_neg,
    ← mul_div_assoc, sum_neg_distrib, ← sum_div, Yn, mul_sum, Complex.re_sum]
  congr 2
  rw [sum_comm]
  simp_all; grind

end GradedNear
