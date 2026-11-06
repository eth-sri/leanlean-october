import GradedNear.Tactics

import GradedNear.Expansion

/-!
# The Gram part of the second Cauchy–Schwarz factor

`Σ_n (Λ(n)/n) g(t_n) e^{s₁ t_n} |Y_n|² = Σ_{j,k} a_j a_k Re primeSum(χ_j χ_k⁻¹, g, s_{jk})`,
with `s_{jk} = (1 - σ_{jk}/𝓛) + i(γ_j - γ_k)` and `σ_{jk} = s₁ - δ_j - δ_k` (paper §8.5).
-/

open Complex

namespace GradedNear

variable {q : ℕ} {ι : Type*}

/-- `ycomp_j · conj(ycomp_k) = a_j a_k e^{-(δ_j+δ_k) t_n} (χ_j χ_k⁻¹)(n) e^{-i(γ_j - γ_k) log n}`. -/
lemma ycomp_mul_conj (E : Entries q ι) (a : ι → ℝ) (j k : ι) (n : ℕ) :
    ycomp E a j n * (starRingEnd ℂ) (ycomp E a k n) =
      ((a j * a k * Real.exp (-(E.δ j + E.δ k) * tn q n) : ℝ) : ℂ) *
        ((E.χ j * (E.χ k)⁻¹) n * cexp (-(((E.γ j - E.γ k) * Real.log n : ℝ) : ℂ) * I)) := by
  simp only [ycomp, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, Complex.conj_I,
    MulChar.coeToFun_mul, Pi.mul_apply]
  simp only [starRingEnd_apply, MulChar.star_apply', neg_add, neg_mul, ofReal_mul]
  push_cast
  ring_nf
  grind [Complex.exp_add, Complex.exp_sub, Complex.exp_neg]

/-- `|Y_n|² = Σ_{j,k} Re(ycomp_j · conj ycomp_k)`. -/
lemma norm_Yn_sq [Fintype ι] (E : Entries q ι) (a : ι → ℝ) (n : ℕ) :
    ‖Yn E a n‖ ^ 2 = ∑ j, ∑ k, (ycomp E a j n * (starRingEnd ℂ) (ycomp E a k n)).re := by
  rw [← Complex.ofReal_re (‖Yn E a n‖ ^ 2), Complex.ofReal_pow, ← Complex.mul_conj', Yn,
    map_sum, Finset.sum_mul_sum, Complex.re_sum]
  simp

/-- The Gram point `s_{jk} = (1 - σ_{jk}/𝓛) + i(γ_j - γ_k)` with `σ_{jk} = s₁ - δ_j - δ_k`. -/
noncomputable def sjk (D : NearData) (E : Entries q ι) (j k : ι) : ℂ :=
  testPoint q (D.s₁ - E.δ j - E.δ k) (E.γ j - E.γ k)

end GradedNear
