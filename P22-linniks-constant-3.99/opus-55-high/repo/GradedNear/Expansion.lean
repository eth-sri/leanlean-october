module

public import GradedNear.Basic

/-!
# The responses as one sum over `n`

`Σ_j a_j R_j = -𝓛⁻¹ Re Σ_{1 ≤ n ≤ q^{x_f}} c_n Y_n`, with `c_n = (Λ(n)/n) e^{s t_n} f(t_n)` and
`Y_n = Σ_j a_j e^{-δ_j t_n} χ_j(n) e^{-i γ_j log n}` (paper §8.5).
-/

@[expose] public section

open Complex
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GradedNear

variable {q : ℕ} {ι : Type*} [Fintype ι]

/-- `Y_n = Σ_j a_j e^{-δ_j t_n} χ_j(n) e^{-i γ_j log n}`. -/
def Yn (E : Entries q ι) (a : ι → ℝ) (n : ℕ) : ℂ :=
  ∑ j, (a j : ℂ) * ((Real.exp (-(E.δ j) * tn q n) : ℂ) * E.χ j n *
    cexp (-((E.γ j * Real.log n : ℝ) : ℂ) * I))

/-- `c_n = (Λ(n)/n) e^{s t_n} f(t_n)`. -/
def cWeight (D : NearData) (q n : ℕ) : ℝ :=
  Λ n / n * Real.exp (D.s * tn q n) * D.f (tn q n)

/-- `Σ_j a_j R_j = -𝓛⁻¹ Re Σ_{1 ≤ n ≤ q^{x_f}} c_n Y_n`. -/
lemma sum_response (D : NearData) (E : Entries q ι) (a : ι → ℝ) (hq : 2 ≤ q)
    (hf : ∀ t, D.xf ≤ t → D.f t = 0) :
    ∑ j, a j * response D E j =
      -(∑ n ∈ Finset.Icc 1 ⌊(q : ℝ) ^ D.xf⌋₊, (cWeight D q n : ℂ) * Yn E a n).re /
        Real.log q := by
  unfold response Yn
  simp only [primeSum_eq_sum hq _ _ hf, re_sum, Finset.mul_sum, ← Finset.sum_neg_distrib,
    Finset.sum_div]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n hn0 => Finset.sum_congr rfl fun j _ => ?_
  have hn : (0 : ℝ) < n := mod_cast (Finset.mem_Icc.1 hn0).1
  rw [natCast_cpow_neg (by simp at hn0; omega), show Real.exp (-(1 - (D.s - E.δ j) / Real.log q) *
      Real.log n) = (1 / n) * Real.exp (D.s * tn q n) * Real.exp (-E.δ j * tn q n) by
    rw [one_div, ← Real.exp_log hn, ← Real.exp_neg, Real.exp_log hn, ← Real.exp_add,
      ← Real.exp_add]
    congr 1; unfold tn; ring]
  simp [cWeight]
  ring

end GradedNear
