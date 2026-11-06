
import GradedNear.Basic
import GradedNear.Tactics

/-!
# The responses as one sum over `n`

`Σ_j a_j R_j = -𝓛⁻¹ Re Σ_{1 ≤ n ≤ q^{x_f}} c_n Y_n`, with `c_n = (Λ(n)/n) e^{s t_n} f(t_n)` and
`Y_n = Σ_j a_j e^{-δ_j t_n} χ_j(n) e^{-i γ_j log n}` (paper §8.5).
-/

open Complex
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GradedNear

variable {q : ℕ} {ι : Type*} [Fintype ι]

/-- The general term identity: for every `n`,
`Λ(n) χ(n) n^{-((1 - σ/𝓛) + iγ)} F(t_n) = (Λ(n)/n) e^{σ t_n} F(t_n) · χ(n) e^{-iγ log n}`. -/
lemma prime_term (F : ℝ → ℝ) (n : ℕ) (χ : DirichletCharacter ℂ q) (σ γ : ℝ) :
    ↑(Λ n) * χ n * ↑n ^ (- testPoint q σ γ ) *
        ↑(F (tn q n)) =
      ↑(Λ n / n * Real.exp (σ * tn q n) * F (tn q n)) *
        (χ n * cexp (-↑(γ * Real.log n) * I)) := by
  by_cases hn0 : n = 0
  · simp [hn0]
  rw [natCast_cpow_anchor hn0]
  push_cast
  ring

/-- The `j`-th component of `Y_n`. -/
def ycomp (E : Entries q ι) (a : ι → ℝ) (j : ι) (n : ℕ) : ℂ :=
  ↑(a j) * (↑(Real.exp (- E.δ j * tn q n)) * E.χ j n *
    cexp (-((E.γ j * Real.log n : ℝ) : ℂ) * I))

/-- The character-weighted sum of the entry components. -/
def Yn (E : Entries q ι) (a : ι → ℝ) (n : ℕ) : ℂ := ∑ j, ycomp E a j n

end GradedNear
