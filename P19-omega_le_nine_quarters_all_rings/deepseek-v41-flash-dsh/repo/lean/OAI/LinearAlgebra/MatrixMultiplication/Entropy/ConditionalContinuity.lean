module

public import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ConditionalLabels

public section

@[expose] section

namespace OAI

/-! Finite entropy, rate estimates and ordered asymptotic limits. -/


namespace MatrixMultiplication.ConditionalLabels

open MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology Classical

universe u v w
variable {A : Type u} [Fintype A] {Label : ℕ → Type v}
  [∀ n, Fintype (Label n)]

theorem exists_rational_law_sequence (p : FiniteLaw A) :
    ∃ q : ℕ → RationalLaw A,
      ∀ a, Tendsto (fun n => (q n).toFiniteLaw.mass a) atTop (𝓝 (p.mass a)) := by
  have hexists (n : ℕ) := p.exists_rational_approximation
    (1 / ((n : ℝ) + 1)) (by positivity)
  choose q _support close using hexists
  refine ⟨q, fun a => ?_⟩
  have hdifference : Tendsto
      (fun n => (q n).toFiniteLaw.mass a - p.mass a) atTop (𝓝 0) := by
    apply squeeze_zero_norm _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    simpa using (close n a).le
  simpa using hdifference.add_const (p.mass a)

end MatrixMultiplication.ConditionalLabels


end OAI
