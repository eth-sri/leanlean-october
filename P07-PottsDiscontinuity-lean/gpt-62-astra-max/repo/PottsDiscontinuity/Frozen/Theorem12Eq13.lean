module

public import Mathlib
public import PottsDiscontinuity.Analysis.Identity44
public import PottsDiscontinuity.Analysis.Asymptotic13

@[expose] public section

open MeasureTheory Filter Topology Real

namespace PottsDiscontinuity

/-- Positivity of the rate and its asymptotics (1.3). -/
theorem rc_theorem_1_2_positivity_eq_1_3 :
    (∀ q : ℝ, 4 < q → ∀ lam : ℝ, 0 < lam → Real.cosh lam = Real.sqrt q / 2 →
      ∃ S T : ℝ,
        Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N,
            (-1 : ℝ) ^ k / k * Real.tanh (k * lam)) atTop (𝓝 S) ∧
        HasSum (fun k : ℕ => 4 / ((2 * k + 1) * Real.sinh (π ^ 2 * (2 * k + 1) / (2 * lam)))) T ∧
        0 < lam + 2 * S ∧ lam + 2 * S = T) ∧
    Asymptotics.IsEquivalent (𝓝[>] (4 : ℝ))
      (fun q => ∑' k : ℕ, 4 / ((2 * k + 1) *
        Real.sinh (π ^ 2 * (2 * k + 1) / (2 * Real.arcosh (Real.sqrt q / 2)))))
      (fun q => 8 * Real.exp (-(π ^ 2 / Real.sqrt (q - 4)))) :=
  ⟨fun _ _ lam hlam _ => identity44 hlam, asymptotic13⟩

end PottsDiscontinuity
