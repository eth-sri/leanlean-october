module

public import DedekindZetaZeroFree.Moments.Comparison.FiniteRowContourDecay

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section

def comparisonFrequencyKernel {ι : Type*}
    (q : ι → ℝ) (M W : ℂ → ℂ) (E : ι → ℂ → ℂ → ℂ → ℂ)
    (Z : ℝ) (u : ι) (ξ w z : ℂ) : ℂ :=
  comparisonRealPower Z
      ((comparisonA : ℂ) / 2 + ξ - 1 + (comparisonH₀ : ℂ) * z +
        (comparisonB : ℂ) * (w - 1)) *
    Complex.exp ((ξ + z - 1) ^ 2) * M z * W w *
    comparisonRealPower (q u) (-z) * E u ξ w z

def comparisonFrequencyDyad {ι : Type*} (q : ι → ℝ) (principal : ι)
    (K U : ℝ) (C : Finset ι) : Prop :=
  (∀ u ∈ C, u ≠ principal ∧ U ≤ q u ∧ q u < 2 * U) ∧ (C.card : ℝ) ≤ K * U

open MeasureTheory

end
end DedekindZetaZeroFree
