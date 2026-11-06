module

public import DedekindZetaZeroFree.Moments.Comparison.FiniteRowContourDecay

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section



def comparisonFrequencyDyad {ι : Type*} (q : ι → ℝ) (principal : ι)
    (K U : ℝ) (C : Finset ι) : Prop :=
  (∀ u ∈ C, u ≠ principal ∧ U ≤ q u ∧ q u < 2 * U) ∧ (C.card : ℝ) ≤ K * U

open MeasureTheory

end
end DedekindZetaZeroFree
