module

public import OAI.NumberTheory.PrimeGaps.Profiles

@[expose] public section

namespace OAI

namespace LargePrimeGaps

open Filter

open Set Filter MeasureTheory

open scoped Topology ContDiff

noncomputable def deleteCoordinate {j : ℕ} (f : (Fin (j+1) → ℝ) → ℝ)
    (t : Fin j → ℝ) : ℝ := ∫ u : ℝ, f (Fin.snoc t u)

end LargePrimeGaps

end OAI
