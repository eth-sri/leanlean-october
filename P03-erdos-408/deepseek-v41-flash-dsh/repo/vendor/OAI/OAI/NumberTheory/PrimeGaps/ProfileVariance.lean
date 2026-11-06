module

public import OAI.NumberTheory.PrimeGaps.Profiles

@[expose] public section

namespace OAI

namespace LargePrimeGaps







noncomputable def deleteCoordinate {j : ℕ} (f : (Fin (j+1) → ℝ) → ℝ)
    (t : Fin j → ℝ) : ℝ := ∫ u : ℝ, f (Fin.snoc t u)

end LargePrimeGaps

end OAI
