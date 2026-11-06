module

public import OAI.NumberTheory.PrimeGaps.ProfileVariance

@[expose] public section

namespace OAI

namespace LargePrimeGaps







noncomputable def l2Mass {j : ℕ} (f : (Fin j → ℝ) → ℝ) : ℝ := ∫ t, f t^2

@[simp] theorem l2Mass_zero (j : ℕ) : l2Mass (0 : (Fin j → ℝ) → ℝ) = 0 := by
  simp [l2Mass]

@[simp] theorem deleteCoordinate_zero (j : ℕ) :
    deleteCoordinate (0 : (Fin (j+1) → ℝ) → ℝ) = 0 := by
  funext t
  simp [deleteCoordinate]

def positiveSimplex (j : ℕ) (tau : ℝ) : Set (Fin j → ℝ) :=
  {t | (∀ i, 0 < t i) ∧ coordinateSum t < tau}

end LargePrimeGaps

end OAI
