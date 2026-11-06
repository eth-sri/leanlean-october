module
public import OAI.NumberTheory.DirichletL.Reflection.OriginalWeights
public import OAI.NumberTheory.DirichletL.Reflection.InactiveEnergy
import WeylPort.Analytic.RealLaplace

@[expose] public section

namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma bounded_row_multiplier_energy {κ : Type*} (rows : Finset κ) (r f : κ→ℂ)
    (hr : ∀ k∈rows,‖r k‖≤1) :
    (∑ k∈rows,‖r k*f k‖^2)≤∑ k∈rows,‖f k‖^2 := by
  apply Finset.sum_le_sum
  intro k hk
  apply pow_le_pow_left₀ (norm_nonneg _)
  pm_514 hr k hk

end
end SevenEighths.InverseReflectedPhase

end OAI
