module

public import HypoellipticAleksandrov.KineticAleksandrov.Autonomous.PositionOverlapSupport

/-! # Localized positive norms with actual support and restarted tails -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.Autonomous
open Set MeasureTheory Filter
open scoped ENNReal

/- Support inside a larger observation set transfers the positive Lq norm bound. -/
theorem positionPositiveNorm_restrict_le {X : Type*} [MeasurableSpace X]
    (m : Measure X) (F : X → ℝ≥0∞) (q : ℝ) (hq : 0 < q)
    (E T ) (hE : MeasurableSet E) (hT : MeasurableSet T)
    (hs : ∀ᵐ x ∂m, x ∈ E → F x ≠ 0 → x ∈ T) :
    positionPositiveNorm (m.restrict E) q F ≤ positionPositiveNorm (m.restrict T) q F := by
  unfold positionPositiveNorm
  apply ENNReal.rpow_le_rpow _ (one_div_nonneg.mpr hq.le)
  rw [← lintegral_indicator hE, ← lintegral_indicator hT]
  apply lintegral_mono_ae
  filter_upwards [hs] with x hx
  by_cases he : x ∈ E
  · rw [indicator_of_mem he]
    by_cases hf : F x = 0
    · rw [hf, ENNReal.zero_rpow_of_pos hq]
      exact zero_le
    · rw [indicator_of_mem (hx he hf)]
  · rw [indicator_of_notMem he]
    exact zero_le

/- The elapsed tail used on output bin `i` after source bin `j`. -/
def positionOverlapDelay (i j : ℕ) : ℝ := max ((i : ℝ) - (j : ℝ) - 1) 0

/- Strict future support converts the grid delay to an elapsed-time lower bound. -/
end HypoellipticAleksandrov.KineticAleksandrov.Autonomous
