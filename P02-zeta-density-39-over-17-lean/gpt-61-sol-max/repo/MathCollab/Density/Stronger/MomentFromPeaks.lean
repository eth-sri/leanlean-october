module
public import MathCollab.Density.Stronger.ConditionalMoment
public import MathCollab.Density.Stronger.SeparatedVolume
public import MathCollab.Density.Stronger.Fourth.FourthMoment
public import MathCollab.Density.Stronger.ConditionalDensity

@[expose] public section

open MeasureTheory Filter
open scoped Interval

namespace MathCollab.Density.Stronger

/-- The literal fourth moment is now supplied by a proved producer. -/
theorem actual_fourth_moment_eventually (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ H : ℝ in atTop,
      (∫ t in H..2*H, zetaMomentCriticalNorm t^4) ≤ C*H^(1+η) := by
  obtain ⟨C,B,hC,hfourth⟩ := Fourth.zeta_fourth_dyadic η hη
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop B,eventually_gt_atTop (0 : ℝ)] with H hH hH0
  exact hfourth H hH hH0

/-- Generic separated covering applied to the literal actual-zeta superlevel.
The actual finite-peak bound remains the displayed hypothesis. -/
theorem pointValue_volume_le_of_peak_card {H V η : ℝ} (hV : 0 < V)
    (hpeaks : ∀ W : Finset ℝ, oneSeparated W →
      (∀ t ∈ W, t ∈ pointValueSuperlevel H V) →
      (W.card : ℝ)*V^12 ≤ H^(2+η)) :
    volume (pointValueSuperlevel H V) ≤ ENNReal.ofReal (2*H^(2+η)/V^12) := by
  have hc : ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ pointValueSuperlevel H V) →
      oneSeparated W → (W.card : ℝ) ≤ H^(2+η)/V^12 := by
    intro W hW hsep
    exact (le_div_iff₀ (pow_pos hV 12)).mpr (hpeaks W hsep hW)
  have h := volume_le_two_mul_of_separated_card_bound hc
  simpa only [mul_div_assoc] using h


