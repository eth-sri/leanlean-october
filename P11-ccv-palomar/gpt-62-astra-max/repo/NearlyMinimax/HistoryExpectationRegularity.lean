module

public import NearlyMinimax.HistoryPriorWeakTransport


@[expose] public section

/-!
# Endpoint regularity and absolute continuity of the actual history prior
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter Set
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

variable {dependent : J → J → Prop} [Std.Refl dependent] [Std.Symm dependent] {Δ : ℕ}
    (hlabels : DegreeAtMost dependent Δ) {ρ T B : ℝ} (hρ : 0 < ρ) (hT : 0 ≤ T) (hB : 0 ≤ B) {E : Type*}
    [MeasurableSpace E] (μ : Measure (HistoryMarked dependent E)) [IsProbabilityMeasure μ] {a : E → ℝ}
    (ha : Measurable a) (habound : ∀ e, |a e| ≤ B) (hsmall : T * B / ρ ≤ historyActivityRadius Δ)
    {F : HistoryMarked dependent E → ℝ} (hF : Measurable F) {M : ℝ} (hM : 0 ≤ M)
    (hFbound : ∀ h, |F h| ≤ M)
include hlabels hρ hB ha habound hsmall hF hM hFbound

/-- Actual history expectations are Lipschitz on the closed source interval. -/
theorem historyMarkedExpectation_lipschitzOn :
    LipschitzOnWith ⟨M * (ρ⁻¹ * (Fintype.card J) * B * (3 / 2) ^ Fintype.card J), by positivity⟩
      (historyMarkedExpectation ρ μ a F) (Icc 0 T) := by
  have path := (historyDensityPath hlabels hρ hB ha habound hsmall Subset.rfl).weight hF hFbound
  unfold historyMarkedExpectation
  simpa using path.family.integral_lipschitz μ (path.lipschitz (convex_Icc ..) (by positivity))

include hT in
/-- In particular, expectation regularity on the entire interval is proved, not assumed. -/
theorem historyMarkedExpectation_absolutelyContinuous :
    AbsolutelyContinuousOnInterval (historyMarkedExpectation ρ μ a F) 0 T := by
  have hl := historyMarkedExpectation_lipschitzOn hlabels hρ hB
    μ ha habound hsmall hF hM hFbound
  rw [← uIcc_of_le hT] at hl
  exact hl.absolutelyContinuousOnInterval

end NearlyMinimax
