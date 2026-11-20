module

public import NearlyMinimax.HistoryDensityDerivative
public import NearlyMinimax.BoundedPath


@[expose] public section

/-!
# Differentiating actual marked-history expectations
-/

noncomputable section
open MeasureTheory Filter Set
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

/-- The expectation weighted by the actual source history polynomial. -/
def historyMarkedExpectation {dependent : J → J → Prop} (ρ : ℝ)
    {E : Type*} [MeasurableSpace E] (μ : Measure (HistoryMarked dependent E))
    (a : E → ℝ) (F : HistoryMarked dependent E → ℝ) (t : ℝ) : ℝ :=
  ∫ h, F h * historyMarkedDensity ρ t a h ∂μ

theorem historyActivity_mono {u T B ρ r : ℝ} (hu : u ≤ T) (hB : 0 ≤ B) (hρ : 0 ≤ ρ)
    (h : T * B / ρ ≤ r) : u * B / ρ ≤ r :=
  (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hu hB) hρ).trans h

variable {dependent : J → J → Prop} [Std.Refl dependent] [Std.Symm dependent] {Δ : ℕ}
    (hlabels : DegreeAtMost dependent Δ) {ρ T B : ℝ}
include hlabels

/-- Simultaneous majorants for the density and its time derivative. -/
theorem historyDensityPath (hρ : 0 < ρ) (hB : 0 ≤ B)
    {E : Type*} [MeasurableSpace E] {a : E → ℝ} (ha : Measurable a) (hab : ∀ e, |a e| ≤ B)
    (hsmall : T * B / ρ ≤ historyActivityRadius Δ) {s : Set ℝ} (hs : s ⊆ Icc 0 T) :
    BoundedPath s (fun t (h : HistoryMarked dependent E) => historyMarkedDensity ρ t a h)
      (fun t h => historyMarkedDensityDerivative ρ t a h) ((3 / 2) ^ Fintype.card J)
      (ρ⁻¹ * Fintype.card J * B * (3 / 2) ^ Fintype.card J) := by
  have hguard u (hu : u ∈ s) := historyActivity_mono (hs hu).2 hB hρ.le hsmall
  refine ⟨⟨fun u => historyMarkedDensity_measurable dependent ρ u ha, ?_⟩,
    ⟨fun u => historyMarkedDensityDerivative_measurable dependent ρ u ha, fun u hu =>
      historyMarkedDensityDerivative_bound hlabels hρ (hs hu).1 hB hab (hguard u hu)⟩,
    fun h u _ => historyMarkedDensity_hasDerivAt ρ u a h⟩
  intro u hu h
  have hb := historyMarkedDensity_bounds hlabels hρ (hs hu).1 hB hab (hguard u hu) h
  exact abs_le.mpr ⟨by linarith [show 0 ≤ (1 / 2 : ℝ) ^ Fintype.card J by positivity,
    show 0 ≤ (3 / 2) ^ Fintype.card J by positivity], hb.2⟩

end NearlyMinimax
