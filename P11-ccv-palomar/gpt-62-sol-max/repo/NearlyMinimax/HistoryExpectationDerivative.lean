module

public import NearlyMinimax.HistoryDensityDerivative
public import NearlyMinimax.BoundedPath


@[expose] public section

/-!
# Uniform regularity of the marked-history density path
-/

noncomputable section
open MeasureTheory Filter Set
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

namespace HistoryPriorBounds

variable {dependent : J → J → Prop} {Δ : ℕ} {T B : ℝ}
    {E : Type*} [MeasurableSpace E] {π : Measure E} [IsProbabilityMeasure π]
    {a : E → ℝ} (P : HistoryPriorBounds dependent Δ π a T B)
include P

/-- Uniform bounds on the density path and its derivative, on any subinterval. -/
theorem density_path_bounds {s : Set ℝ} (hs : s ⊆ Icc 0 T) :
    BoundedPath s (fun u => historyMarkedDensity dependent (historyReferenceRho Δ) u a)
        ((3 / 2 : ℝ) ^ Fintype.card J) ∧
      BoundedPath s (fun u => historyMarkedDensityDerivative dependent (historyReferenceRho Δ) u a)
        ((historyReferenceRho Δ)⁻¹ * (Fintype.card J : ℝ) * B * (3 / 2 : ℝ) ^ Fintype.card J) := by
  let ρ := historyReferenceRho Δ
  have hρ : 0 < ρ := historyReferenceRho_pos Δ
  have hB := P.bound_nonneg
  refine ⟨.of_abs (fun u => historyMarkedDensity_measurable dependent ρ u a P.measurable) (by positivity) ?_,
    .of_abs (fun u => historyMarkedDensityDerivative_measurable dependent ρ u a P.measurable) (by positivity) ?_⟩
  · intro u hu h
    rw [abs_of_nonneg (P.density_nonneg (hs hu) h)]
    exact (P.density_bounds (hs hu) h).2
  · exact fun u hu => P.densityDerivative_abs_le (hs hu)

end HistoryPriorBounds
end NearlyMinimax
