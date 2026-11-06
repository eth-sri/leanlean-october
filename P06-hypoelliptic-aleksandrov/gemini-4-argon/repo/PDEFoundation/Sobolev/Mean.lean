module

public import PDEFoundation.Measure.AffineVolume
public import PDEFoundation.Measure.Jensen
public import PDEFoundation.Measure.NormalizedLp

/-!
# Integral means on native vector domains

The compatibility definitions of zero mean and integral average are kept
separate.  `MeanZeroOn` remains meaningful without dividing by the volume;
results using `integralAverage` state positive finite volume explicitly when
that condition matters.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal Pointwise

/- A scalar function has zero integral on `U`. -/
noncomputable def MeanZeroOn {d }
    (U : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  ∫ x in U, u x ∂volume = 0

/- The arithmetic integral average on `U`.

This total definition is retained for compatibility.  Its mathematical
average properties require `0 < volume U` and `volume U < ∞`. -/
noncomputable def integralAverage {d }
    (U : Set (Vec d)) (u : Vec d → ℝ) : ℝ :=
  (volume U).toReal⁻¹ * ∫ x in U, u x ∂volume

/- The arithmetic average is literally integration against normalized
restricted volume. The identity is total, including zero- and
infinite-volume sets. -/
theorem integral_normalizedVolumeOn_eq_integralAverage
    {d } (U : Set (Vec d)) (u : Vec d → ℝ) :
    ∫ x, u x ∂normalizedVolumeOn U =
      integralAverage U u := by
  rw [normalizedVolumeOn, integral_smul_measure,
    ENNReal.toReal_inv]
  rfl

theorem MeanZeroOn.congr_ae {d U} {u v : Vec d → ℝ}
    (hu : MeanZeroOn U u) (huv : u =ᵐ[volumeOn U] v) :
    MeanZeroOn U v := by
  unfold MeanZeroOn at hu ⊢
  have hint :=
    integral_congr_ae huv
  change (∫ x, v x ∂volumeOn U) = 0
  rw [← hint]
  simpa [volumeOn] using hu

end PDE
