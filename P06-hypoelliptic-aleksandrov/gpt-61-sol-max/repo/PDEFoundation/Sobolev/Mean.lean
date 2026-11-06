module

public import PDEFoundation.Measure.AffineVolume
public import PDEFoundation.Measure.Jensen
public import PDEFoundation.Measure.NormalizedLp
import Aesop



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

variable {d : ℕ}

variable (U : Set (Vec d)) (u : Vec d → ℝ)

/-- A scalar function has zero integral on `U`. -/
noncomputable def MeanZeroOn
     : Prop :=
  ∫ x in U, u x = 0

/-- The arithmetic integral average on `U`.

This total definition is retained for compatibility.  Its mathematical
average properties require `0 < volume U` and `volume U < ∞`. -/
noncomputable def integralAverage
     : ℝ :=
  (volume U).toReal⁻¹ * ∫ x in U, u x

/-- The arithmetic average is literally integration against normalized
restricted volume. The identity is total, including zero- and
infinite-volume sets. -/
theorem integral_normalizedVolumeOn_eq_integralAverage
      :
    ∫ x, u x ∂normalizedVolumeOn U =
      integralAverage U u := by
  simp_all [normalizedVolumeOn] <;> aesop

variable {U : Set (Vec d)}

variable {u : Vec d → ℝ}

theorem integralAverage_eq_zero_of_meanZeroOn

    (hu : MeanZeroOn U u) :
    integralAverage U u = 0 := by
  rw [integralAverage, hu, mul_zero]

variable (hu : IntegrableOn u U volume) (hUPos : 0 < volume U) (hUTop : volume U < ∞)

include hu hUPos hUTop in
/-- Subtracting the arithmetic average produces a zero-mean function on a
positive finite-volume set. -/
theorem meanZeroOn_sub_integralAverage

     :
    MeanZeroOn U (fun x => u x - integralAverage U u) := by


  unfold MeanZeroOn
  rw [integral_sub hu (integrableOn_const hUTop.ne), setIntegral_const]
  change
    (∫ x in U, u x) -
      (volume U).toReal * integralAverage U u = 0
  unfold integralAverage
  field_simp [((ENNReal.toReal_pos hUPos.ne' hUTop.ne).ne')]
  ring

section
variable (x : Vec d)

include hu hUPos hUTop
/-- Subtracting the arithmetic average is exactly the volume-normalized
average of all pointwise differences from a fixed point.

This identity is the Jensen step in the convex-domain Poincaré argument. -/
theorem sub_integralAverage_eq_volumeAverage_sub


     :
    u x - integralAverage U u =
      (volume U).toReal⁻¹ *
        ∫ y in U, (u x - u y) := by

  have hconstInt :
      IntegrableOn (fun _ : Vec d => u x) U  :=
    integrableOn_const hUTop.ne
  have hconst :
      ∫ y in U, (u x ) =
        (volume U).toReal * u x := by
    rw [setIntegral_const]
    rfl
  let I : ℝ := ∫ y in U, u y

  calc
    u x - integralAverage U u =
        u x - (volume U).toReal⁻¹ * I := rfl
    _ = (volume U).toReal⁻¹ *
          ((volume U).toReal * u x - I) :=
      (by
          field_simp [((ENNReal.toReal_pos hUPos.ne' hUTop.ne).ne')])
    _ = (volume U).toReal⁻¹ *
          ((∫ y in U, u x) - I) := by
      rw [← hconst]
    _ = (volume U).toReal⁻¹ *
        ∫ y in U, (u x - u y) := by
      rw [integral_sub hconstInt hu]

/-- Probability-measure form of the mean-difference identity. -/
theorem sub_integralAverage_eq_integral_sub_normalizedVolumeOn


     :
    u x - integralAverage U u =
      ∫ y, (u x - u y) ∂normalizedVolumeOn U := by
  simp_all [normalizedVolumeOn, sub_integralAverage_eq_volumeAverage_sub]
end


/-- Jensen's inequality for the mean-subtracted value, written on normalized
restricted volume. -/
theorem abs_sub_integralAverage_rpow_le_integral_abs_sub_rpow

    {p : ℝ} (hp : 1 ≤ p)
    (hu : IntegrableOn u U )
    (hUPos : 0 < volume U) (hUTop : volume U < ∞)
    (x : Vec d)
    (hup : IntegrableOn (fun y => |u x - u y| ^ p)
      U ) :
    |u x - integralAverage U u| ^ p ≤
      ∫ y, |u x - u y| ^ p ∂normalizedVolumeOn U := by
  let  :=
    isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top
      hUPos hUTop
  have hconst :
      IntegrableOn (fun _ : Vec d => u x) U  :=
    integrableOn_const hUTop.ne
  have hdiff  :=
    integrable_normalizedVolumeOn_of_integrableOn
      (hconst.sub hu) hUPos
  have hpowDiff  :=
    integrable_normalizedVolumeOn_of_integrableOn
      hup hUPos
  rw [sub_integralAverage_eq_integral_sub_normalizedVolumeOn
    hu hUPos hUTop x]
  exact abs_integral_rpow_le_integral_abs_rpow
    hp hdiff hpowDiff

theorem MeanZeroOn.congr_ae
     {u v : Vec d → ℝ}
    (hu : MeanZeroOn U u) (huv : u =ᵐ[volumeOn U] v) :
    MeanZeroOn U v := by
  unfold MeanZeroOn at hu ⊢

  change (∫ x, v x ∂volumeOn U) = 0
  rw [← (integral_congr_ae huv)]
  exact hu

end PDE
