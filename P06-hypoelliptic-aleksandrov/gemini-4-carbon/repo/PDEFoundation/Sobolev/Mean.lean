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

/-- A scalar function has zero integral on `U`. -/
noncomputable def MeanZeroOn {d : ℕ}
    (U : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  ∫ x in U, u x ∂volume = 0

/-- The arithmetic integral average on `U`.

This total definition is retained for compatibility.  Its mathematical
average properties require `0 < volume U` and `volume U < ∞`. -/
noncomputable def integralAverage {d : ℕ}
    (U : Set (Vec d)) (u : Vec d → ℝ) : ℝ :=
  (volume U).toReal⁻¹ * ∫ x in U, u x ∂volume

/-- The arithmetic average is literally integration against normalized
restricted volume. The identity is total, including zero- and
infinite-volume sets. -/
theorem integral_normalizedVolumeOn_eq_integralAverage
    {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) :
    ∫ x, u x ∂normalizedVolumeOn U =
      integralAverage U u := by
  rw [normalizedVolumeOn, integral_smul_measure,
    ENNReal.toReal_inv]
  rfl

theorem integralAverage_eq_zero_of_meanZeroOn {d : ℕ}
    {U : Set (Vec d)} {u : Vec d → ℝ}
    (hu : MeanZeroOn U u) :
    integralAverage U u = 0 := by
  rw [integralAverage, hu, mul_zero]

/-- Subtracting the arithmetic average produces a zero-mean function on a
positive finite-volume set. -/
theorem meanZeroOn_sub_integralAverage
    {d : ℕ} {U : Set (Vec d)} {u : Vec d → ℝ}
    (hu : IntegrableOn u U volume)
    (hUPos : 0 < volume U) (hUTop : volume U < ∞) :
    MeanZeroOn U (fun x => u x - integralAverage U u) := by
  have hconst :
      IntegrableOn (fun _ : Vec d => integralAverage U u)
        U volume :=
    integrableOn_const hUTop.ne
  have hvolReal : (volume U).toReal ≠ 0 :=
    (ENNReal.toReal_pos hUPos.ne' hUTop.ne).ne'
  unfold MeanZeroOn
  rw [integral_sub hu hconst, setIntegral_const]
  change
    (∫ x in U, u x ∂volume) -
      (volume U).toReal * integralAverage U u = 0
  unfold integralAverage
  field_simp [hvolReal]
  ring

/-- Subtracting the arithmetic average is exactly the volume-normalized
average of all pointwise differences from a fixed point.

This identity is the Jensen step in the convex-domain Poincaré argument. -/
theorem sub_integralAverage_eq_volumeAverage_sub
    {d : ℕ} {U : Set (Vec d)} {u : Vec d → ℝ}
    (hu : IntegrableOn u U volume)
    (hUPos : 0 < volume U) (hUTop : volume U < ∞)
    (x : Vec d) :
    u x - integralAverage U u =
      (volume U).toReal⁻¹ *
        ∫ y in U, (u x - u y) ∂volume := by
  have hvolReal : (volume U).toReal ≠ 0 :=
    (ENNReal.toReal_pos hUPos.ne' hUTop.ne).ne'
  have hconstInt :
      IntegrableOn (fun _ : Vec d => u x) U volume :=
    integrableOn_const hUTop.ne
  have hconst :
      ∫ y in U, (u x : ℝ) ∂volume =
        (volume U).toReal * u x := by
    rw [setIntegral_const]
    rfl
  let I : ℝ := ∫ y in U, u y ∂volume
  have hscale :
      u x - (volume U).toReal⁻¹ * I =
        (volume U).toReal⁻¹ *
          ((volume U).toReal * u x - I) := by
    field_simp [hvolReal]
  calc
    u x - integralAverage U u =
        u x - (volume U).toReal⁻¹ * I := by
      rfl
    _ = (volume U).toReal⁻¹ *
          ((volume U).toReal * u x - I) :=
      hscale
    _ = (volume U).toReal⁻¹ *
          ((∫ y in U, u x ∂volume) - I) := by
      rw [← hconst]
    _ = (volume U).toReal⁻¹ *
        ∫ y in U, (u x - u y) ∂volume := by
      rw [integral_sub hconstInt hu]

/-- Probability-measure form of the mean-difference identity. -/
theorem sub_integralAverage_eq_integral_sub_normalizedVolumeOn
    {d : ℕ} {U : Set (Vec d)} {u : Vec d → ℝ}
    (hu : IntegrableOn u U volume)
    (hUPos : 0 < volume U) (hUTop : volume U < ∞)
    (x : Vec d) :
    u x - integralAverage U u =
      ∫ y, (u x - u y) ∂normalizedVolumeOn U := by
  rw [normalizedVolumeOn, integral_smul_measure,
    ENNReal.toReal_inv]
  exact sub_integralAverage_eq_volumeAverage_sub
    hu hUPos hUTop x

/-- Jensen's inequality for the mean-subtracted value, written on normalized
restricted volume. -/
theorem abs_sub_integralAverage_rpow_le_integral_abs_sub_rpow
    {d : ℕ} {U : Set (Vec d)} {u : Vec d → ℝ}
    {p : ℝ} (hp : 1 ≤ p)
    (hu : IntegrableOn u U volume)
    (hUPos : 0 < volume U) (hUTop : volume U < ∞)
    (x : Vec d)
    (hup : IntegrableOn (fun y => |u x - u y| ^ p)
      U volume) :
    |u x - integralAverage U u| ^ p ≤
      ∫ y, |u x - u y| ^ p ∂normalizedVolumeOn U := by
  let : IsProbabilityMeasure (normalizedVolumeOn U) :=
    isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top
      hUPos hUTop
  have hconst :
      IntegrableOn (fun _ : Vec d => u x) U volume :=
    integrableOn_const hUTop.ne
  have hdiff :
      Integrable (fun y => u x - u y)
        (normalizedVolumeOn U) :=
    integrable_normalizedVolumeOn_of_integrableOn
      (hconst.sub hu) hUPos
  have hpowDiff :
      Integrable (fun y => |u x - u y| ^ p)
        (normalizedVolumeOn U) :=
    integrable_normalizedVolumeOn_of_integrableOn
      hup hUPos
  rw [sub_integralAverage_eq_integral_sub_normalizedVolumeOn
    hu hUPos hUTop x]
  exact abs_integral_rpow_le_integral_abs_rpow
    hp hdiff hpowDiff

theorem MeanZeroOn.congr_ae {d : ℕ}
    {U : Set (Vec d)} {u v : Vec d → ℝ}
    (hu : MeanZeroOn U u) (huv : u =ᵐ[volumeOn U] v) :
    MeanZeroOn U v := by
  unfold MeanZeroOn at hu ⊢
  have hint :
      (∫ x, u x ∂volumeOn U) =
        ∫ x, v x ∂volumeOn U :=
    integral_congr_ae huv
  change (∫ x, v x ∂volumeOn U) = 0
  rw [← hint]
  simpa [volumeOn] using hu

end PDE
