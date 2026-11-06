module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyMeanNorm
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyProjection
public import HypoellipticAleksandrov.Parabolic.ScalingMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.ScalingMeasure

open private HypoellipticAleksandrov.Parabolic.map_restrict_parabolicAffine from HypoellipticAleksandrov.Parabolic.ScalingMeasure


/-!
# Normalized mean-norm transport on parabolic Morrey boxes

This file transports normalized volume and its direct integral and `L^(d + 1)`
consequences from the literal unit forward box to positive-radius physical
forward boxes.  The Jacobian cancels inside the normalized measure, so the
authoritative extended mean norm is exactly affine covariant.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped ENNReal

variable {d : Nat} (t₀ : Real) (v₀ : PDE.Vec d) {r : Real} (hr : 0 < r)




include hr in
/-- Positive parabolic affine scaling sends normalized volume on the literal
unit forward box to normalized volume on its literal forward physical image. -/
theorem map_parabolicNormalizedVolumeOn_parabolicMorreyUnitBox
     :
    Measure.map (parabolicAffine t₀ v₀ r)
      (parabolicNormalizedVolumeOn (parabolicMorreyUnitBox d)) =
      parabolicNormalizedVolumeOn (parabolicBox 1 r t₀ v₀) := by
  let U  := parabolicMorreyUnitBox d
  let Q  := parabolicBox 1 r t₀ v₀
  let a  := ENNReal.ofReal (r ^ (d + 2))

  have hinv : ENNReal.ofReal ((r ^ (d + 2))⁻¹) = a⁻¹ := by
    exact ENNReal.ofReal_inv_of_pos (pow_pos hr _)
  have himage : parabolicAffine t₀ v₀ r '' U = Q := by
    exact (parabolicAffine_image_parabolicMorreyUnitBox t₀ v₀ hr)
  have hvolume : volume Q = a * volume U := by
    rw [← himage]
    exact (volume_parabolicAffine_image_eq t₀ v₀ hr U)

  have hUpos  := (ENNReal.toReal_pos_iff.mp (volume_parabolicMorreyUnitBox_toReal_pos d)).1

  have hscalar : (volume U)⁻¹ * a⁻¹ = (volume Q)⁻¹ := by
    rw [hvolume, ENNReal.mul_inv (a := a) (b := volume U)
      (Or.inr (volume_parabolicMorreyUnitBox_ne_top d)) (Or.inr hUpos.ne')]
    exact mul_comm _ _
  change Measure.map (parabolicAffine t₀ v₀ r)
      ((volume U)⁻¹ • volume.restrict U) =
    (volume Q)⁻¹ • volume.restrict Q
  rw [Measure.map_smul, _root_.HypoellipticAleksandrov.Parabolic.map_restrict_parabolicAffine t₀ v₀ hr U,
    map_volume_parabolicAffine t₀ v₀ hr, hinv, Measure.restrict_smul,
    himage, smul_smul, hscalar]
  exact (contDiff_parabolicAffine t₀ v₀ r).continuous.measurable.aemeasurable

variable (f : HypoellipticAleksandrov.Parabolic.ScalarField d)

include hr
/-- Normalized `MemLp` on a physical forward box is equivalent to normalized
`MemLp` of its scalar affine pullback on the literal unit forward box. -/
theorem memLp_parabolicNormalizedVolumeOn_parabolicBox_iff

     :
    MemLp f (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 r t₀ v₀)) ↔
      MemLp (pullbackScalar f t₀ v₀ r) (parabolicExponent d)
        (parabolicNormalizedVolumeOn (parabolicMorreyUnitBox d)) := by
  rw [← map_parabolicNormalizedVolumeOn_parabolicMorreyUnitBox t₀ v₀ hr]
  exact ((parabolicAffine_measurableEmbedding hr).memLp_map_measure_iff

       )

/-- The authoritative normalized extended `L^(d+1)` norm is exactly affine
covariant between a physical forward box and the literal unit forward box. -/
theorem parabolicELpMeanNormOn_parabolicBox_eq

     :
    parabolicELpMeanNormOn d f (parabolicBox 1 r t₀ v₀) =
      parabolicELpMeanNormOn d (pullbackScalar f t₀ v₀ r)
        (parabolicMorreyUnitBox d) := by
  unfold parabolicELpMeanNormOn
  rw [← map_parabolicNormalizedVolumeOn_parabolicMorreyUnitBox t₀ v₀ hr]
  exact ((parabolicAffine_measurableEmbedding hr).eLpNorm_map_measure

       )

end HypoellipticAleksandrov.Parabolic
