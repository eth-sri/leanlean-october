module

public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyMeanNorm
public import HypoellipticAleksandrov.Parabolic.ParabolicMorreyProjection
public import HypoellipticAleksandrov.Parabolic.ScalingMeasure
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Normalized mean-norm transport on parabolic Morrey boxes

This file transports normalized volume and its direct integral and `L^(d + 1)`
consequences from the literal unit forward box to positive-radius physical
forward boxes.  The Jacobian cancels inside the normalized measure, so the
authoritative extended mean norm is exactly affine covariant.
-/

@[expose] public section


namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped ENNReal

variable {d : Nat} (t₀ : Real) (v₀ : PDE.Vec d) {r : Real}


/-- Positive parabolic affine scaling sends normalized volume on the literal
unit forward box to normalized volume on its literal forward physical image. -/
theorem map_parabolicNormalizedVolumeOn_parabolicMorreyUnitBox
     (hr : 0 < r) :
    Measure.map (parabolicAffine t₀ v₀ r)
      (parabolicNormalizedVolumeOn (parabolicMorreyUnitBox d)) =
      parabolicNormalizedVolumeOn (parabolicBox 1 r t₀ v₀) := by
  let U  := parabolicMorreyUnitBox d
  let Q  := parabolicBox 1 r t₀ v₀
  let a  := ENNReal.ofReal (r ^ (d + 2))
  have hpow : 0 < r ^ (d + 2) := pow_pos hr _
  have hinv : ENNReal.ofReal ((r ^ (d + 2))⁻¹) = a⁻¹ := by
    aesop
  have himage : parabolicAffine t₀ v₀ r '' U = Q := by
    simpa using
      (parabolicAffine_image_parabolicMorreyUnitBox t₀ v₀ hr)
  have hvolume : volume Q = a * volume U := by
    rw [← himage]
    simpa using
      (volume_parabolicAffine_image_eq t₀ v₀ hr U)
  have hUreal : 0 < (volume U).toReal := by
    simpa using volume_parabolicMorreyUnitBox_toReal_pos d
  have hUpos  := (ENNReal.toReal_pos_iff.mp hUreal).1
  have hUtop : volume U ≠ ∞ := by
    aesop
  have hscalar : (volume U)⁻¹ * a⁻¹ = (volume Q)⁻¹ := by
    rw [hvolume, ENNReal.mul_inv (a := a) (b := volume U)
      (Or.inr hUtop) (Or.inr hUpos.ne')]
    ring
  change Measure.map (parabolicAffine t₀ v₀ r)
      ((volume U)⁻¹ • volume.restrict U) =
    (volume Q)⁻¹ • volume.restrict Q
  rw [Measure.map_smul, map_restrict_parabolicAffine t₀ v₀ hr,
    map_volume_parabolicAffine t₀ v₀ hr, hinv, Measure.restrict_smul,
    himage, smul_smul, hscalar]
  exact (contDiff_parabolicAffine t₀ v₀ r).continuous.measurable.aemeasurable

/-- Normalized `MemLp` on a physical forward box is equivalent to normalized
`MemLp` of its scalar affine pullback on the literal unit forward box. -/
theorem memLp_parabolicNormalizedVolumeOn_parabolicBox_iff
     (hr : 0 < r)
    (f : TimeVelocity d -> Real) :
    MemLp f (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 r t₀ v₀)) ↔
      MemLp (pullbackScalar f t₀ v₀ r) (parabolicExponent d)
        (parabolicNormalizedVolumeOn (parabolicMorreyUnitBox d)) := by
  rw [← map_parabolicNormalizedVolumeOn_parabolicMorreyUnitBox t₀ v₀ hr]
  simpa only [pullbackScalar] using
    ((parabolicAffine_measurableEmbedding hr).memLp_map_measure_iff
      (μ := parabolicNormalizedVolumeOn _)
      (g := f) (p := parabolicExponent d))

/-- The authoritative normalized extended `L^(d+1)` norm is exactly affine
covariant between a physical forward box and the literal unit forward box. -/
theorem parabolicELpMeanNormOn_parabolicBox_eq
     (hr : 0 < r)
    (f : TimeVelocity d -> Real) :
    parabolicELpMeanNormOn d f (parabolicBox 1 r t₀ v₀) =
      parabolicELpMeanNormOn d (pullbackScalar f t₀ v₀ r)
        (parabolicMorreyUnitBox d) := by
  unfold parabolicELpMeanNormOn
  rw [← map_parabolicNormalizedVolumeOn_parabolicMorreyUnitBox t₀ v₀ hr]
  simpa only [pullbackScalar] using
    ((parabolicAffine_measurableEmbedding hr).eLpNorm_map_measure
      (μ := parabolicNormalizedVolumeOn _)
      (g := f) (p := parabolicExponent d))

end HypoellipticAleksandrov.Parabolic
