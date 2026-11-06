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

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory Set
open scoped ENNReal

theorem map_parabolicNormalizedVolumeOn_parabolicMorreyUnitBox
    {d } (t₀ : Real) (v₀ : PDE.Vec d) {r } (hr : 0 < r) :
    Measure.map (parabolicAffine t₀ v₀ r)
      (parabolicNormalizedVolumeOn (parabolicMorreyUnitBox d)) =
      parabolicNormalizedVolumeOn (parabolicBox 1 r t₀ v₀) := by
  let U := parabolicMorreyUnitBox d
  let Q := parabolicBox 1 r t₀ v₀
  let a : ENNReal := ENNReal.ofReal (r ^ (d + 2))
  have hpow : 0 < r ^ (d + 2) := pow_pos hr _
  have hinv : ENNReal.ofReal ((r ^ (d + 2))⁻¹) = a⁻¹ := by
    simpa only [a] using ENNReal.ofReal_inv_of_pos hpow
  have himage : parabolicAffine t₀ v₀ r '' U = Q := by
    simpa only [U, Q] using
      (parabolicAffine_image_parabolicMorreyUnitBox t₀ v₀ hr)
  have hvolume : volume Q = a * volume U := by
    rw [← himage]
    simpa only [a] using
      (volume_parabolicAffine_image_eq t₀ v₀ hr U)
  have hUreal : 0 < (volume U).toReal := by
    simpa only [U] using volume_parabolicMorreyUnitBox_toReal_pos d
  have hUpos : 0 < volume U := (ENNReal.toReal_pos_iff.mp hUreal).1
  have hUtop : volume U ≠ ∞ := by
    simpa only [U] using volume_parabolicMorreyUnitBox_ne_top d
  have hscalar : (volume U)⁻¹ * a⁻¹ = (volume Q)⁻¹ := by
    rw [hvolume, ENNReal.mul_inv (a := a) (b := volume U)
      (Or.inr hUtop) (Or.inr hUpos.ne')]
    exact mul_comm _ _
  change Measure.map (parabolicAffine t₀ v₀ r)
      ((volume U)⁻¹ • volume.restrict U) =
    (volume Q)⁻¹ • volume.restrict Q
  have _h_inl_11 : Measure.map (parabolicAffine t₀ v₀ r) (volume.restrict U) =
      (Measure.map (parabolicAffine t₀ v₀ r) volume).restrict
        (parabolicAffine t₀ v₀ r '' U) := by
      have hpreimage :
          parabolicAffine t₀ v₀ r ⁻¹' (parabolicAffine t₀ v₀ r '' U) = U :=
        preimage_image_eq _ (parabolicAffine_injective hr)
      calc
        Measure.map (parabolicAffine t₀ v₀ r) (volume.restrict U) =
            Measure.map (parabolicAffine t₀ v₀ r)
              (volume.restrict
                (parabolicAffine t₀ v₀ r ⁻¹' (parabolicAffine t₀ v₀ r '' U))) := by
          rw [hpreimage]
        _ = (Measure.map (parabolicAffine t₀ v₀ r) volume).restrict
            (parabolicAffine t₀ v₀ r '' U) :=
          ((parabolicAffine_measurableEmbedding hr).restrict_map volume
            (parabolicAffine t₀ v₀ r '' U)).symm

    /- Positive parabolic affine scaling sends normalized volume on the literal
    unit forward box to normalized volume on its literal forward physical image. -/
  rw [Measure.map_smul, _h_inl_11,
    map_volume_parabolicAffine t₀ v₀ hr, hinv, Measure.restrict_smul,
    himage, smul_smul, hscalar]
  exact (contDiff_parabolicAffine t₀ v₀ r).continuous.measurable.aemeasurable

/- Normalized `MemLp` on a physical forward box is equivalent to normalized
`MemLp` of its scalar affine pullback on the literal unit forward box. -/
theorem memLp_parabolicNormalizedVolumeOn_parabolicBox_iff
    {d } (t₀ : Real) (v₀ : PDE.Vec d) {r } (hr : 0 < r)
    (f : TimeVelocity d -> Real) :
    MemLp f (parabolicExponent d)
      (parabolicNormalizedVolumeOn (parabolicBox 1 r t₀ v₀)) ↔
      MemLp (pullbackScalar f t₀ v₀ r) (parabolicExponent d)
        (parabolicNormalizedVolumeOn (parabolicMorreyUnitBox d)) := by
  rw [← map_parabolicNormalizedVolumeOn_parabolicMorreyUnitBox t₀ v₀ hr]
  simpa only [pullbackScalar] using
    ((parabolicAffine_measurableEmbedding hr).memLp_map_measure_iff
      (μ := parabolicNormalizedVolumeOn (parabolicMorreyUnitBox d))
      (g := f) (p := parabolicExponent d))

/- The authoritative normalized extended `L^(d+1)` norm is exactly affine
covariant between a physical forward box and the literal unit forward box. -/
end HypoellipticAleksandrov.Parabolic
