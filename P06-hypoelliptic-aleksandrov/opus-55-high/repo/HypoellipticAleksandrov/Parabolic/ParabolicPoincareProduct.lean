module

public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareFoundation
public import PDEFoundation.Measure.NormalizedLp
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Product disintegration on the parabolic Morrey unit box

This module records the literal time-outer product measure on the parabolic
Morrey unit box and the corresponding extended `L^(d + 1)` disintegration.
The result is deliberately finite-free: it uses nonnegative Tonelli and
extended-real power algebra, so it also covers infinite norms.
-/

@[expose] public section


namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped ENNReal

variable (d : Nat)

theorem parabolicExponent_ne_zero  : parabolicExponent d ≠ 0 := by
  simp [parabolicExponent]

theorem parabolicExponent_ne_top  : parabolicExponent d ≠ ∞ := by
  simp [parabolicExponent]

/-- Restricted time--velocity volume on the literal unit box is the time-outer
product of the literal unit interval and velocity cube. -/
theorem parabolicMorreyUnitBox_restrict_volume_eq_prod  :
    volume.restrict (parabolicMorreyUnitBox d) =
      (volume.restrict (Set.Ioo (0 : Real) 1)).prod
        (volume.restrict (velocityCube (0 : PDE.Vec d) 1)) := by
  rw [parabolicMorreyUnitBox, volume_timeVelocity_eq_prod]
  symm
  simpa [parabolicBox] using Measure.prod_restrict (μ := volume)
    (ν := volume) _
    _

/-- The time-indexed velocity-slice norm is a.e. measurable. -/
theorem aemeasurable_parabolicMorreyUnitVelocitySlice_eLpNorm
    {d : Nat} (f : TimeVelocity d -> Real)
    (hf : AEMeasurable f (volume.restrict (parabolicMorreyUnitBox d))) :
    AEMeasurable
      (fun t : Real =>
        PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
          (parabolicExponent d) (fun v => f (t, v)))
      (volume.restrict (Set.Ioo (0 : Real) 1)) := by
  let μ : Measure Real := volume.restrict (Set.Ioo (0) 1)
  let ν : Measure (PDE.Vec d) :=
    volume.restrict (velocityCube (0) 1)
  let p  := parabolicExponent d
  have hbox : volume.restrict (parabolicMorreyUnitBox d) = μ.prod ν := by
    simpa using parabolicMorreyUnitBox_restrict_volume_eq_prod d
  have hf' : AEMeasurable f (μ.prod ν) := by
    simp_all
  have hp_ne_zero : p ≠ 0 := by
    simpa using parabolicExponent_ne_zero d
  have hp_ne_top : p ≠ ∞ := by
    simpa using parabolicExponent_ne_top d
  have hpow : AEMeasurable
      (Function.uncurry fun t : Real => fun v : PDE.Vec d =>
        ‖f (t, v)‖ₑ ^ p.toReal) (μ.prod ν) := by
    fun_prop
  have hinner  :=
    hpow.lintegral_prod_right
  have hroot : AEMeasurable
      (fun t => (∫⁻ v, ‖f _‖ₑ ^ p.toReal ∂ν) ^ (1 / p.toReal)) μ :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hinner
  refine hroot.congr ?_
  filter_upwards [hf'.aestronglyMeasurable.prodMk_left] with t ht
  exact (eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top ht).symm

/-- Exact time-outer disintegration of the extended parabolic norm. -/
theorem parabolicELpNormOn_parabolicMorreyUnitBox_eq_time_eLpNorm_velocitySlice
    {d : Nat} (f : TimeVelocity d -> Real)
    (hf : AEMeasurable f (volume.restrict (parabolicMorreyUnitBox d))) :
    parabolicELpNormOn d f (parabolicMorreyUnitBox d) =
      MeasureTheory.eLpNorm
        (fun t : Real =>
          PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
            (parabolicExponent d) (fun v => f (t, v)))
        (parabolicExponent d)
        (volume.restrict (Set.Ioo (0 : Real) 1)) := by
  let μ : Measure Real := volume.restrict (Set.Ioo (0) 1)
  let ν : Measure (PDE.Vec d) :=
    volume.restrict (velocityCube (0) 1)
  let p : ℝ≥0∞ := parabolicExponent d
  have hbox : volume.restrict (parabolicMorreyUnitBox d) = μ.prod ν := by
    simpa using parabolicMorreyUnitBox_restrict_volume_eq_prod d
  have hf' : AEMeasurable f (μ.prod ν) := by
    simp_all
  have hp_ne_zero : p ≠ 0 := by
    simpa using parabolicExponent_ne_zero d
  have hp_ne_top : p ≠ ∞ := by
    simpa using parabolicExponent_ne_top d
  have hp_toReal_pos : 0 < p.toReal :=
    ENNReal.toReal_pos hp_ne_zero hp_ne_top
  have hpow : AEMeasurable
      (Function.uncurry fun t : Real => fun v : PDE.Vec d =>
        ‖f (t, v)‖ₑ ^ p.toReal) (μ.prod ν) := by
    fun_prop
  calc
    eLpNorm f p (volume.restrict (parabolicMorreyUnitBox d)) =
        (∫⁻ z, ‖f z‖ₑ ^ p.toReal ∂μ.prod ν) ^ (1 / p.toReal) := by
      rw [hbox, eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top
        hf'.aestronglyMeasurable]
    _ = (∫⁻ t, ∫⁻ v, ‖f (t, v)‖ₑ ^ p.toReal ∂ν ∂μ) ^ (1 / p.toReal) := by
      congr 1
      exact
        lintegral_prod (μ := μ) (ν := ν)
          (Function.uncurry fun t : Real => fun v : PDE.Vec d =>
            ‖f (t, v)‖ₑ ^ p.toReal) hpow
    _ = (∫⁻ t,
        (PDE.eLpNormOn (velocityCube (0) 1) p
          (fun v => f (t, v))) ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
      apply congrArg (fun q : ℝ≥0∞ => q ^ (1 / p.toReal))
      apply lintegral_congr_ae
      filter_upwards [hf'.aestronglyMeasurable.prodMk_left] with t ht
      change ∫⁻ v, ‖f (t, v)‖ₑ ^ p.toReal ∂ν =
        (eLpNorm (fun v : PDE.Vec d => f (t, v)) p ν) ^ p.toReal
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top ht,
        ← ENNReal.rpow_mul, one_div_mul_cancel (ne_of_gt hp_toReal_pos),
        ENNReal.rpow_one]
    _ = eLpNorm
        (fun t : Real => PDE.eLpNormOn (velocityCube (0) 1) p
          (fun v => f (t, v))) p μ := by
      have hslice := aemeasurable_parabolicMorreyUnitVelocitySlice_eLpNorm f hf
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top
        hslice.aestronglyMeasurable]
      rfl

end HypoellipticAleksandrov.Parabolic
