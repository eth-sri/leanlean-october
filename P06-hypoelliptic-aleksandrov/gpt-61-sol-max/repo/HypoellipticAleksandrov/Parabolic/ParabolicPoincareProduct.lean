module

public import HypoellipticAleksandrov.Parabolic.ParabolicPoincareFoundation
public import PDEFoundation.Measure.NormalizedLp
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Prod
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Measure.DensityNearOneMeasure

open private HypoellipticAleksandrov.Parabolic.parabolicExponent_ne_top from HypoellipticAleksandrov.Measure.DensityNearOneMeasure
open private HypoellipticAleksandrov.Parabolic.parabolicExponent_ne_zero from HypoellipticAleksandrov.Measure.DensityNearOneMeasure


/-!
# Product disintegration on the parabolic Morrey unit box

This module records the literal time-outer product measure on the parabolic
Morrey unit box and the corresponding extended `L^(d + 1)` disintegration.
The result is deliberately finite-free: it uses nonnegative Tonelli and
extended-real power algebra, so it also covers infinite norms.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open MeasureTheory
open scoped ENNReal

variable (d : Nat)







/-- Restricted time--velocity volume on the literal unit box is the time-outer
product of the literal unit interval and velocity cube. -/
theorem parabolicMorreyUnitBox_restrict_volume_eq_prod  :
    volume.restrict (parabolicMorreyUnitBox d) =
      (volume.restrict (Set.Ioo (0 : Real) 1)).prod
        (volume.restrict (velocityCube (0 : PDE.Vec d) 1)) := by
  rw [parabolicMorreyUnitBox, volume_timeVelocity_eq_prod]
  symm
  simpa [parabolicBox] using Measure.prod_restrict (μ := (volume : Measure Real))
    (ν := (volume : Measure (PDE.Vec d))) (Set.Ioo 0 1)
    (velocityCube (0 ) 1)

variable {d : Nat} (f : HypoellipticAleksandrov.Parabolic.ScalarField d) (hf : AEMeasurable f (volume.restrict (parabolicMorreyUnitBox d)))

include hf
/-- The time-indexed velocity-slice norm is a.e. measurable. -/
theorem aemeasurable_parabolicMorreyUnitVelocitySlice_eLpNorm
     :
    AEMeasurable
      (fun t  =>
        PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
          (parabolicExponent d) (fun v => f (t, v)))
      (volume.restrict (Set.Ioo (0 ) 1)) := by
  let μ  := volume.restrict (Set.Ioo (0 : Real) 1)
  let ν  :=
    volume.restrict (velocityCube (0 : PDE.Vec d) 1)
  let p  := parabolicExponent d
  have hbox : volume.restrict (parabolicMorreyUnitBox d) = μ.prod ν := by
    exact parabolicMorreyUnitBox_restrict_volume_eq_prod d
  have hf' : AEMeasurable f (μ.prod ν) := by
    rw [← hbox]
    exact hf


  have hpow : AEMeasurable
      (Function.uncurry fun t  => fun v : PDE.Vec d =>
        ‖f (t, v)‖ₑ ^ p.toReal) (μ.prod ν) := by
    change AEMeasurable (fun z  => ‖f z‖ₑ ^ p.toReal) (μ.prod ν)
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hf'.enorm

  change AEMeasurable
    (fun t  => eLpNorm (fun v : PDE.Vec d => f (t, v)) p ν) μ

  refine (show AEMeasurable
      (fun t => (∫⁻ v, ‖f (t, v)‖ₑ ^ p.toReal ∂ν) ^ (1 / p.toReal)) μ from ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hpow.lintegral_prod_right).congr ?_
  filter_upwards [hf'.aestronglyMeasurable.prodMk_left] with t ht
  exact (eLpNorm_eq_lintegral_rpow_enorm_toReal (show p ≠ 0 by
      exact _root_.HypoellipticAleksandrov.Parabolic.parabolicExponent_ne_zero d) (show p ≠ ∞ by
      exact _root_.HypoellipticAleksandrov.Parabolic.parabolicExponent_ne_top d) ht).symm

/-- Exact time-outer disintegration of the extended parabolic norm. -/
theorem parabolicELpNormOn_parabolicMorreyUnitBox_eq_time_eLpNorm_velocitySlice
     :
    parabolicELpNormOn d f (parabolicMorreyUnitBox d) =
      MeasureTheory.eLpNorm
        (fun t  =>
          PDE.eLpNormOn (velocityCube (0 : PDE.Vec d) 1)
            (parabolicExponent d) (fun v => f (t, v)))
        (parabolicExponent d)
        (volume.restrict (Set.Ioo (0 ) 1)) := by
  let sharedTerm_1c2d66fb7b := ((velocityCube (0 : PDE.Vec d) 1))
  let μ  := volume.restrict (Set.Ioo (0 : Real) 1)
  let ν  :=
    volume.restrict sharedTerm_1c2d66fb7b
  let p  := parabolicExponent d
  have hbox : volume.restrict (parabolicMorreyUnitBox d) = μ.prod ν := by
    exact parabolicMorreyUnitBox_restrict_volume_eq_prod d
  have hf' : AEMeasurable f (μ.prod ν) := by
    rw [← hbox]
    exact hf
  have hp_ne_zero : p ≠ 0 := by
    exact _root_.HypoellipticAleksandrov.Parabolic.parabolicExponent_ne_zero d
  have hp_ne_top : p ≠ ∞ := by
    exact _root_.HypoellipticAleksandrov.Parabolic.parabolicExponent_ne_top d


  change eLpNorm f p (volume.restrict (parabolicMorreyUnitBox d)) =
    eLpNorm
      (fun t  => PDE.eLpNormOn sharedTerm_1c2d66fb7b p
        (fun v => f (t, v))) p μ
  calc
    eLpNorm f p (volume.restrict (parabolicMorreyUnitBox d)) =
        (∫⁻ z, ‖f z‖ₑ ^ p.toReal ∂μ.prod ν) ^ (1 / p.toReal) := by
      rw [hbox, eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top
        hf'.aestronglyMeasurable]
    _ = (∫⁻ t, ∫⁻ v, ‖f (t, v)‖ₑ ^ p.toReal ∂ν ∂μ) ^ (1 / p.toReal) := by
      congr 1
      exact
        lintegral_prod
          (Function.uncurry fun t  => fun v : PDE.Vec d =>
            ‖f (t, v)‖ₑ ^ p.toReal) ((id (Measurable.comp_aemeasurable (Continuous.measurable ENNReal.continuous_rpow_const) (AEMeasurable.enorm hf'))))
    _ = (∫⁻ t,
        (PDE.eLpNormOn sharedTerm_1c2d66fb7b p
          (fun v => f (t, v))) ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
      apply congrArg (fun q : ℝ≥0∞ => q ^ (1 / p.toReal))
      apply lintegral_congr_ae
      filter_upwards [hf'.aestronglyMeasurable.prodMk_left] with t ht
      change ∫⁻ v, ‖f (t, v)‖ₑ ^ p.toReal ∂ν =
        (eLpNorm (fun v  => f (t, v)) p ν) ^ p.toReal
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top ht,
        ← ENNReal.rpow_mul, one_div_mul_cancel (ne_of_gt (ENNReal.toReal_pos hp_ne_zero hp_ne_top)),
        ENNReal.rpow_one]
    _ = eLpNorm
        (fun t  => PDE.eLpNormOn sharedTerm_1c2d66fb7b p
          (fun v => f (t, v))) p μ := by

      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top
        (aemeasurable_parabolicMorreyUnitVelocitySlice_eLpNorm f hf).aestronglyMeasurable]
      simp only [enorm_eq_self]
      rfl

end HypoellipticAleksandrov.Parabolic
