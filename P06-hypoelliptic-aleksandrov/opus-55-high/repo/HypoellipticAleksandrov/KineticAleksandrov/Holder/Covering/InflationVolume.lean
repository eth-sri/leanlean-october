module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.Inflation
public import HypoellipticAleksandrov.Geometry.KineticPointMeasure
public import PDEFoundation.Measure.BallVolume
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic

/-! # Cylinder volumes by time slicing

This proof uses product Lebesgue measure and the Euclidean-ball volume formula.
It does not use a general kinetic affine-map volume formula.
-/

@[expose] public section


namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory

variable {d : ℕ} (P : KineticPoint d) {r : ℝ}

/-- At a fixed time, the free-transport position condition is an ordinary translated ball. -/
theorem position_ball_slice  (t : ℝ)
    (x : PDE.Vec d) {r : ℝ} (hr : 0 < r) :
    x - P.position - (t-P.time) • P.velocity ∈ PDE.euclideanBall 0 (r ^ 3) ↔
      x ∈ PDE.euclideanBall (P.position+(t-P.time) • P.velocity) (r ^ 3) := by
  rw [PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hr 3),
    PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (pow_pos hr 3), sub_zero]
  ring

/-- Cylinder volume is time length times the two Euclidean ball volumes. -/
theorem volume_cylinder_product  (hr : 0 < r) :
    volume (backwardCylinder P r) = ENNReal.ofReal (r ^ 2) *
      (volume (PDE.euclideanBall (0 : PDE.Vec d) (r ^ 3)) *
        volume (PDE.euclideanBall (0 : PDE.Vec d) r)) := by
  let s := (KineticPoint.equivProd d).symm ⁻¹' backwardCylinder P r
  have hs : MeasurableSet s := (isOpen_cylinder P r).measurableSet.preimage
    (KineticPoint.measurable_equivProd_symm d)
  have hpre : (KineticPoint.equivProd d) ⁻¹' s = backwardCylinder P r := by
    grind
  have hv := (KineticPoint.measurePreserving_equivProd d).measure_preimage hs.nullMeasurableSet
  rw [hpre] at hv
  rw [hv, Measure.volume_eq_prod, Measure.prod_apply hs]
  have hslice (t : ℝ) : Prod.mk t ⁻¹' s =
      if t ∈ Ioo (P.time-r^2) P.time then
        PDE.euclideanBall (P.position+(t-P.time) • P.velocity) (r ^ 3) ×ˢ
          PDE.euclideanBall P.velocity r else ∅ := by
    ext z
    simp only [mem_preimage, s, mem_backwardCylinder_iff, KineticPoint.equivProd,
      Equiv.coe_fn_symm_mk, relativePosition]
    rw [position_ball_slice P t z.1 hr]
    grind
  have hcenter (x : PDE.Vec d) {R : ℝ} (hR : 0 < R) :
      volume (PDE.euclideanBall x R) = volume (PDE.euclideanBall (0 : PDE.Vec d) R) := by
    rw [PDE.volume_euclideanBall_eq_unit_mul_of_pos x hR,
      PDE.volume_euclideanBall_eq_unit_mul_of_pos 0 hR]
  simp_rw [hslice]
  have heq : (fun t : ℝ => volume (if t ∈ Ioo (P.time-r^2) P.time then
        PDE.euclideanBall (P.position+(t-P.time) • P.velocity) (r ^ 3) ×ˢ
          PDE.euclideanBall P.velocity r else ∅)) =
      (Ioo (P.time-r^2) P.time).indicator (fun _ : ℝ =>
        volume (PDE.euclideanBall (0 : PDE.Vec d) (r ^ 3)) *
          volume (PDE.euclideanBall (0 : PDE.Vec d) r)) := by
    funext t
    by_cases ht : t ∈ Ioo (P.time-r^2) P.time
    · simp only [ht, ite_true, indicator_of_mem, Measure.volume_eq_prod,
        Measure.prod_prod, hcenter _ (pow_pos hr 3), hcenter _ hr]
    · simp only [ht, ite_false, measure_empty, indicator_of_notMem ht]
  rw [heq, lintegral_indicator measurableSet_Ioo, lintegral_const,
    Measure.restrict_apply_univ, Real.volume_Ioo]
  ring

/-- Exact homogeneous scaling of cylinder volume, independent of the center. -/
theorem volume_cylinder_eq_unit  (hr : 0 < r) :
    volume (backwardCylinder P r) = ENNReal.ofReal (r ^ (4*d+2)) *
      volume (backwardCylinder (⟨0,0,0⟩ : KineticPoint d) 1) := by
  rw [volume_cylinder_product P hr, volume_cylinder_product _ zero_lt_one]
  rw [PDE.volume_euclideanBall_eq_unit_mul_of_pos 0 (pow_pos hr 3),
    PDE.volume_euclideanBall_eq_unit_mul_of_pos 0 hr]
  simp only [one_pow, ENNReal.ofReal_one]
  have hp : r ^ 2 * (r ^ 3) ^ d * r ^ d = r ^ (4*d+2) := by
    ring
  have hcoeff : ENNReal.ofReal (r ^ (4*d+2)) = ENNReal.ofReal (r ^ 2) *
      ENNReal.ofReal ((r ^ 3) ^ d) * ENNReal.ofReal (r ^ d) := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hr.le 2),
      ← ENNReal.ofReal_mul (by positivity), hp]
  rw [hcoeff]
  ring

/-- Positive-radius cylinders have positive finite volume. -/
theorem volume_cylinder_pos_ne_top 
    (hr : 0 < r) :
    0 < volume (backwardCylinder P r) ∧ volume (backwardCylinder P r) ≠ ⊤ := by
  rw [volume_cylinder_product P hr]
  exact ⟨ENNReal.mul_pos (ENNReal.ofReal_pos.mpr (sq_pos_of_pos hr)).ne'
      (ENNReal.mul_pos (PDE.volume_euclideanBall_pos 0 (pow_pos hr 3)).ne'
        (PDE.volume_euclideanBall_pos 0 hr).ne').ne',
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (PDE.volume_euclideanBall_ne_top 0 (pow_pos hr 3).le)
        (PDE.volume_euclideanBall_ne_top 0 hr.le))⟩

/-- Eightfold centered inflation has exactly the homogeneous volume multiplier. -/
theorem volume_inflatedCylinder  (hr : 0 < r) :
    volume (inflatedCylinder P r 8) = ENNReal.ofReal ((8 : ℝ) ^ (4*d+2)) *
      volume (backwardCylinder P r) := by
  rw [inflatedCylinder, volume_cylinder_eq_unit _ (mul_pos (by norm_num) hr),
    volume_cylinder_eq_unit P hr, mul_pow,
    ENNReal.ofReal_mul (by positivity), mul_assoc]

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
