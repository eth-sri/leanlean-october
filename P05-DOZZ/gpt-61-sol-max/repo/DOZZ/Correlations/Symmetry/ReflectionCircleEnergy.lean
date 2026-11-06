/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Symmetry.ReflectionCircleTransport
public import DOZZ.Correlations.Symmetry.ReflectionTestCovariance
public section
open MeasureTheory Filter
open scoped Topology
namespace DOZZ.Proofs

variable (x : ℂ) (r : ℝ)

include x r in
/-- The mixed energy transforms with both pinning corrections. -/
theorem reflection_circle_cross  (f : TestFn) :
    circleCross (1 - x) r (symmetryReflectionTest f) = circleCross x r f +
      (∫ z, f z * symmetryReflectionPotential z) +
      testMass f * (∫ z, symmetryReflectionPotential z ∂circleMeasure x r) := by
  have hc : Continuous (fun z => ∫ w, gffKernel z w ∂circleMeasure x r) := by
    exact continuous_circleKernelPotential x r
  have hi : Integrable (fun z => f z * ∫ w, gffKernel z w ∂circleMeasure x r) :=
    (f.continuous.mul hc).integrable_of_hasCompactSupport f.hasCompactSupport.mul_right
  have hd : Integrable (fun z => f z * symmetryReflectionPotential z) :=
    (f.continuous.mul symmetryReflectionPotential_continuous).integrable_of_hasCompactSupport
      f.hasCompactSupport.mul_right
  have hm : Integrable (fun z : ℂ => f z) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  unfold circleCross
  rw [← symmetryReflection_integral (fun z => symmetryReflectionTest f z *
    ∫ w, gffKernel z w ∂circleMeasure (1 - x) r)]
  change (∫ z, f (1 - (1 - z)) *
    ∫ w, gffKernel (1 - z) w ∂circleMeasure (1 - x) r) = _
  simp only [show ∀ z : ℂ, 1 - (1 - z) = z from symmetryReflection_involutive]
  simp_rw [symmetryReflection_circle_kernel, mul_add]
  have ho := integral_add (hi.add hd)
    (hm.mul_const (∫ w, symmetryReflectionPotential w ∂circleMeasure x r))
  have hin := integral_add hi hd
  simp only [Pi.add_def] at ho hin
  rw [ho, hin, integral_mul_const]
  rfl

include x r in
/-- Circle self-energy transforms by twice the mean pinning correction. -/
theorem reflection_circle_self  :
    circleSelfEnergy (1 - x) r = circleSelfEnergy x r +
      2 * (∫ z, symmetryReflectionPotential z ∂circleMeasure x r) := by
  rw [circleSelfEnergy_eq, circleSelfEnergy_eq, symmetryReflection_circle_potential]
  ring

include x r in
/-- Reflection preserves the zero-gap limit for normalized weak circle approximations. -/
theorem reflection_circle_energy_gap  (f : TestFn) :
    circleEnergyGap (1 - x) r (symmetryReflectionTest f) = circleEnergyGap x r f +
      2 * (testMass f - 1) * ((∫ z, f z * symmetryReflectionPotential z) -
        (∫ z, symmetryReflectionPotential z ∂circleMeasure x r)) := by
  unfold circleEnergyGap
  rw [gffCov_symmetryReflectionTest, reflection_circle_cross, reflection_circle_self]
  ring
end DOZZ.Proofs
