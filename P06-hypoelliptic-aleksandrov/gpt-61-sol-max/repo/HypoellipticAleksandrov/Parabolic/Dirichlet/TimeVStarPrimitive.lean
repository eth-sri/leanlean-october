module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTests
public import PDEFoundation.Sobolev.OneDimensional.PrimitiveWeakIdentity
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Reverse-time dual Bochner primitives

This module constructs the literal restricted-measure Bochner primitive of a
reverse-time `L²(V*)` curve.  It contains no representative, trace, energy,
weak PDE, or Lions--Magenes assertion.
-/

@[expose] public section

open MeasureTheory Set


noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {d : ℕ} {Ω : PDE.VelocityRegion d} (hΩ : IsOpen Ω) (T : ℝ) (g : ReverseTimeL2VStar hΩ T)

private theorem integrable_vstar
     :
    Integrable (fun tau => g tau) (reverseTimeVolume T) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T))
    infer_instance

  exact (MeasureTheory.Lp.memLp g).integrable (by norm_num)

/-- The restricted-measure Bochner primitive of a reverse-time dual curve. -/
def reverseTimeVStarPrimitive
     :
    ℝ → H10HilbertGraphDual hΩ :=
  fun t => ∫ tau in Set.Ioc 0 t, g tau ∂reverseTimeVolume T

/-- The dual primitive is continuous on the closed reverse-time interval. -/
theorem continuousOn_reverseTimeVStarPrimitive
     :
    ContinuousOn (reverseTimeVStarPrimitive hΩ T g) (Set.Icc 0 T) := by
  letI : NullSingletonClass (reverseTimeVolume T) := by
    change NullSingletonClass (volume.restrict (Ioo (0 : ℝ) T))
    infer_instance
  exact intervalIntegral.continuousOn_primitive
    (integrable_vstar hΩ T g).integrableOn

/-- The restricted-measure primitive vanishes at time zero. -/
theorem reverseTimeVStarPrimitive_zero
     :
    reverseTimeVStarPrimitive hΩ T g 0 = 0 := by
  change ∫ tau in Set.Ioc 0 0, g tau ∂reverseTimeVolume T = 0
  simp

/-- Increments of the dual primitive are the corresponding restricted-time integrals. -/
theorem reverseTimeVStarPrimitive_sub

    {s t : ℝ} (hs : s ∈ Set.Icc 0 T) (ht : t ∈ Set.Icc 0 T)
    (hst : s ≤ t) :
    reverseTimeVStarPrimitive hΩ T g t -
        reverseTimeVStarPrimitive hΩ T g s =
      ∫ tau in Set.Ioc s t, g tau ∂reverseTimeVolume T := by
  change (∫ tau in Ioc 0 t, g tau ∂reverseTimeVolume T) -
      ∫ tau in Ioc 0 s, g tau ∂reverseTimeVolume T = _
  rw [← intervalIntegral.integral_of_le ht.1,
    ← intervalIntegral.integral_of_le hs.1,
    intervalIntegral.integral_interval_sub_left
      (integrable_vstar hΩ T g).intervalIntegrable
      (integrable_vstar hΩ T g).intervalIntegrable,
    intervalIntegral.integral_of_le hst]

variable (v : H10HilbertGraph hΩ)

/-- Evaluation by a fixed spatial test commutes with the dual primitive. -/
theorem reverseTimeVStarPrimitive_apply

     (t : ℝ) :
    reverseTimeVStarPrimitive hΩ T g t v =
      ∫ tau in Set.Ioc 0 t, (g tau) v ∂reverseTimeVolume T := ContinuousLinearMap.integral_apply
    ((integrable_vstar hΩ T g).integrableOn) v

/-- A fixed-vector evaluation of the dual primitive is integrable in reverse time. -/
theorem integrable_reverseTimeVStarPrimitive_apply

     :
    MeasureTheory.Integrable
      (fun tau => reverseTimeVStarPrimitive hΩ T g tau v)
      (reverseTimeVolume T) := (id
  (IntegrableOn.mono_set
    (ContinuousOn.integrableOn_Icc
      (Continuous.comp_continuousOn (ContinuousLinearMap.continuous ((ContinuousLinearMap.apply ℝ ℝ) v))
        (continuousOn_reverseTimeVStarPrimitive hΩ T g)))
    Ioo_subset_Icc_self))

private theorem primitive_apply_on_Ioo

     {t : ℝ} (ht : t ∈ Ioo 0 T) :
    reverseTimeVStarPrimitive hΩ T g t v =
      PDE.intervalPrimitive 0 (fun s => (g s) v) t := by
  rw [reverseTimeVStarPrimitive_apply]
  change (∫ s in Ioc 0 t, (g s) v ∂reverseTimeVolume T) = _
  rw [show (∫ s in Ioc 0 t, (g s) v ∂reverseTimeVolume T) =
      ∫ s in Ioc 0 t, (g s) v by
    simp only [reverseTimeVolume, reverseTimeOpenInterval,
      Measure.restrict_restrict measurableSet_Ioc]
    rw [inter_eq_left.mpr]
    intro s hs
    exact ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩]
  exact (intervalIntegral.integral_of_le (le_of_lt ht.1)).symm

/-- The dual primitive has weak derivative `g` against compact scalar tests. -/
theorem reverseTimeVStarPrimitive_test_deriv

     (eta : ReverseTimeScalarTest T) :
    MeasureTheory.Integrable
      (fun tau => reverseTimeVStarPrimitive hΩ T g tau v * eta.deriv tau)
      (reverseTimeVolume T) ∧
    MeasureTheory.Integrable (fun tau => (g tau) v * eta tau)
      (reverseTimeVolume T) ∧
    (∫ tau,
      reverseTimeVStarPrimitive hΩ T g tau v * eta.deriv tau
      ∂reverseTimeVolume T) =
      -(∫ tau, (g tau) v * eta tau ∂reverseTimeVolume T) := by
  let sharedTerm_b2f8ccb809 := ((fun tau => reverseTimeVStarPrimitive hΩ T g tau v * eta.deriv tau))

  letI : IsFiniteMeasure (reverseTimeVolume T) := by
    change IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) T))
    infer_instance
  have hqLp : MemLp (fun tau => (g tau) v) 2 (reverseTimeVolume T) :=
    (MeasureTheory.Lp.memLp g).continuousLinearMap_comp
      (ContinuousLinearMap.apply ℝ ℝ v)

  refine ⟨(by
      change IntegrableOn
        sharedTerm_b2f8ccb809
        (Ioo (0 ) T)
      have hcont : ContinuousOn
          sharedTerm_b2f8ccb809
          (Icc 0 T) :=
        ((ContinuousLinearMap.apply ℝ ℝ v).continuous.comp_continuousOn
          (continuousOn_reverseTimeVStarPrimitive hΩ T g)).mul
          eta.contDiff_deriv.continuous.continuousOn
      exact hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self), (by
      simpa only [Pi.mul_def] using hqLp.integrable_mul (eta.memLp 2)), ?_⟩


  calc
    (∫ tau, reverseTimeVStarPrimitive hΩ T g tau v * eta.deriv tau
      ∂reverseTimeVolume T) =
        ∫ tau, PDE.intervalPrimitive 0 (fun s => (g s) v) tau * _root_.deriv eta tau
          ∂reverseTimeVolume T := integral_congr_ae (by
              filter_upwards [ae_restrict_mem measurableSet_Ioo] with tau ht
              rw [primitive_apply_on_Ioo hΩ T g v ht, eta.deriv_apply])
    _ = -(∫ tau, (g tau) v * eta tau ∂reverseTimeVolume T) := by
      simpa only [reverseTimeVolume, reverseTimeOpenInterval] using
        PDE.intervalPrimitive_scalar_weak_identity_Ioo (by
            change Integrable (fun tau => (g tau) v) (volume.restrict (Icc (0 ) T))
            simpa only [reverseTimeVolume, reverseTimeOpenInterval,
              restrict_Ioo_eq_restrict_Icc] using hqLp.integrable (by norm_num))
          (eta.contDiff.of_le (by simp)) eta.tsupport_subset

end HypoellipticAleksandrov.Parabolic.Dirichlet
