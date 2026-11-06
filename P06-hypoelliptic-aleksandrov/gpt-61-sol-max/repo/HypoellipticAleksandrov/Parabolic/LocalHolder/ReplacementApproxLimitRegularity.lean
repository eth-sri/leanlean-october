module

public import HypoellipticAleksandrov.Parabolic.FiniteOrderSobolevC12Representative
public import HypoellipticAleksandrov.Parabolic.LocalHolder.ReplacementApproxWeakLimit
public import HypoellipticAleksandrov.KineticAleksandrov.Occupation.LocalizedKrylovRegularity

/-! # Classical regularity of a continuous higher-weak-derivative limit

The finite Sobolev representatives agree pointwise with the continuous limit on their
open collars. Scalar classical regularity then follows by locality.
-/

 public section

namespace HypoellipticAleksandrov.Parabolic.LocalHolder
open Set MeasureTheory


variable {d : ℕ} {U : HypoellipticAleksandrov.Parabolic.Region d}

/-- Scalar anisotropic classical regularity is local on its carrier. -/
theorem scalarC12On_of_locally_scalarC12On  {u : HypoellipticAleksandrov.Parabolic.ScalarField d}
    (hlocal : ∀ z ∈ U, ∃ V, IsOpen V ∧ z ∈ V ∧ IsScalarC12On u V) :
    IsScalarC12On u U := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply continuousOn_of_locally_continuousOn
    intro z hz
    obtain ⟨V, hV, hzV, huV⟩ := hlocal z hz
    exact ⟨V, hV, hzV, huV.continuousOn.mono inter_subset_right⟩
  · intro z hz
    obtain ⟨V, _, hzV, huV⟩ := hlocal z hz
    exact huV.timeSlice_differentiableAt hzV
  · intro z hz
    obtain ⟨V, _, hzV, huV⟩ := hlocal z hz
    exact huV.spatialSlice_contDiffAt hzV
  · apply continuousOn_of_locally_continuousOn
    intro z hz
    obtain ⟨V, hV, hzV, huV⟩ := hlocal z hz
    exact ⟨V, hV, hzV, huV.continuousOn_scalarTimeDerivative.mono inter_subset_right⟩
  · apply continuousOn_of_locally_continuousOn
    intro z hz
    obtain ⟨V, hV, hzV, huV⟩ := hlocal z hz
    exact ⟨V, hV, hzV, huV.continuousOn_scalarSpatialGradient.mono inter_subset_right⟩
  · apply continuousOn_of_locally_continuousOn
    intro z hz
    obtain ⟨V, hV, hzV, huV⟩ := hlocal z hz
    exact ⟨V, hV, hzV, huV.continuousOn_scalarSpatialHessian.mono inter_subset_right⟩

/-- A continuous function carrying the actual higher weak family is classical on its carrier. -/
theorem scalarC12On_of_continuousOn_higher_weak_family  (hU : IsOpen U)
    {u : HypoellipticAleksandrov.Parabolic.ScalarField d} (hu : ContinuousOn u U)
    (D : ParabolicWeakDerivativeFamily d (2 * (d + 4)) U u) :
    IsScalarC12On u U := by
  apply scalarC12On_of_locally_scalarC12On
  intro z hz
  obtain ⟨rho, hrho, v, hsub, hv, hv12, hvae, hjet⟩ :=
    exists_finiteOrderSobolevC12Representative hU (isCompact_singleton (x := z))
      (singleton_subset_iff.mpr hz) D
  let V := Metric.thickening rho ({z} )
  have hV : IsOpen V := Metric.isOpen_thickening
  have heq : EqOn v u V := Measure.eqOn_open_of_ae_eq hvae hV
    hv.continuous.continuousOn (hu.mono hsub)
  refine ⟨V, hV, ?_, ?_⟩
  · exact Metric.self_subset_thickening hrho _ (mem_singleton z)
  · exact KineticAleksandrov.Occupation.isScalarC12On_congr_open hV hv12 heq.symm

end HypoellipticAleksandrov.Parabolic.LocalHolder
