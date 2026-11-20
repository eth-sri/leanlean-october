/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module
public import DOZZ.MeasureTheory.CylinderLaws

public import DOZZ.GMC.Construction.RootedFiniteCoordinateIdentity
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! Rooted laws of the determining field and measure coordinates. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

/-- The point-rooted field and chaos coordinate path is jointly measurable. -/
theorem measurable_pointRootedCoordinatePath
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (M : Ω → Measure ℂ)
    (hMmeas : Measurable M) (hfinite : ∀ ω, IsFiniteMeasure (M ω)) :
    Measurable (fun q : ℂ × Ω => gmcTiltCoordinatePath
      (fun f => X q.2 f + γ * gffRootCovariance q.1 f)
      (gmcRootedMeasure γ q.1 (M q.2))) := by
  have hfield : Measurable (fun q : ℂ × Ω =>
      fun f => X q.2 f + γ * gffRootCovariance q.1 f) := by
    rw [measurable_pi_iff]
    intro f
    exact ((hX.2 f).1.comp measurable_snd).add
      (measurable_const.mul ((gffRootCovariance_continuous f).measurable.comp measurable_fst))
  exact measurable_gmcTiltCoordinatePath.comp
    (hfield.prodMk (measurable_gmcRootedMeasure_family M hMmeas hfinite γ))

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (hMmeas : Measurable M)
  (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (A : Set ℂ) (hA : MeasurableSet A) (R : ℝ)
  (hAR : A ⊆ Metric.closedBall (0 : ℂ) R)
  (hRoot : ∀ᵐ u ∂gmcReferenceMeasure.restrict A,
      ∀ᵐ ω ∂P, IsFiniteMeasure (gmcRootedMeasure γ u (M ω)))
include hX hγ hγ2 hM hMmeas Xc hXc hA R hAR hRoot

/-- The finite-dimensional rooted marked law on a bounded root set. -/
theorem rooted_finite_coordinate_law
    (s : Finset gmcTiltCoordinateIndex) :
    Measure.map (fun ω => gmcTiltFiniteCoordinatePath s (fun f => X ω f) (M ω))
      (P.withDensity (fun ω => M ω A)) =
    Measure.map (fun q : ℂ × Ω => gmcTiltFiniteCoordinatePath s
      (fun f => X q.2 f + γ * gffRootCovariance q.1 f)
      (gmcRootedMeasure γ q.1 (M q.2))) ((gmcReferenceMeasure.restrict A).prod P) := by
  let _ := hX.1
  let _ : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
  have hmass : Measurable (fun ω => M ω A) := (Measure.measurable_coe hA).comp hMmeas
  have hmean : (∫⁻ ω, M ω A ∂P) ≠ ⊤ := by
    rw [equatorGFF_GMC_intensity P X hX γ hγ hγ2 M hM A hA]
    exact measure_ne_top _ _
  let _ := isFiniteMeasure_withDensity hmean
  have hl : Measurable (fun ω => gmcTiltFiniteCoordinatePath s (fun f => X ω f) (M ω)) :=
    (measurable_gmcTiltFiniteCoordinatePath s).comp
      ((measurable_pi_iff.mpr fun f => (hX.2 f).1).prodMk hMmeas)
  have hr : Measurable (fun q : ℂ × Ω => gmcTiltFiniteCoordinatePath s
      (fun f => X q.2 f + γ * gffRootCovariance q.1 f)
      (gmcRootedMeasure γ q.1 (M q.2))) := by
    rw [measurable_pi_iff]
    exact fun i => (measurable_pi_apply i.1).comp
      (measurable_pointRootedCoordinatePath P X hX γ M hMmeas hM.1)
  apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
  intro φ
  rw [lintegral_map (by fun_prop) hl, lintegral_map (by fun_prop) hr, lintegral_withDensity_eq_lintegral_mul _ hmass (by fun_prop)]
  have hj : AEMeasurable (fun q : ℂ × Ω => (φ (gmcTiltFiniteCoordinatePath s
      (fun f => X q.2 f + γ * gffRootCovariance q.1 f)
      (gmcRootedMeasure γ q.1 (M q.2))) : ℝ≥0∞))
      ((gmcReferenceMeasure.restrict A).prod P) := by
    exact (measurable_coe_nnreal_ennreal.comp (φ.continuous.measurable.comp hr)).aemeasurable
  rw [lintegral_prod _ hj]
  let ψ := φ.comp ((↑) : ℝ≥0 → ℝ) NNReal.isometry_coe.lipschitzWith
  have heq := rooted_finite_coordinate_identity P X hX γ hγ hγ2 M hM hMmeas
    Xc hXc A hA R hAR hRoot s ψ (fun q => (φ q).coe_nonneg)
  simpa only [ψ, BoundedContinuousFunction.comp_apply, ENNReal.ofReal_coe_nnreal,
    Pi.mul_apply, mul_comm] using heq

/-- The complete determining-coordinate law on a bounded root set, without restricting the
observable to finitely many coordinates. -/
theorem rooted_full_coordinate_law :
    Measure.map (fun ω => gmcTiltCoordinatePath (fun f => X ω f) (M ω))
      (P.withDensity (fun ω => M ω A)) =
    Measure.map (fun q : ℂ × Ω => gmcTiltCoordinatePath
      (fun f => X q.2 f + γ * gffRootCovariance q.1 f)
      (gmcRootedMeasure γ q.1 (M q.2))) ((gmcReferenceMeasure.restrict A).prod P) := by
  let _ : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
  have hmean : (∫⁻ ω, M ω A ∂P) ≠ ⊤ := by
    rw [equatorGFF_GMC_intensity P X hX γ hγ hγ2 M hM A hA]
    exact measure_ne_top _ _
  let _ := isFiniteMeasure_withDensity hmean
  have hl : Measurable (fun ω => gmcTiltCoordinatePath (fun f => X ω f) (M ω)) :=
    measurable_gmcTiltCoordinatePath.comp
      ((measurable_pi_iff.mpr fun f => (hX.2 f).1).prodMk hMmeas)
  have hr := measurable_pointRootedCoordinatePath P X hX γ M hMmeas hM.1
  apply measure_eq_of_finite_coordinate_map_eq
  intro s
  have hm : Measurable (s.restrict : (gmcTiltCoordinateIndex → ℝ) → s → ℝ) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply i.1
  rw [Measure.map_map hm hl, Measure.map_map hm hr]
  exact rooted_finite_coordinate_law P X hX γ hγ hγ2 M hM hMmeas
    Xc hXc A hA R hAR hRoot s

end

end DOZZ.Proofs
