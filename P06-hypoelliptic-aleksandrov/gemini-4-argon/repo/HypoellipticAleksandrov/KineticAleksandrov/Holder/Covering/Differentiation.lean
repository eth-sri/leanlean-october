module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.DifferentiationRegular
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.DifferentiationDefect
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.Maximal
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.DifferentiationGeometry
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.Inflation
import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.InflationVolume
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Topology.MetricSpace.ProperSpace

/-! # Density differentiation of indicators on centered kinetic cylinders

Outer approximation and the proved weak maximal estimate give density-one at almost
every point. Ordinary metric balls are used only to prove topological shrinking of the
basis, never to compare its eccentric volumes.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory
open scoped Topology

/- Points of E with arbitrarily small failures of a fixed near-full density threshold. -/
def densityFailure {d : ℕ} (E : Set (KineticPoint d)) (eta : ℝ) : Set (KineticPoint d) :=
  {P | P ∈ E ∧ ∀ r0 : ℝ, 0 < r0 → ∃ r : ℝ, 0 < r ∧ r < r0 ∧
    (volume (E ∩ centeredCylinder P r)).toReal <
      (1-eta)*(volume (centeredCylinder P r)).toReal}

/- A failed density point lies in the maximal set of the error of any open approximation. -/
theorem densityFailure_subset_error_maximal {d : ℕ} {E U : Set (KineticPoint d)}
    (hE : NullMeasurableSet E volume) (hU : IsOpen U) (hEU : E ⊆ U)
    {eta : ℝ} (heta : 0 < eta) :
    densityFailure E eta ⊆ maximalCylinderUnion (U \ E) (ENNReal.ofReal eta) := by
  intro P hP
  obtain ⟨r0, hr0, hsmall⟩ : ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r < r0 → centeredCylinder P r ⊆ U := by
    have hP := (hEU hP.1)
    obtain ⟨eps, heps, hball⟩ := Metric.isOpen_iff.mp hU P hP
    obtain ⟨r0, hr0, hsmall⟩ := centeredCylinder_subset_ball P heps
    exact ⟨r0, hr0, fun r hr hrr => (hsmall r hr hrr).trans hball⟩
  obtain ⟨r, hr, hrr, hdef⟩ := hP.2 (min r0 1) (lt_min hr0 zero_lt_one)
  have hsub := hsmall r hr (hrr.trans_le (min_le_left _ _))
  have heq : (U \ E) ∩ centeredCylinder P r = centeredCylinder P r \ E := by
    ext X
    constructor
    · exact fun h => ⟨h.2, h.1.2⟩
    · exact fun h => ⟨⟨hsub h.1, h.2⟩, h.1⟩
  have hcharge := measure_density_defect hE
    (volume_cylinder_pos_ne_top (centeredTop P r) hr).2 heta.le hdef.le
  change ENNReal.ofReal eta * volume (centeredCylinder P r) ≤
    volume (centeredCylinder P r \ E) at hcharge
  rw [← heq] at hcharge
  exact mem_iUnion₂.mpr ⟨(centeredTop P r, r),
    ⟨hr, (hrr.trans_le (min_le_right _ _)).le, hcharge⟩,
    self_mem_centeredCylinder P hr⟩

/- A measurable finite-volume set has no positive-measure density failures. -/
theorem volume_densityFailure_eq_zero_of_measurable {d : ℕ} {E : Set (KineticPoint d)}
    (hE : MeasurableSet E) (hfinite : volume E ≠ ⊤) {eta : ℝ} (heta : 0 < eta) :
    volume (densityFailure E eta) = 0 := by
  let : Measure.OuterRegular (volume : Measure (KineticPoint d)) := by
      change Measure.OuterRegular
        (Measure.map (KineticPoint.homeomorphProd d).symm
          (volume : Measure (ℝ × (PDE.Vec d × PDE.Vec d))))
      let : Measure.Regular (volume : Measure (ℝ × (PDE.Vec d × PDE.Vec d))) :=
        Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure volume
      exact Measure.OuterRegular.map (KineticPoint.homeomorphProd d).symm volume

    /- Every bounded kinetic set has finite volume. -/
  let C := ENNReal.ofReal ((8 : ℝ) ^ (4*d+2))
  have hC0 : C ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hCtop : C ≠ ⊤ := ENNReal.ofReal_ne_top
  have hzero : ENNReal.ofReal eta * volume (densityFailure E eta) = 0 := by
    apply le_antisymm ?_ bot_le
    apply le_of_forall_gt
    intro eps heps
    have hdiv : eps/C ≠ 0 := (ENNReal.div_pos_iff.mpr ⟨heps.ne', hCtop⟩).ne'
    obtain ⟨U, hEU, hU, _, herror⟩ := hE.exists_isOpen_sdiff_lt hfinite hdiv
    have hbound := (mul_le_mul_right (measure_mono
      (densityFailure_subset_error_maximal hE.nullMeasurableSet hU hEU heta))
      (ENNReal.ofReal eta)).trans
      (maximalCylinderUnion_weak_type (U \ E) (ENNReal.ofReal eta))
    have herr : C * volume (U \ E) < eps := by
      have h := ENNReal.mul_lt_mul_left hC0 hCtop herror
      rwa [mul_comm (volume (U \ E)) C, mul_comm (eps/C) C,
        ENNReal.mul_div_cancel hC0 hCtop] at h
    exact hbound.trans_lt herr
  exact (mul_eq_zero.mp hzero).resolve_left (ENNReal.ofReal_pos.mpr heta).ne'

/- Null-measurable finite-volume sets satisfy the same density theorem. -/
theorem ae_centeredCylinder_density {d } {E : Set (KineticPoint d)}
    (hE : NullMeasurableSet E volume) (hbounded : Bornology.IsBounded E)
    {eta } (heta : 0 < eta) :
    ∀ᵐ P ∂(volume.restrict E), ∃ r0 : ℝ, 0 < r0 ∧
      ∀ r : ℝ, 0 < r → r < r0 →
        (1-eta)*(volume (centeredCylinder P r)).toReal ≤
          (volume (E ∩ centeredCylinder P r)).toReal := by
  have hzero : volume (densityFailure E eta) = 0 := by
    have hfinite := (volume_bounded_ne_top hbounded)
    obtain ⟨M, hEM, hM, hME⟩ := hE.exists_measurable_superset_ae_eq
    have hMf : volume M ≠ ⊤ := by rwa [measure_congr hME]
    have hsub : densityFailure E eta ⊆ densityFailure M eta := by
      intro P hP
      refine ⟨hEM hP.1, ?_⟩
      intro r0 hr0
      obtain ⟨r, hr, hrr, hbad⟩ := hP.2 r0 hr0
      refine ⟨r, hr, hrr, ?_⟩
      rw [measure_congr (hME.inter Filter.EventuallyEq.rfl)]
      exact hbad
    exact measure_mono_null hsub (volume_densityFailure_eq_zero_of_measurable hM hMf heta)
  have hae : ∀ᵐ P ∂volume, P ∉ densityFailure E eta := by
    apply ae_iff.mpr
    have heq : {P : KineticPoint d | ¬P ∉ densityFailure E eta} = densityFailure E eta := by
      ext P
      exact not_not
    rw [heq]
    exact hzero
  rw [ae_restrict_iff'₀ hE]
  filter_upwards [hae] with P hP hPE
  by_contra hnot
  apply hP
  refine ⟨hPE, ?_⟩
  intro r0 hr0
  by_contra hnone
  apply hnot
  refine ⟨r0, hr0, ?_⟩
  intro r hr hrr
  by_contra hbad
  exact hnone ⟨r, hr, hrr, lt_of_not_ge hbad⟩

/- A single full-measure subset has near-full density at every positive threshold. -/
end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
