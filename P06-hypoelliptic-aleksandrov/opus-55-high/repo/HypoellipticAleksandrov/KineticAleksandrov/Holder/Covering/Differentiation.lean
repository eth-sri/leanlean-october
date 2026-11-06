module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.DifferentiationRegular
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.DifferentiationDefect
public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.Maximal
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Tactic

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

/-- Points of E with arbitrarily small failures of a fixed near-full density threshold. -/
def densityFailure {d : ℕ} (E : Set (KineticPoint d)) (eta : ℝ) : Set (KineticPoint d) :=
  {P | P ∈ E ∧ ∀ r0 : ℝ, 0 < r0 → ∃ r : ℝ, 0 < r ∧ r < r0 ∧
    (volume (E ∩ centeredCylinder P r)).toReal <
      (1-eta)*(volume (centeredCylinder P r)).toReal}

variable {d : ℕ} {E : Set (KineticPoint d)}

/-- A failed density point lies in the maximal set of the error of any open approximation. -/
theorem densityFailure_subset_error_maximal  {E U : Set (KineticPoint d)}
    (hE : NullMeasurableSet E volume) (hU : IsOpen U) (hEU : E ⊆ U)
    {eta : ℝ} (heta : 0 < eta) :
    densityFailure E eta ⊆ maximalCylinderUnion (U \ E) (ENNReal.ofReal eta) := by
  intro P hP
  obtain ⟨r0, hr0, hsmall⟩ := centeredCylinder_eventually_subset_open hU (hEU hP.1)
  obtain ⟨r, hr, hrr, hdef⟩ := hP.2 (min r0 1) (lt_min hr0 zero_lt_one)
  have hsub := hsmall r hr (hrr.trans_le (min_le_left _ _))
  have heq : (U \ E) ∩ centeredCylinder P r = centeredCylinder P r \ E := by
    grind
  have hcharge := measure_density_defect hE
    (volume_cylinder_pos_ne_top _ hr).2 heta.le hdef.le
  change ENNReal.ofReal eta * volume (centeredCylinder P r) ≤
    volume (centeredCylinder P r \ E) at hcharge
  rw [← heq] at hcharge
  exact mem_iUnion₂.mpr ⟨(centeredTop P r, r),
    ⟨hr, (hrr.trans_le (min_le_right _ _)).le, hcharge⟩,
    self_mem_centeredCylinder P hr⟩

/-- A measurable finite-volume set has no positive-measure density failures. -/
theorem volume_densityFailure_eq_zero_of_measurable 
    (hE : MeasurableSet E) (hfinite : volume E ≠ ⊤) {eta : ℝ} (heta : 0 < eta) :
    volume (densityFailure E eta) = 0 := by
  let  :=
    outerRegular_kinetic_volume d
  let C := ENNReal.ofReal ((8) ^ (4*d+2))
  have hC0 : C ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hCtop : C ≠ ⊤ := ENNReal.ofReal_ne_top
  have hzero : ENNReal.ofReal eta * volume (densityFailure E eta) = 0 := by
    apply le_antisymm ?_ bot_le
    apply le_of_forall_gt
    intro eps heps
    have hdiv  := (ENNReal.div_pos_iff.mpr ⟨heps.ne', hCtop⟩).ne'
    obtain ⟨U, hEU, hU, _, herror⟩ := hE.exists_isOpen_sdiff_lt hfinite hdiv
    have hbound := (mul_le_mul_right (measure_mono
      (densityFailure_subset_error_maximal hE.nullMeasurableSet hU hEU heta))
      _).trans
      (maximalCylinderUnion_weak_type _ _)
    have herr : C * volume (U \ E) < eps := by
      have h := ENNReal.mul_lt_mul_left hC0 hCtop herror
      rwa [mul_comm, mul_comm (eps/C),
        ENNReal.mul_div_cancel] at h
    grind
  exact (mul_eq_zero.mp hzero).resolve_left (ENNReal.ofReal_pos.mpr heta).ne'

/-- Null-measurable finite-volume sets satisfy the same density theorem. -/
theorem volume_densityFailure_eq_zero 
    (hE : NullMeasurableSet E volume) (hfinite : volume E ≠ ⊤)
    {eta : ℝ} (heta : 0 < eta) : volume (densityFailure E eta) = 0 := by
  obtain ⟨M, hEM, hM, hME⟩ := hE.exists_measurable_superset_ae_eq
  have hMf : volume M ≠ ⊤ := by rwa [measure_congr]
  have hsub : densityFailure E eta ⊆ densityFailure M eta := by
    intro P hP
    refine ⟨hEM hP.1, ?_⟩
    intro r0 hr0
    obtain ⟨r, hr, hrr, hbad⟩ := hP.2 r0 hr0
    refine ⟨r, hr, hrr, ?_⟩
    rw [measure_congr (hME.inter Filter.EventuallyEq.rfl)]
    omega
  exact measure_mono_null hsub (volume_densityFailure_eq_zero_of_measurable hM hMf heta)

/-- At almost every point of a bounded null-measurable set, all sufficiently small centered
kinetic cylinders meet any fixed near-full density threshold. -/
theorem ae_centeredCylinder_density 
    (hE : NullMeasurableSet E volume) (hbounded : Bornology.IsBounded E)
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᵐ P ∂(volume.restrict E), ∃ r0 : ℝ, 0 < r0 ∧
      ∀ r : ℝ, 0 < r → r < r0 →
        (1-eta)*(volume (centeredCylinder P r)).toReal ≤
          (volume (E ∩ centeredCylinder P r)).toReal := by
  have hzero := volume_densityFailure_eq_zero hE (volume_bounded_ne_top hbounded) heta
  have hae : ∀ᵐ P ∂volume, P ∉ densityFailure E eta := by
    apply ae_iff.mpr
    simp_all
  rw [ae_restrict_iff'₀ hE]
  filter_upwards [hae] with P hP hPE
  by_contra hnot
  apply hP
  refine ⟨hPE, ?_⟩
  simp_all

/-- A single full-measure subset has near-full density at every positive threshold. -/
theorem ae_centeredCylinder_density_all 
    (hE : NullMeasurableSet E volume) (hbounded : Bornology.IsBounded E) :
    ∀ᵐ P ∂(volume.restrict E), ∀ eta : ℝ, 0 < eta →
      ∃ r0 : ℝ, 0 < r0 ∧ ∀ r : ℝ, 0 < r → r < r0 →
        (1-eta)*(volume (centeredCylinder P r)).toReal ≤
          (volume (E ∩ centeredCylinder P r)).toReal := by
  have hnat : ∀ n : ℕ, ∀ᵐ P ∂(volume.restrict E), ∃ r0 : ℝ, 0 < r0 ∧
      ∀ r : ℝ, 0 < r → r < r0 →
        (1-1/(n+1))*(volume (centeredCylinder P r)).toReal ≤
          (volume (E ∩ centeredCylinder P r)).toReal := by
    intro n
    exact ae_centeredCylinder_density hE hbounded (by positivity)
  filter_upwards [ae_all_iff.mpr hnat] with P hP
  intro eta heta
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt heta
  obtain ⟨r0, hr0, hsmall⟩ := hP n
  refine ⟨r0, hr0, ?_⟩
  intro r hr hrr
  have h := hsmall r hr hrr
  have hvol := ENNReal.toReal_nonneg (a := volume (centeredCylinder P r))
  have hdiff : 1-eta ≤ 1-1/(n+1) := by linarith
  exact (mul_le_mul_of_nonneg_right hdiff hvol).trans h

end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
