/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.SoftLimitC

/-! # Measurability of the derivative masses in the measure

The Bochner integral of a strongly measurable function with values in a finite-dimensional real
space depends measurably on the measure: in coordinates it is the integral of real functions on
the measurable set of measures for which the function is integrable, and zero elsewhere. As a
consequence the softened mass and its first and second derivatives are strongly measurable
functions of a measurable random measure. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DOZZ.Proofs

attribute [local instance low] bpzNormedAddCommGroupBilin bpzNormedSpaceBilin

/-- Integrals of a strongly measurable function with values in a finite-dimensional space depend
measurably on the measure. -/
theorem bpz_stronglyMeasurable_integral_measure {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {f : ℂ → E} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun m : Measure ℂ => ∫ x, f x ∂m) := by
  set A := {m | ∫⁻ x, ‖f x‖ₑ ∂m < ⊤} with hA
  have hAm : MeasurableSet A :=
    by measurability
  let b := Module.finBasis ℝ E
  have key : (fun m => ∫ x, f x ∂m) = fun m =>
      ∑ i, A.indicator (fun m => ∫ x, b.coord i (f x) ∂m) m • b i := by
    funext m
    by_cases hm : m ∈ A
    · have hint : Integrable f m := ⟨hf.aestronglyMeasurable, hm⟩
      conv_lhs => rw [← b.sum_repr (∫ x, f x ∂m)]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      have h := ContinuousLinearMap.integral_comp_comm
        (LinearMap.toContinuousLinearMap (b.coord i)) hint
      simp_all
    · have hint : ¬ Integrable f m := fun h => hm h.2
      rw [integral_undef hint]
      simp_all
  rw [key]
  refine Finset.stronglyMeasurable_fun_sum _ fun i _ => ?_
  have hc :=
    ((LinearMap.continuous_of_finiteDimensional (b.coord i)).comp_stronglyMeasurable hf).measurable
  exact (((measurable_integral_measure hc).indicator hAm).stronglyMeasurable).smul_const _
section
variable (a ε : ℝ)
section
variable (z : ℂ) {w : ℂ → ℝ}
section
variable (hw : Measurable w)
include hw

/-- The first derivative factor is strongly measurable in the integration variable. -/
theorem bpz_stronglyMeasurable_softDeriv :
    StronglyMeasurable (fun x : ℂ => w x • bpzSoftDeriv a ε x z) := by
  have hbase : Measurable (fun x => Complex.normSq (x - z) + ε ^ 2) := by fun_prop
  have hc : Measurable
      (fun x => -2 * a * (Complex.normSq _ + ε ^ 2) ^ (a - 1)) :=
    (hbase.pow_const _).const_mul _
  have hL : Continuous (fun x => innerSL ℝ (x - z)) :=
    (innerSL ℝ).continuous.comp (continuous_id.sub continuous_const)
  exact hw.stronglyMeasurable.smul (hc.stronglyMeasurable.smul hL.stronglyMeasurable)

/-- The second derivative factor is strongly measurable in the integration variable. -/
theorem bpz_stronglyMeasurable_softDeriv2 :
    StronglyMeasurable (fun x : ℂ => w x • bpzSoftDeriv2 a ε x z) := by
  have hbase : Measurable (fun x => Complex.normSq (x - z) + ε ^ 2) := by fun_prop
  have hc2 : Measurable
      (fun x => 4 * a * (a - 1) * (Complex.normSq _ + ε ^ 2) ^ (a - 2)) :=
    (hbase.pow_const _).const_mul _
  have hc1 : Measurable
      (fun x => 2 * a * (Complex.normSq _ + ε ^ 2) ^ (a - 1)) :=
    (hbase.pow_const _).const_mul _
  have hL : Continuous (fun x => innerSL ℝ (x - z)) :=
    (innerSL ℝ).continuous.comp (continuous_id.sub continuous_const)
  have hS :=
    (ContinuousLinearMap.smulRightL ℝ ℂ _).continuous₂.comp₂ hL hL
  exact hw.stronglyMeasurable.smul ((hc2.stronglyMeasurable.smul hS.stronglyMeasurable).add
    (hc1.stronglyMeasurable.smul stronglyMeasurable_const))

end

end
section
variable {w : ℂ → ℝ}
section
variable (hw : Measurable w) (z : ℂ)
include hw

/-- The softened mass is a measurable function of the measure. -/
theorem bpz_measurable_softMassReal :
    Measurable (fun m : Measure ℂ => bpzSoftMassReal a ε w m z) :=
  measurable_integral_measure ((bpzSoft_measurable_rpow a ε z).mul hw)

/-- The first derivative mass is a strongly measurable function of the measure. -/
theorem bpz_stronglyMeasurable_softMassDeriv : StronglyMeasurable (fun m : Measure ℂ => bpzSoftMassDeriv a ε w m z) :=
  bpz_stronglyMeasurable_integral_measure (bpz_stronglyMeasurable_softDeriv a ε z hw)

/-- The second derivative mass is a strongly measurable function of the measure. -/
theorem bpz_stronglyMeasurable_softMassDeriv2 : StronglyMeasurable (fun m : Measure ℂ => bpzSoftMassDeriv2 a ε w m z) :=
  bpz_stronglyMeasurable_integral_measure (bpz_stronglyMeasurable_softDeriv2 a ε z hw)

end

end

end

end DOZZ.Proofs
