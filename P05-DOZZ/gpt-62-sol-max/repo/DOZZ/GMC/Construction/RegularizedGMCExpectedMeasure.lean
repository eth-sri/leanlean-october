/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.RegularizedGMC
public import DOZZ.Statements.GMC.GmcReferenceMeasure
public import DOZZ.GMC.MeasurableIntegrals
import DOZZ.GMC.CircleAverageCutoffIntensity
import Mathlib.Probability.Kernel.WithDensity
import DOZZ.GMC.Construction.ReferenceMeasureFinite
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Prod

/-! The expected finite-cutoff circle chaos is the deterministic reference measure. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- A cutoff measure is measurable even for a coarser σ-algebra on which the field
is jointly measurable: computing the variance still uses the original ambient measure. -/
theorem regularizedGMC_measurable_of_joint
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (m : MeasurableSpace Ω) (P : @Measure Ω mΩ)
    [@IsProbabilityMeasure Ω mΩ P] (Xc : Ω → ℂ → ℝ → ℝ) (γ r : ℝ)
    (hfield : Measurable[mΩ.prod (borel ℂ)] (fun p : Ω × ℂ => Xc p.1 p.2 r))
    (hm : Measurable[m.prod (borel ℂ)] (fun p : Ω × ℂ => Xc p.1 p.2 r)) :
    Measurable[m] (fun ω => @regularizedGMC Ω mΩ P Xc γ r ω) := by
  letI : MeasurableSpace Ω := mΩ
  let V : ℂ → ℝ := fun x => ∫ ω, Xc ω x r ^ 2 ∂P
  have hV : Measurable V :=
    ((hfield.comp measurable_swap).pow_const 2).stronglyMeasurable.integral_prod_right.measurable
  have hn : Measurable (normPlus : ℂ → ℝ) := measurable_const.max measurable_norm
  let d : Ω → ℂ → ℝ≥0∞ := fun ω x => ENNReal.ofReal
    (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * V x) * normPlus x ^ (-4 : ℝ))
  letI : MeasurableSpace Ω := m
  have hd : Measurable (Function.uncurry d) :=
    ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp
      ((hm.const_mul γ).sub ((hV.comp measurable_snd).const_mul _))).mul
      ((hn.comp measurable_snd).pow_const _))
  let κ := (Kernel.const Ω (volume : Measure ℂ)).withDensity d
  have heq : ⇑κ = (fun ω => @regularizedGMC Ω mΩ P Xc γ r ω) :=
    funext fun ω => Kernel.withDensity_apply (Kernel.const Ω (volume : Measure ℂ)) hd ω
  exact heq ▸ κ.measurable

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ)
include Ω X hX hXc

/-- A finite-cutoff circle GMC is a measurable random measure. -/
theorem regularizedGMC_measurable :
    Measurable (fun ω => regularizedGMC P Xc γ r ω) := by
  letI := hX.1
  exact regularizedGMC_measurable_of_joint _ P Xc γ r (hXc.1 r) (hXc.1 r)

/-- Integrating any nonnegative measurable spatial test against the expected cutoff chaos gives
the same integral as against the GMC reference measure. -/
theorem regularizedGMC_lintegral_test_eq_reference (φ : ℂ → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ ω, ∫⁻ x, φ x ∂regularizedGMC P Xc γ r ω ∂P =
      ∫⁻ x, φ x ∂gmcReferenceMeasure := by
  let μ := fun ω => regularizedGMC P Xc γ r ω
  have hm : AEMeasurable μ P := (regularizedGMC_measurable P X hX Xc hXc γ r).aemeasurable
  have h : P.bind μ = gmcReferenceMeasure := by
    ext s hs
    rw [Measure.bind_apply hs hm]
    exact regularizedGMC_lintegral_eq_reference P X hX Xc hXc γ r s hs
  change (∫⁻ ω, ∫⁻ x, φ x ∂μ ω ∂P) = _
  rw [← Measure.lintegral_bind hm hφ.aemeasurable, h]

/-- The cutoff measure is finite almost surely, since its expected total mass is finite. -/
theorem regularizedGMC_finite_ae :
    ∀ᵐ ω ∂P, IsFiniteMeasure (regularizedGMC P Xc γ r ω) := by
  have h := regularizedGMC_lintegral_eq_reference P X hX Xc hXc γ r Set.univ MeasurableSet.univ
  exact (ae_lt_top ((Measure.measurable_coe MeasurableSet.univ).comp
    (regularizedGMC_measurable P X hX Xc hXc γ r))
    (h.trans_ne gmcReferenceMeasure_univ_ne_top)).mono fun _ hω => ⟨hω⟩

end

end DOZZ.Proofs
