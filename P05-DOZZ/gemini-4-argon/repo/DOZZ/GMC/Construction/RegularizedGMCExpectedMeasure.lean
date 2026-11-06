/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.RegularizedGMC
public import DOZZ.Statements.GMC.GmcReferenceMeasure
import DOZZ.GMC.CircleAverageCutoffIntensity
import DOZZ.GMC.Construction.ReferenceMeasureFinite
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Prod

/-! The expected finite-cutoff circle chaos is the deterministic reference measure. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- A finite-cutoff circle GMC is a measurable random measure. -/
theorem regularizedGMC_measurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    Xc (hXc : IsCircleAverage P X Xc) γ r :
    Measurable (fun ω => regularizedGMC P Xc γ r ω) := by
  classical
  let _ := hX.1
  let V : ℂ → ℝ := fun x => ∫ ω, Xc ω x r ^ 2 ∂P
  have hVmeas : Measurable V := by
    let q : ℂ → Ω → ℝ := fun x ω => Xc ω x r ^ 2
    have hq : Measurable (Function.uncurry q) := by
      have hbase := (hXc.1 r).comp measurable_swap
      change Measurable (fun p : ℂ × Ω => Xc p.2 p.1 r ^ 2)
      rw [(show (fun p : ℂ × Ω => Xc p.2 p.1 r ^ 2) = fun p => Xc p.2 p.1 r * Xc p.2 p.1 r by funext p; ring)]
      exact hbase.mul hbase
    change Measurable (fun x => ∫ ω, q x ω ∂P)
    exact hq.stronglyMeasurable.integral_prod_right.measurable
  let density : Ω × ℂ → ℝ≥0∞ := fun p => ENNReal.ofReal
    (Real.exp (γ * Xc p.1 p.2 r - γ ^ 2 / 2 * V p.2) * normPlus p.2 ^ (-4 : ℝ))
  have hdensity : Measurable density := by
    have := hXc.1 r
    have : Measurable (fun p : Ω × ℂ => normPlus p.2) :=
      (show Measurable (fun x => normPlus x) by unfold normPlus; exact measurable_const.max measurable_norm).comp measurable_snd
    have : Measurable (fun p : Ω × ℂ => V p.2) := hVmeas.comp measurable_snd
    dsimp [density]
    fun_prop
  apply Measure.measurable_of_measurable_coe
  intro A hA
  let G : Ω × ℂ → ℝ≥0∞ := fun p => if p.2 ∈ A then density p else 0
  have hEval : (fun ω => regularizedGMC P Xc γ r ω A) =
      fun ω => ∫⁻ x, G (ω, x) ∂volume := by
    funext ω
    rw [regularizedGMC, withDensity_apply _ hA]
    change (∫⁻ x in A, density (ω, x) ∂volume) = _
    exact (fun ω => by rw [← lintegral_indicator hA]; apply lintegral_congr; intro x; by_cases hx : x ∈ A <;> simp [G, hx]) ω
  rw [hEval]
  exact (Measurable.ite (hA.preimage measurable_snd) hdensity measurable_const).lintegral_prod_right'

/-- Integrating any nonnegative measurable spatial test against the expected cutoff chaos gives
the same integral as against the GMC reference measure. -/
theorem regularizedGMC_lintegral_test_eq_reference
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    Xc (hXc : IsCircleAverage P X Xc)
    γ r (φ : ℂ → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ ω, ∫⁻ x, φ x ∂regularizedGMC P Xc γ r ω ∂P =
      ∫⁻ x, φ x ∂gmcReferenceMeasure := by
  classical
  let μ : Ω → Measure ℂ := fun ω => regularizedGMC P Xc γ r ω
  have hμ := regularizedGMC_measurable P X hX Xc hXc γ r
  have hJoin : (P.map μ).join = gmcReferenceMeasure := by
    apply Measure.ext
    intro A hA
    rw [Measure.join_apply hA, lintegral_map (Measure.measurable_coe hA) hμ]
    exact regularizedGMC_lintegral_eq_reference P X hX Xc hXc γ r A hA
  calc
    ∫⁻ ω, ∫⁻ x, φ x ∂regularizedGMC P Xc γ r ω ∂P =
        ∫⁻ m, ∫⁻ x, φ x ∂m ∂P.map μ := by
          symm
          exact lintegral_map (Measure.measurable_lintegral hφ) hμ
    _ = ∫⁻ x, φ x ∂(P.map μ).join := (Measure.lintegral_join hφ.aemeasurable).symm
    _ = ∫⁻ x, φ x ∂gmcReferenceMeasure := by rw [hJoin]

/-- The cutoff measure is finite almost surely, since its expected total mass is finite. -/
theorem regularizedGMC_finite_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) X (hX : IsEquatorGFF P X)
    Xc (hXc : IsCircleAverage P X Xc) γ r :
    ∀ᵐ ω ∂P, IsFiniteMeasure (regularizedGMC P Xc γ r ω) := by
  let μ : Ω → Measure ℂ := fun ω => regularizedGMC P Xc γ r ω
  filter_upwards [ae_lt_top ((Measure.measurable_coe MeasurableSet.univ).comp (regularizedGMC_measurable P X hX Xc hXc γ r)) (show ∫⁻ ω, μ ω Set.univ ∂P ≠ ∞ by rw [(show ∫⁻ ω, μ ω Set.univ ∂P = gmcReferenceMeasure Set.univ by simpa [μ] using regularizedGMC_lintegral_test_eq_reference P X hX Xc hXc γ r (fun _ => 1) measurable_const)]; exact gmcReferenceMeasure_univ_ne_top)] with ω hω
  exact ⟨hω⟩

end DOZZ.Proofs
