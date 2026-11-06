/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.GMCGeneralTilt
import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Measure.GiryMonad

/-! Measurable factorization inputs for the general GMC Cameron--Martin identity. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs
section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
section
variable (hX : IsEquatorGFF P X)
include hX

private theorem regularized_testIntegral_raw_measurable_proxy
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ)
    (f : BoundedContinuousFunction ℂ ℝ)
    (hμ : Measurable[equatorGFFRawDistributionSigma X]
      (fun ω => regularizedGMC P Xc γ r ω)) :
    ∃ g : Ω → ℝ,
      Measurable[equatorGFFRawDistributionSigma X] g ∧
      (fun ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) =ᵐ[P] g := by
  let μ : Ω → Measure ℂ := fun ω => regularizedGMC P Xc γ r ω
  let pos : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ x, (f.nnrealPart x) ∂μ ω
  let neg : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ x, ((-f).nnrealPart x) ∂μ ω
  have hpos : Measurable[equatorGFFRawDistributionSigma X] pos := by
    fun_prop
  have hneg : Measurable[equatorGFFRawDistributionSigma X] neg := by
    fun_prop
  have hproxy : Measurable[equatorGFFRawDistributionSigma X]
      (fun ω => (pos ω).toReal - (neg ω).toReal) := by
    fun_prop
  have heq :
      (fun ω => ∫ x, f x ∂μ ω) =ᵐ[P]
        fun ω => (pos ω).toReal - (neg ω).toReal := by
    filter_upwards [(regularizedGMC_finite_ae P X hX Xc hXc γ r)] with ω hω
    rw [BoundedContinuousFunction.integral_eq_integral_nnrealPart_sub (μ := μ ω) f, ← BoundedContinuousFunction.toReal_lintegral_coe_eq_integral f.nnrealPart (μ ω), ← BoundedContinuousFunction.toReal_lintegral_coe_eq_integral (-f).nnrealPart (μ ω)]
  tauto

/-- A bounded-continuous test integral of an `IsGMCOf` limit has a raw-measurable version when its
cutoff random measures are raw-measurable. The version is the limit of measurable proxies for a
subsequence of cutoff integrals. -/
theorem equatorGFF_GMC_testIntegral_raw_measurable_version
    (γ : ℝ) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (M : Ω → Measure ℂ)
    (hconv : ∀ f : BoundedContinuousFunction ℂ ℝ,
      TendstoInMeasure P
        (fun r ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) atTop
        (fun ω => ∫ x, f x ∂M ω))
    (hCut : ∀ r,
      Measurable[equatorGFFRawDistributionSigma X]
        (fun ω => regularizedGMC P Xc γ r ω))
    (f : BoundedContinuousFunction ℂ ℝ) :
    ∃ g : Ω → ℝ,
      Measurable[equatorGFFRawDistributionSigma X] g ∧
      (fun ω => ∫ x, f x ∂M ω) =ᵐ[P] g := by
  have hconvNat :=
    (hconv f).comp tendsto_natCast_atTop_atTop
  obtain ⟨ns, hns, hnsAE⟩ := hconvNat.exists_seq_tendsto_ae
  have hseq : ∀ n, ∃ g : Ω → ℝ,
      Measurable[equatorGFFRawDistributionSigma X] g ∧
      (fun ω => ∫ x, f x ∂regularizedGMC P Xc γ (ns n) ω) =ᵐ[P] g := by
    intro n
    exact regularized_testIntegral_raw_measurable_proxy P X hX Xc hXc γ (ns n) f
      (hCut (ns n))
  choose g hgmeas hgae using hseq
  let gLim : Ω → ℝ := fun ω => limUnder atTop (fun n => g n ω)
  have hgLim : Measurable[equatorGFFRawDistributionSigma X] gLim := by
    let : MeasurableSpace Ω := equatorGFFRawDistributionSigma X
    exact (StronglyMeasurable.limUnder
      (fun n => (hgmeas n).stronglyMeasurable)).measurable
  have hAEproxy :=
    ae_all_iff.mpr hgae
  have hEq : (fun ω => ∫ x, f x ∂M ω) =ᵐ[P] gLim := by
    filter_upwards [hnsAE, hAEproxy] with ω hω hωeq
    have hT :=
      (hω.congr' (Filter.Eventually.of_forall hωeq))
    exact hT.limUnder_eq.symm
  tauto

end

end

end DOZZ.Proofs
