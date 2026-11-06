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


/-- A bounded-continuous test integral of an `IsGMCOf` limit has a raw-measurable version when its
cutoff random measures are raw-measurable. The version is the limit of measurable proxies for a
subsequence of cutoff integrals. -/
theorem equatorGFF_GMC_testIntegral_raw_measurable_version
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
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
  have regularized_testIntegral_raw_measurable_proxy (r : ℝ) (f : BoundedContinuousFunction ℂ ℝ) (hμ : Measurable[equatorGFFRawDistributionSigma X] (fun ω => regularizedGMC P Xc γ r ω)) : ∃ g : Ω → ℝ, Measurable[equatorGFFRawDistributionSigma X] g ∧ (fun ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) =ᵐ[P] g := by
    let μ : Ω → Measure ℂ := fun ω => regularizedGMC P Xc γ r ω
    exact ⟨_, (by fun_prop), (show (fun ω => ∫ x, f x ∂μ ω) =ᵐ[P] fun ω => ((fun ω => ∫⁻ x, (f.nnrealPart x : ℝ≥0∞) ∂μ ω) ω).toReal - ((fun ω => ∫⁻ x, ((-f).nnrealPart x : ℝ≥0∞) ∂μ ω) ω).toReal by filter_upwards [(regularizedGMC_finite_ae P X hX Xc hXc γ r)] with ω hω; rw [BoundedContinuousFunction.integral_eq_integral_nnrealPart_sub (μ := μ ω) f, ← BoundedContinuousFunction.toReal_lintegral_coe_eq_integral f.nnrealPart (μ ω), ← BoundedContinuousFunction.toReal_lintegral_coe_eq_integral (-f).nnrealPart (μ ω)])⟩
  obtain ⟨ns, hns, hnsAE⟩ := ((hconv f).comp tendsto_natCast_atTop_atTop).exists_seq_tendsto_ae
  choose g hgmeas hgae using (show ∀ n, ∃ g : Ω → ℝ, Measurable[equatorGFFRawDistributionSigma X] g ∧ (fun ω => ∫ x, f x ∂regularizedGMC P Xc γ (ns n : ℝ) ω) =ᵐ[P] g by intro n; exact regularized_testIntegral_raw_measurable_proxy (ns n : ℝ) f (hCut (ns n : ℝ)))
  let gLim : Ω → ℝ := fun ω => limUnder atTop (fun n => g n ω)
  have hgLim : Measurable[equatorGFFRawDistributionSigma X] gLim := by
    let : MeasurableSpace Ω := equatorGFFRawDistributionSigma X
    exact (StronglyMeasurable.limUnder (l := atTop)
      (fun n => (hgmeas n).stronglyMeasurable)).measurable
  exact ⟨gLim, hgLim, (by filter_upwards [hnsAE, (ae_all_iff.mpr hgae)] with ω hω hωeq; change (∫ x, f x ∂M ω) = limUnder atTop (fun n => g n ω); exact (hω.congr' (Filter.Eventually.of_forall hωeq)).limUnder_eq.symm)⟩

end DOZZ.Proofs
