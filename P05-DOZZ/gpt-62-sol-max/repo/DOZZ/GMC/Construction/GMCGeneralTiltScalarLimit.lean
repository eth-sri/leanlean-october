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
cutoff random measures are raw-measurable. The version is the limit along an almost surely convergent
subsequence of cutoff integrals. -/
theorem equatorGFF_GMC_testIntegral_raw_measurable_version
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (γ : ℝ) (Xc : Ω → ℂ → ℝ → ℝ)
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
  have hconvNat := (hconv f).comp tendsto_natCast_atTop_atTop
  obtain ⟨ns, hns, hnsAE⟩ := hconvNat.exists_seq_tendsto_ae
  let g (n : ℕ) (ω : Ω) := ∫ x, f x ∂regularizedGMC P Xc γ (ns n : ℝ) ω
  have hgmeas (n : ℕ) : Measurable[equatorGFFRawDistributionSigma X] (g n) := by
    letI := equatorGFFRawDistributionSigma X
    exact measurable_integral_of_measurable_measure (hCut _) f.continuous.stronglyMeasurable
  let gLim  := fun ω => limUnder atTop (fun n => g n ω)
  exact ⟨gLim, (by
    let  := equatorGFFRawDistributionSigma X
    exact (StronglyMeasurable.limUnder (l := atTop)
      (fun n => (hgmeas n).stronglyMeasurable)).measurable), hnsAE.mono fun ω hω => hω.limUnder_eq.symm⟩

end DOZZ.Proofs
