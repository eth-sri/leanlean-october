/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Lateral.AnnularComparison
public import DOZZ.Brownian.ReflectionMassMeasurability

/-!
# Initial-block inverse estimates for the two-sided reflection mass

For arbitrary continuous radial paths and an independent given lateral chaos, the initial
positive-time block gives an inverse-moment estimate. It uses one lateral measure throughout;
no independence between its two half-lines is required. The radial exponential-supremum
estimate and the lateral inverse-moment estimate remain explicit analytic inputs.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- Nonpositive powers reverse mass inequalities, including at zero and infinity. -/
theorem ennreal_rpow_antitone_nonpos (x y : ℝ≥0∞) (q : ℝ)
    (hxy : x ≤ y) (hq : q ≤ 0) : y ^ q ≤ x ^ q := by
  simpa only [← ENNReal.rpow_neg, neg_neg] using (ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hxy (neg_nonneg.mpr hq)))
section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

/-- Local finiteness makes the actual full reflection mass AE measurable for any AE measurable
path pair; a conditioned law is not needed for this carrier fact. -/
theorem twoSidedReflectionMass_aemeasurable_of_lateral
    (γ : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : IsLateralGMCOf P γ Z) :
    AEMeasurable (fun ω => twoSidedReflectionMass γ B Z ω) P := by
  have hp := hB.prodMk hZ.2.2.2.1
  have hl : ∀ᵐ ω ∂P, LocallyFiniteOnTranslationWindows (Z ω) := by
    filter_upwards [hZ.2.2.2.2.1] with ω hω
    tauto
  have hm := aemeasurable_reflectionMassInput_map_of_locallyFinite P γ
    (fun ω => (B ω, Z ω)) hp hl
  exact hm.comp_aemeasurable hp
section
variable (γ q : ℝ) (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
section
variable (hB : AEMeasurable B P) (hZ : IsLateralGMCOf P γ Z)
include hB hZ

/-- Every real moment integrand of the actual reflection mass is AE measurable. -/
theorem twoSidedReflectionMass_rpow_aemeasurable_of_lateral
    :
    AEMeasurable (fun ω => (twoSidedReflectionMass γ B Z ω) ^ q) P := ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
    (twoSidedReflectionMass_aemeasurable_of_lateral P γ B Z hB hZ)

/-- A finite strictly negative moment implies almost sure positive reflection mass. -/
theorem twoSidedReflectionMass_pos_ae_of_negative_moment
    (hq : q < 0)
    (hm : (∫⁻ ω, (twoSidedReflectionMass γ B Z ω) ^ q ∂P) < ⊤) :
    ∀ᵐ ω ∂P, 0 < twoSidedReflectionMass γ B Z ω := by
  have hf := ae_lt_top' (twoSidedReflectionMass_rpow_aemeasurable_of_lateral
    P γ q B Z hB hZ) hm.ne
  filter_upwards [hf] with ω hω
  apply pos_iff_ne_zero.mpr
  aesop

/-- A finite strictly positive moment implies almost sure finite reflection mass. -/
theorem twoSidedReflectionMass_finite_ae_of_positive_moment
    (hq : 0 < q)
    (hm : (∫⁻ ω, (twoSidedReflectionMass γ B Z ω) ^ q ∂P) < ⊤) :
    ∀ᵐ ω ∂P, twoSidedReflectionMass γ B Z ω < ⊤ := by
  have hf := ae_lt_top' (twoSidedReflectionMass_rpow_aemeasurable_of_lateral
    P γ q B Z hB hZ) hm.ne
  filter_upwards [hf] with ω hω
  apply lt_top_iff_ne_top.mpr
  aesop

end

end

/-- Two enclosing moment bounds control every intervening reflection moment. -/
theorem twoSidedReflectionMass_moment_le_endpoints
    (γ l u q : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : IsLateralGMCOf P γ Z)
    (hl : l ≤ q) (hu : q ≤ u) :
    (∫⁻ ω, (twoSidedReflectionMass γ B Z ω) ^ q ∂P) ≤
      (∫⁻ ω, (twoSidedReflectionMass γ B Z ω) ^ l ∂P) +
        (∫⁻ ω, (twoSidedReflectionMass γ B Z ω) ^ u ∂P) := lintegral_rpow_le_endpoint_sum P _
    (twoSidedReflectionMass_aemeasurable_of_lateral P γ B Z hB hZ) hl hu

/-- The two conditioned-process clauses already imply AE measurability of the whole path pair. -/
theorem conditionedPair_aemeasurable (B : Ω → BrownianPath × BrownianPath) (ν : ℝ)
    (hB : IsTwoSidedConditionedBrownianProcess P B ν) : AEMeasurable B P :=
  hB.1.1.prodMk hB.2.1.1

/-- Endpoint moment bounds assemble the exact uniform moment conclusion for a family of
reflection data. The enclosing orders and their bounds are supplied explicitly. -/
theorem twoSidedReflectionMass_uniform_moments_of_endpoints
    (Kγ Kν Kq : Set ℝ)
    (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : ℝ → Ω → Measure ℝ)
    (hData : ∀ γ ∈ Kγ, ∀ ν ∈ Kν,
      IsTwoSidedConditionedBrownianProcess P (B ν) ν ∧
        IsLateralGMCOf P γ (Z γ) ∧ IndepFun (B ν) (Z γ) P)
    (l u : ℝ) (hl : ∀ q ∈ Kq, l ≤ q) (hu : ∀ q ∈ Kq, q ≤ u)
    (Cl Cu : ℝ≥0∞) (hCl : Cl < ⊤) (hCu : Cu < ⊤)
    (hLower : ∀ γ ∈ Kγ, ∀ ν ∈ Kν,
      (∫⁻ ω, (twoSidedReflectionMass γ (B ν) (Z γ) ω) ^ l ∂P) ≤ Cl)
    (hUpper : ∀ γ ∈ Kγ, ∀ ν ∈ Kν,
      (∫⁻ ω, (twoSidedReflectionMass γ (B ν) (Z γ) ω) ^ u ∂P) ≤ Cu) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ γ ∈ Kγ, ∀ ν ∈ Kν, ∀ q ∈ Kq,
      (∫⁻ ω, (twoSidedReflectionMass γ (B ν) (Z γ) ω) ^ q ∂P) ≤ C := by
  refine ⟨Cl + Cu, ENNReal.add_lt_top.mpr ⟨hCl, hCu⟩, ?_⟩
  intro γ hγ ν hν q hq
  have hd := hData γ hγ ν hν
  exact (twoSidedReflectionMass_moment_le_endpoints P γ l u q (B ν) (Z γ)
    (conditionedPair_aemeasurable P (B ν) ν hd.1) hd.2.1 (hl q hq) (hu q hq)).trans
    (add_le_add (hLower γ hγ ν hν) (hUpper γ hγ ν hν))

end

end DOZZ.Proofs
