/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Reflection.LastCut
public import DOZZ.Brownian.LateralMoments.UnitInverse

/-!
# Brownian reflection-mass moment estimates

The lateral unit-block inverse moments `∫⁻ (Z [0,1])^(-v) < ⊤` (all `v > 0`) are the single input
the conditional moment estimates of this directory leave open. They give the uniform inverse
moments of the conditioned unit-block mass, the last-cut moment bound, and, through almost-sure
nonvanishing of the lateral chaos, the zero-drift moment limits and the endpoint limit `R → -1`
([KRV, Lemma 3.3], [KRV, §12.3]).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs
section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
section
variable (γ : ℝ)

/-- A lateral GMC is almost surely nonzero: its unit-block mass has finite inverse moments. -/
theorem lateralGMC_ne_zero_ae (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z) : ∀ᵐ ω ∂P, Z ω ≠ 0 := by
  have hm : AEMeasurable (fun ω => Z ω (Icc 0 1)) P :=
    (Measure.measurable_coe measurableSet_Icc).comp_aemeasurable hZ.2.2.2.1
  filter_upwards [ae_pos_of_lintegral_rpow_neg_lt_top hm one_pos
    (lateralGMC_unit_inverse_moment_lt_top P γ Z hZ 1 one_pos)] with ω hω h0
  simp_all
section
variable (hγ : 0 < γ) (hγ2 : γ < 2)
include hγ hγ2

/-- The last-cut estimate for the two-sided reflection integral; it does not assume that the
discarded and retained masses are independent. -/
theorem reflectionMass_lastCut_bound
    (Kν Kp : Set ℝ)
    (hKν : IsCompact Kν) (hKp : IsCompact Kp)
    (B : ℝ → Ω → BrownianPath × BrownianPath)
    (hB : ∀ ν ∈ Kν,
      0 < ν ∧ IsTwoSidedConditionedBrownianProcess P (B ν) ν)
    (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (hInd : ∀ ν ∈ Kν, IndepFun (B ν) Z P)
    (hp : ∀ p ∈ Kp, 0 < p ∧ p < 4 / γ ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ ν ∈ Kν, ∀ p ∈ Kp, ∀ c : ℝ, 0 ≤ c →
        0 ≤
          (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ (B ν) Z ω) p ∂P).toReal -
          (∫⁻ ω, ENNReal.rpow (twoSidedReflectionCutMass γ c (B ν) Z ω) p ∂P).toReal ∧
        (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ (B ν) Z ω) p ∂P).toReal -
          (∫⁻ ω, ENNReal.rpow (twoSidedReflectionCutMass γ c (B ν) Z ω) p ∂P).toReal ≤
            C * Real.exp (-γ * c) := reflectionMass_lastCut_bound_of_inverse P γ hγ hγ2 Kν Kp hKν hKp B hB Z hZ hInd hp
    (fun v hv => lateralGMC_unit_inverse_moment_lt_top P γ Z hZ v hv)

/-- The law-level Brownian/GMC input to [KRV, Lemma 10.6], with small power `ν/γ`. The local
epsilon domain and zero-mode evaluation are handled in `structureConstant_lastone_limit`;
this declaration states only the conditioned integral limit. -/
theorem lastone_brownian_smallPower_limit
    (Z : Ω → Measure ℝ)
    (B : ℝ → Ω → BrownianPath × BrownianPath)
    (hB : ∀ ν : ℝ, 0 < ν → IsTwoSidedConditionedBrownianProcess P (B ν) ν)
    (hZ : IsLateralGMCOf P γ Z)
    (hInd : ∀ ν : ℝ, 0 < ν → IndepFun (B ν) Z P) :
    Tendsto (fun ν : ℝ =>
      (∫⁻ ω, ENNReal.rpow (twoSidedReflectionMass γ (B ν) Z ω) (ν / γ) ∂P).toReal)
      (𝓝[>] 0) (𝓝 1) := by
  have _consumed := hγ2
  exact lastone_brownian_smallPower_limit_of_ne_zero P γ hγ Z B hB hZ hInd
    (lateralGMC_ne_zero_ae P γ Z hZ)

end

end

/-- The consequence of `reflectionMoment_zeroDrift_tendsto_one` for the full reflection
coefficient: `R(α)→−1` as `α↑Q`. -/
theorem reflectionR_tendsto_Q
    (γ μ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : ∀ α, γ / 2 < α → α < Q γ → IsReflectionData P γ α (B α) Z) :
    Tendsto (fun α : ℝ => reflectionR P γ μ α (B α) Z)
      (𝓝[<] (Q γ)) (𝓝 (-1)) := by
  have _consumed := hγ2
  have hQ : γ / 2 < Q γ := by
    unfold Q
    simp_all
  have hZ :=
    (hData ((γ / 2 + Q γ) / 2) (by linarith) (by linarith)).2.1
  exact reflectionR_tendsto_Q_of_ne_zero P γ μ hγ hμ B Z hData (lateralGMC_ne_zero_ae P γ Z hZ)

end

end DOZZ.Proofs

end
