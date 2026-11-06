/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.Statements.Brownian.LateralProjectedGMC
public import DOZZ.Statements.Defs.IsGMCOf
import Mathlib.Topology.Order.Compact

/-!
# Local finiteness of the polar lateral projection

On a compact logarithmic-radius interval the radial Wick weight is bounded, since the radial
path is continuous. A finite plane measure therefore has finite projected mass on every bounded
interval. This is one carrier condition needed for the lateral GMC layer.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- The polar projection of a finite source measure has finite mass on every compact interval.
The bound depends on the compact interval and the continuous radial path. -/
theorem lateralProjectedGMC_Icc_ne_top
    (γ : ℝ) (A : TwoSidedPath) (M : Measure ℂ) [IsFiniteMeasure M]
    (a b : ℝ) :
    lateralProjectedGMC γ A M (Set.Icc a b) < ⊤ := by
  by_cases hab : a ≤ b
  · obtain ⟨s₀, hs₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (nonempty_Icc.mpr hab) (continuous_abs.comp A.continuous).continuousOn
    let K := |A s₀|
    let R := max |a| |b|
    let C := |γ| * K + |γ * Q γ| * R
    have hK_nonneg : 0 ≤ K := abs_nonneg _
    have hC_nonneg : 0 ≤ C := by
      positivity
    have hweight (x : ℂ)
        (hx : -Real.log ‖x‖ ∈ Set.Icc a b) :
        ENNReal.ofReal (if ‖x‖ = 0 then 0 else
          Real.exp (-γ * A (-Real.log ‖x‖) +
            γ * Q γ * |Real.log ‖x‖|)) ≤ ENNReal.ofReal (Real.exp C) := by
      by_cases hx0 : ‖x‖ = 0
      · simp_all
      · have hs : -Real.log ‖x‖ ∈ Set.Icc a b := hx
        have hAs : |A (-Real.log ‖x‖)| ≤ K := by
          tauto
        have hlog : |Real.log ‖x‖| ≤ R := by
          grind
        have hexp : -γ * A (-Real.log ‖x‖) +
            γ * Q γ * |Real.log ‖x‖| ≤ C := by
          dsimp [C]
          calc
            -γ * A _ + γ * Q γ * |Real.log ‖x‖|
                ≤ abs _ +
                    abs _ :=
                    add_le_add (le_abs_self _) (le_abs_self _)
            _ = abs γ * abs (A (-Real.log ‖x‖)) +
                  abs (γ * Q γ) * abs (Real.log ‖x‖) := by
                  simp
            _ ≤ abs γ * K + abs (γ * Q γ) * R := by
                  bound
        bound
    let ρ : ℂ → ℝ := fun x => -Real.log ‖x‖
    let w : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (if ‖x‖ = 0 then 0 else
      Real.exp (-γ * A (ρ x) + γ * Q γ * |Real.log ‖x‖|))
    have hρ : Measurable ρ := measurable_neg.comp (Real.measurable_log.comp measurable_norm)
    have hpre : MeasurableSet (ρ ⁻¹' Set.Icc a b) :=
      measurableSet_Icc.preimage hρ
    unfold lateralProjectedGMC
    change (M.withDensity w).map ρ (Set.Icc a b) < ⊤
    rw [Measure.map_apply hρ measurableSet_Icc,
      withDensity_apply w hpre]
    have hmono :
        (∫⁻ x in ρ ⁻¹' Set.Icc a b, w x ∂M) ≤
          ∫⁻ x in ρ ⁻¹' Set.Icc a b, ENNReal.ofReal (Real.exp C) ∂M := by
      apply setLIntegral_mono' hpre
      intro x hx
      exact hweight x hx
    exact lt_of_le_of_lt hmono (by
      rw [setLIntegral_const]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top M _))
  · have hempty : Set.Icc a b = ∅ := Set.Icc_eq_empty hab
    have hρ : Measurable (fun x : ℂ => -Real.log ‖x‖) :=
      measurable_neg.comp (Real.measurable_log.comp measurable_norm)
    rw [lateralProjectedGMC, Measure.map_apply hρ measurableSet_Icc, hempty]
    simp

/-- A finite random GMC source and any samplewise continuous radial path give the almost-sure
compact-interval finiteness clause of the lateral carrier. -/
theorem ae_lateralProjectedGMC_interval_ne_top
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ : ℝ) (A : Ω → TwoSidedPath) (M : Ω → Measure ℂ)
    (hM : ∀ ω, IsFiniteMeasure (M ω)) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ,
      lateralProjectedGMC γ (A ω) (M ω) (Set.Icc a b) < ⊤ := Filter.Eventually.of_forall fun ω a b => @lateralProjectedGMC_Icc_ne_top γ (A ω) (M ω) (hM ω) a b

end DOZZ.Proofs

end
