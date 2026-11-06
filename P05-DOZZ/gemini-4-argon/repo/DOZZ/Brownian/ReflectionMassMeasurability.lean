/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ReflectionLawTransport
public import DOZZ.Brownian.MeasureTranslationFinite
public import Mathlib.Probability.Kernel.MeasurableLIntegral
public import Mathlib.Topology.Hom.ContinuousEval

/-!
# Measurability of the reflection mass input

The two-sided exponential mass is integrated against a locally finite, generally infinite
measure. We partition the line into the disjoint compact shells already used for measurable
translation, integrate over finite restrictions, and sum the measurable pieces.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The joined value of a pair of continuous entrance paths at a signed time. -/
noncomputable def reflectionPairValue (b : BrownianPath × BrownianPath) (s : ℝ) : ℝ :=
  if hs : 0 ≤ s then b.1 ⟨s, hs⟩ else b.2 ⟨-s, by linarith⟩


/-- The exponential integrand as a jointly measurable function of a path pair and signed time. -/
noncomputable def reflectionMassInputIntegrand (γ : ℝ)
    (z : (BrownianPath × BrownianPath) × ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (γ * reflectionPairValue z.1 z.2))


/-- The contribution of one finite shell to the reflection mass input. -/
noncomputable def reflectionMassInputShell (γ : ℝ) (n : ℕ)
    (z : (BrownianPath × BrownianPath) × Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ s, reflectionMassInputIntegrand γ (z.1, s) ∂
    (finiteRestrictionOnSet (translationShell n) z.2 : Measure ℝ)

/-- Summing the shell contributions gives a measurable extension to arbitrary path-measure pairs. -/
noncomputable def reflectionMassInputShellSum (γ : ℝ)
    (z : (BrownianPath × BrownianPath) × Measure ℝ) : ℝ≥0∞ :=
  ∑' n, reflectionMassInputShell γ n z




/-- If the lateral measure is locally finite almost surely, the reflection mass input is
almost-everywhere measurable under its joint path-measure law. -/
theorem aemeasurable_reflectionMassInput_map_of_locallyFinite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) γ
    (pair : Ω → (BrownianPath × BrownianPath) × Measure ℝ)
    (hpair : AEMeasurable pair P)
    (hlocal : ∀ᵐ ω ∂P, LocallyFiniteOnTranslationWindows (pair ω).2) :
    AEMeasurable (twoSidedReflectionMassInput γ) (P.map pair) := by
  have reflectionMassInput_eq_shellSum_of_locallyFinite (z : (BrownianPath × BrownianPath) × Measure ℝ) (hlocal : LocallyFiniteOnTranslationWindows z.2) : twoSidedReflectionMassInput γ z = reflectionMassInputShellSum γ z := by
    let f : ℝ → ℝ≥0∞ := fun s => reflectionMassInputIntegrand γ (z.1, s)
    have hfinite n : z.2 (translationShell n) < ⊤ := by
      exact lt_of_le_of_lt (measure_mono (translationShell_subset_window n)) (hlocal n)
    have hshellMeasure n :
        finiteRestrictionOnSet (translationShell n) z.2 =
          ⟨z.2.restrict (translationShell n),
            (MeasureTheory.isFiniteMeasure_restrict).2 (ne_of_lt (hfinite n))⟩ := by
      apply Subtype.ext
      simp [finiteRestrictionOnSet, hfinite n]
    change (∫⁻ s, f s ∂z.2) = ∑' n, reflectionMassInputShell γ n z
    calc
      (∫⁻ s, f s ∂z.2) = ∫⁻ s, f s ∂Measure.sum
          (fun n => z.2.restrict (translationShell n)) := by rw [(show Measure.sum (fun n => z.2.restrict (translationShell n)) = z.2 by rw [← Measure.restrict_iUnion translationShell_pairwise_disjoint (fun n => measurableSet_translationShell n), translationShell_iUnion, Measure.restrict_univ])]
      _ = ∑' n, ∫⁻ s, f s ∂z.2.restrict (translationShell n) :=
        lintegral_sum_measure f _
      _ = ∑' n, reflectionMassInputShell γ n z := by
        apply tsum_congr
        intro n
        rw [reflectionMassInputShell, hshellMeasure n]
        rfl
  have measurable_reflectionMassInputShellSum : Measurable (reflectionMassInputShellSum γ) := by
    have measurable_reflectionMassInputShell n : Measurable (reflectionMassInputShell γ n) := by
      have measurable_reflectionMassInputIntegrand : Measurable (reflectionMassInputIntegrand γ) := by
        have measurable_reflectionPairValue : Measurable (Function.uncurry reflectionPairValue) := by
          classical
          have heval : Measurable (fun z : (ℝ≥0 × BrownianPath) => z.2 z.1) := (continuous_eval.comp continuous_swap).measurable
          let pos : (BrownianPath × BrownianPath) × ℝ → ℝ := fun z =>
            z.1.1 ⟨max z.2 0, le_max_right _ _⟩
          let neg : (BrownianPath × BrownianPath) × ℝ → ℝ := fun z =>
            z.1.2 ⟨max (-z.2) 0, le_max_right _ _⟩
          have hneg : Measurable neg := by
            dsimp [neg]
            exact heval.comp ((by fun_prop : Measurable fun z : (BrownianPath × BrownianPath) × ℝ =>
              ((⟨max (-z.2) 0, le_max_right _ _⟩ : ℝ≥0), z.1.2)))
          convert (show Measurable (fun z : (BrownianPath × BrownianPath) × ℝ => if 0 ≤ z.2 then pos z else neg z) by exact Measurable.ite (measurableSet_le measurable_const measurable_snd) (by dsimp [pos]; exact heval.comp ((by fun_prop : Measurable fun z : (BrownianPath × BrownianPath) × ℝ => ((⟨max z.2 0, le_max_right _ _⟩ : ℝ≥0), z.1.1)))) hneg) using 1
          funext z
          change (if hs : 0 ≤ z.2 then z.1.1 ⟨z.2, hs⟩ else
              z.1.2 ⟨-z.2, by linarith⟩) =
            (if 0 ≤ z.2 then pos z else neg z)
          by_cases hs : 0 ≤ z.2
          · simp [hs, pos]
          · have hneg : 0 ≤ -z.2 := by linarith
            simp [hs, neg, max_eq_left hneg]
        change Measurable (fun z : (BrownianPath × BrownianPath) × ℝ =>
          ENNReal.ofReal (Real.exp (γ * reflectionPairValue z.1 z.2)))
        exact ENNReal.measurable_ofReal.comp
          (Real.measurable_exp.comp (measurable_const.mul (by change Measurable (Function.uncurry reflectionPairValue); exact measurable_reflectionPairValue)))
      change Measurable (fun z : (BrownianPath × BrownianPath) × Measure ℝ =>
        ∫⁻ s, reflectionMassInputIntegrand γ (z.1, s) ∂
          (finiteRestrictionOnSet (translationShell n) z.2 : Measure ℝ))
      exact (measurable_lintegral_finiteMeasure_parameter (f := reflectionMassInputIntegrand γ) (measurable_reflectionMassInputIntegrand)).comp (measurable_fst.prodMk ((measurable_finiteRestrictionOnSet _ (measurableSet_translationShell n)).comp measurable_snd))
    exact Measurable.tsum fun n => measurable_reflectionMassInputShell n
  have hlocalMap : ∀ᵐ z ∂P.map pair, LocallyFiniteOnTranslationWindows z.2 := by
    have hp : MeasurableSet {z : (BrownianPath × BrownianPath) × Measure ℝ |
        LocallyFiniteOnTranslationWindows z.2} :=
      measurableSet_locallyFiniteOnTranslationWindows.preimage measurable_snd
    rw [ae_map_iff hpair hp]
    exact hlocal
  exact (measurable_reflectionMassInputShellSum).aemeasurable.congr (show twoSidedReflectionMassInput γ =ᵐ[P.map pair] reflectionMassInputShellSum γ by filter_upwards [hlocalMap] with z hz; exact reflectionMassInput_eq_shellSum_of_locallyFinite z hz).symm

end DOZZ.Proofs

end
