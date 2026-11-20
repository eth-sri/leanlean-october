module

import HypoellipticAleksandrov.Analysis.SmoothCutoff

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Smooth compactly supported tests determine finite measures

Two finite Borel measures on a finite-dimensional real normed space which both
vanish off an open set `U` are equal as soon as they have the same integral
against every smooth `[0,1]`-valued function with compact support inside `U`.
-/

@[expose] public section

open MeasureTheory Set Topology

namespace HypoellipticAleksandrov.KineticAleksandrov.SectionTwo

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- A smooth cutoff, compactly supported in an open set, equal to one on a compact set. -/
theorem exists_smooth_cutoff {C V : Set E} (hC : IsCompact C) (hV : IsOpen V) (hCV : C ⊆ V) :
    ∃ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ V ∧
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧ ∀ x ∈ C, φ x = 1 := Analysis.exists_smooth_cutoff hC hV hCV

section
variable {μ ν : Measure E}

/-- Compact sets inside an open set carrying the test *inequality* are dominated. -/
theorem measure_compact_le_of_smooth_le [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {U : Set E}
    (h : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → ∫ x, φ x ∂μ ≤ ∫ x, φ x ∂ν)
    {C V : Set E} (hC : IsCompact C) (hV : IsOpen V) (hCV : C ⊆ V) (hVU : V ⊆ U) :
    μ C ≤ ν V := by
  obtain ⟨φ, hφ, hc, hVφ, hr, h1⟩ := exists_smooth_cutoff hC hV hCV
  have hint (m : Measure E) [IsFiniteMeasure m] : Integrable φ m :=
    hφ.continuous.integrable_of_hasCompactSupport hc
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change μ.real C ≤ ν.real V
  rw [← integral_indicator_one hC.measurableSet, ← integral_indicator_one hV.measurableSet]
  refine (integral_mono ((integrable_const (1 : ℝ)).indicator hC.measurableSet) (hint μ) ?_).trans
    ((h φ hφ hc (hVφ.trans hVU) hr).trans
      (integral_mono (hint ν) ((integrable_const (1 : ℝ)).indicator hV.measurableSet) ?_))
  · intro x
    by_cases hx : x ∈ C
    · simp [hx, h1 x hx]
    · simpa [hx] using (hr x).1
  · intro x
    by_cases hx : x ∈ V
    · simpa [hx] using (hr x).2
    · simp [hx, image_eq_zero_of_notMem_tsupport (fun hx' => hx (hVφ hx'))]

/-- Open sets inside `U` are dominated, by inner regularity of finite Borel measures. -/
theorem measure_open_le_of_smooth_le [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {U : Set E}
    (h : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → ∫ x, φ x ∂μ ≤ ∫ x, φ x ∂ν)
    {V : Set E} (hV : IsOpen V) (hVU : V ⊆ U) : μ V ≤ ν V := by
  refine le_of_forall_lt fun r hr => ?_
  obtain ⟨C, hCV, hCc, hrC⟩ := hV.exists_lt_isCompact hr
  exact hrC.trans_le (measure_compact_le_of_smooth_le h hCc hV hCV hVU)

/-- Finite Borel measures with `μ Uᶜ = 0` that satisfy the smooth-test inequality for tests
supported in the open set `U` are ordered: `μ ≤ ν`.  Only `μ` needs to vanish off `U`. -/
theorem measure_le_of_smooth_integral_le [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {U : Set E} (hU : IsOpen U) (hμ : μ Uᶜ = 0)
    (h : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → ∫ x, φ x ∂μ ≤ ∫ x, φ x ∂ν) :
    μ ≤ ν := by
  refine Measure.le_iff'.mpr fun A => ?_
  rw [Set.measure_eq_iInf_isOpen A ν]
  refine le_iInf₂ fun O hAO => le_iInf fun hO => (measure_mono hAO).trans ?_
  rw [← measure_inter_conull (s := O) hμ]
  exact (measure_open_le_of_smooth_le h (hO.inter hU) inter_subset_right).trans
    (measure_mono inter_subset_left)

/-- Finite measures vanishing off an open set `U` are determined by smooth compact tests in `U`. -/
theorem measure_eq_of_smooth_integral_eq [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {U : Set E} (hU : IsOpen U) (hμ : μ Uᶜ = 0) (hν : ν Uᶜ = 0)
    (h : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → ∫ x, φ x ∂μ = ∫ x, φ x ∂ν) :
    μ = ν := le_antisymm
  (measure_le_of_smooth_integral_le hU hμ fun φ a b c d => (h φ a b c d).le)
  (measure_le_of_smooth_integral_le hU hν fun φ a b c d => (h φ a b c d).ge)

end

end HypoellipticAleksandrov.KineticAleksandrov.SectionTwo
