module

public import HypoellipticAleksandrov.KineticAleksandrov.SectionTwo.UniquenessMeasure
public import Mathlib.MeasureTheory.Measure.Regular

/-!
# Smooth compactly supported tests determine order and zero measure

Finite Borel measures on a finite-dimensional real normed space are compared, and shown to
vanish on an open set, through integrals of smooth `[0,1]`-valued test functions with compact
support.  This extends `SectionTwo.measure_eq_of_smooth_integral_eq` (equality of measures) to
the one-sided and zero cases.  The step is pure measure theory: compact sets are approximated
by smooth cutoffs (`exists_smooth_cutoff`), open sets from inside by compact sets, and
arbitrary sets from outside by open sets (outer regularity of finite Borel measures).  No
regularity assumption is made on the measures.

* `measure_compact_le_of_smooth_le`: compact `C ⊆ V` open gives `μ C ≤ ν V` from test
  inequalities.
* `measure_le_of_smooth_integral_le`: test inequalities with supports in an open `U`, with `μ`
  vanishing off `U`, give `μ ≤ ν` as measures.
* `measure_eq_zero_of_smooth_integral_eq_zero`: vanishing tests with supports in an open `U`
  give `μ U = 0`; the variant `measure_eq_zero_of_smooth_integral_eq_zero_of_support` adds an
  open set carrying the measure, so tests only need support in `F ∩ D`.
-/

@[expose] public section

open MeasureTheory Set Topology

namespace HypoellipticAleksandrov.KineticAleksandrov.Decay

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable {μ ν : Measure E}

/-- Compact sets inside an open set carrying the test *inequality* are dominated. -/
theorem measure_compact_le_of_smooth_le  [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {U : Set E}
    (h : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → ∫ x, φ x ∂μ ≤ ∫ x, φ x ∂ν)
    {C V : Set E} (hC : IsCompact C) (hV : IsOpen V) (hCV : C ⊆ V) (hVU : V ⊆ U) :
    μ C ≤ ν V := by
  obtain ⟨φ, hφ, hφc, hφV, hφr, hφ1⟩ :=
    SectionTwo.exists_smooth_cutoff hC hV hCV
  have hcont : Continuous φ := hφ.continuous
  have hint : ∀ (m : Measure E) [IsFiniteMeasure m], Integrable φ m := fun m _ =>
    hcont.integrable_of_hasCompactSupport hφc
  have h1 : μ.real C ≤ ∫ x, φ x ∂μ := by
    calc μ.real C = ∫ x, C.indicator _ x ∂μ := by
          rw [integral_indicator_one hC.measurableSet]
      _ ≤ ∫ x, φ x ∂μ := by
          refine integral_mono ((integrable_const _).indicator hC.measurableSet)
            (hint μ) ?_
          intro x
          by_cases hx : x ∈ C
          · simp_all
          simp_all
  have h2 : ∫ x, φ x ∂ν ≤ ν.real V := by
    calc ∫ x, φ x ∂ν ≤ ∫ x, V.indicator (1) x ∂ν := by
          refine integral_mono (hint ν)
            ((integrable_const _).indicator hV.measurableSet) ?_
          intro x
          by_cases hx : x ∈ V
          · simp_all
          · have : φ x = 0 := by
              by_contra hne
              exact hx (hφV (subset_tsupport φ hne))
            simp_all
      _ = ν.real V := by rw [integral_indicator_one hV.measurableSet]
  have h3 : μ.real C ≤ ν.real V := h1.trans ((h φ hφ hφc (hφV.trans hVU) hφr).trans h2)
  exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp h3

/-- Open sets inside `U` are dominated, by inner regularity of finite Borel measures. -/
theorem measure_open_le_of_smooth_le  [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {U : Set E}
    (h : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → ∫ x, φ x ∂μ ≤ ∫ x, φ x ∂ν)
    {V : Set E} (hV : IsOpen V) (hVU : V ⊆ U) : μ V ≤ ν V := by
  refine le_of_forall_lt fun r hr => ?_
  obtain ⟨C, hCV, hCc, hrC⟩ := hV.exists_lt_isCompact hr
  exact hrC.trans_le (measure_compact_le_of_smooth_le h hCc hV hCV hVU)

/-- Finite Borel measures with `μ Uᶜ = 0` that satisfy the smooth-test inequality for tests
supported in the open set `U` are ordered: `μ ≤ ν`.  Only `μ` needs to vanish off `U`. -/
theorem measure_le_of_smooth_integral_le  [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {U : Set E} (hU : IsOpen U) (hμ : μ Uᶜ = 0)
    (h : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → ∫ x, φ x ∂μ ≤ ∫ x, φ x ∂ν) :
    μ ≤ ν := by
  have hopen : ∀ O : Set E, μ O ≤ μ (O ∩ U) := by
    intro O
    calc μ O ≤ μ _ := measure_mono (fun x hx => by
          grind)
      _ ≤ μ (O ∩ U) + μ Uᶜ := measure_union_le _ _
      _ = μ _ := by simp_all
  have hopenle : ∀ O : Set E, IsOpen O → μ O ≤ ν O := fun O hO =>
    (hopen O).trans ((measure_open_le_of_smooth_le h (hO.inter hU) inter_subset_right).trans
      (measure_mono inter_subset_left))
  refine Measure.le_iff'.mpr fun A => ?_
  rw [Set.measure_eq_iInf_isOpen A ν]
  refine le_iInf₂ fun O hAO => ?_
  exact le_iInf fun hO => (measure_mono hAO).trans (hopenle O hO)

/-- A finite Borel measure all of whose smooth `[0,1]`-valued tests supported in the open
set `U` integrate to zero gives no mass to `U`. -/
theorem measure_eq_zero_of_smooth_integral_eq_zero {μ : Measure E} [IsFiniteMeasure μ]
    {U : Set E} (hU : IsOpen U)
    (h : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → ∫ x, φ x ∂μ = 0) :
    μ U = 0 := by
  have hle : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → ∫ x, φ x ∂μ ≤ ∫ x, φ x ∂(0 : Measure E) := by
    simp_all
  have := measure_open_le_of_smooth_le hle hU subset_rfl
  simp_all

/-- Zero mass on an open set `F` from vanishing smooth tests supported in `F ∩ D`, where `D`
is an open set carrying all the mass of `μ`. -/
theorem measure_eq_zero_of_smooth_integral_eq_zero_of_support {μ : Measure E}
    [IsFiniteMeasure μ] {F D : Set E} (hF : IsOpen F) (hD : IsOpen D) (hμ : μ Dᶜ = 0)
    (h : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ F ∩ D →
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → ∫ x, φ x ∂μ = 0) :
    μ F = 0 := by
  have h0 := measure_eq_zero_of_smooth_integral_eq_zero (hF.inter hD) h
  refine measure_mono_null (fun x hx => ?_) (measure_union_null h0 hμ)
  grind

end HypoellipticAleksandrov.KineticAleksandrov.Decay
