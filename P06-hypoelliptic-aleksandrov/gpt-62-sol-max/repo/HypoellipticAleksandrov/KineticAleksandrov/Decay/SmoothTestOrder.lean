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

export SectionTwo (measure_compact_le_of_smooth_le measure_open_le_of_smooth_le
  measure_le_of_smooth_integral_le)

/-- A finite Borel measure all of whose smooth `[0,1]`-valued tests supported in the open
set `U` integrate to zero gives no mass to `U`. -/
theorem measure_eq_zero_of_smooth_integral_eq_zero {μ : Measure E} [IsFiniteMeasure μ]
    {U : Set E} (hU : IsOpen U)
    (h : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → ∫ x, φ x ∂μ = 0) :
    μ U = 0 := by
  have hle : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → ∫ x, φ x ∂μ ≤ ∫ x, φ x ∂(0 : Measure E) := by
    intro φ a b c d
    simp [h φ a b c d]
  have := measure_open_le_of_smooth_le hle hU subset_rfl
  simpa using this

/-- Zero mass on an open set `F` from vanishing smooth tests supported in `F ∩ D`, where `D`
is an open set carrying all the mass of `μ`. -/
theorem measure_eq_zero_of_smooth_integral_eq_zero_of_support {μ : Measure E}
    [IsFiniteMeasure μ] {F D : Set E} (hF : IsOpen F) (hD : IsOpen D) (hμ : μ Dᶜ = 0)
    (h : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ F ∩ D →
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) → ∫ x, φ x ∂μ = 0) :
    μ F = 0 := by
  rw [← measure_inter_conull (s := F) hμ]
  exact measure_eq_zero_of_smooth_integral_eq_zero (hF.inter hD) h

end HypoellipticAleksandrov.KineticAleksandrov.Decay
