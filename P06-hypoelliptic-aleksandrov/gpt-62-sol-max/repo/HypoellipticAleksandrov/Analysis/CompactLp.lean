module

public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! Restricted Lᵖ membership for continuous data on compact carriers. -/

@[expose] public section

open MeasureTheory

namespace HypoellipticAleksandrov.Analysis

theorem memLp_restrict_of_isCompact {X E : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [NormedAddCommGroup E] [SecondCountableTopologyEither X E]
    {s : Set X} {f : X → E} {μ : Measure X} [IsFiniteMeasureOnCompacts μ]
    (hs : IsCompact s) (hf : ContinuousOn f s) (p : ENNReal) : MemLp f p (μ.restrict s) := by
  let : IsFiniteMeasure (μ.restrict s) := ⟨by simpa using hs.measure_lt_top (μ := μ)⟩
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuousOn hf
  exact MemLp.of_bound (hf.aestronglyMeasurable hs.measurableSet) C
    ((ae_restrict_mem hs.measurableSet).mono hC)

end HypoellipticAleksandrov.Analysis
