module

public import Mathlib.MeasureTheory.Measure.Portmanteau

@[expose] public section

open Filter Topology
namespace MeasureTheory.ProbabilityMeasure

theorem tendsto_real_clopen {Ω ι : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    [OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω] {l : Filter ι}
    {μ : ProbabilityMeasure Ω} {μs : ι → ProbabilityMeasure Ω} (h : Tendsto μs l (𝓝 μ))
    {E : Set Ω} (hE : IsClopen E) :
    Tendsto (fun i => (μs i).toMeasure.real E) l (𝓝 (μ.toMeasure.real E)) := by
  simpa [Function.comp_def] using
      NNReal.continuous_coe.continuousAt.tendsto.comp (tendsto_measure_of_isClopen_of_tendsto h hE)

end MeasureTheory.ProbabilityMeasure
