module

public import Mathlib.MeasureTheory.Measure.Portmanteau

/-! Diagonal limits of increasing and decreasing connection approximations. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open MeasureTheory Filter Topology
noncomputable section

/-- One-sided control by approximations whose iterated limit is `x`. -/
theorem eventually_lt_of_lower_limits {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] {u l : ℕ → α} {v : ℕ → ℕ → α} {x : α}
    (h : Tendsto l atTop (𝓝 x)) (hv : ∀ m, Tendsto (v m) atTop (𝓝 (l m)))
    (hle : ∀ m, ∀ᶠ n in atTop, v m n ≤ u n) (a : α) (ha : a < x) :
    ∀ᶠ n in atTop, a < u n := by
  obtain ⟨m, hm⟩ := (h.eventually (lt_mem_nhds ha)).exists
  filter_upwards [(hv m).eventually (lt_mem_nhds hm), hle m] with n hn hle'
  exact hn.trans_le hle'

variable {X : Type*} [MeasurableSpace X]

/-- Increasing finite-path events may grow with the volume if each finite law
is dominated by the limiting law on that event. -/
theorem increasing_event_diagonal_tendsto (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (E : ℕ → Set X) (hE : Monotone E)
    (hlocal : ∀ m, Tendsto (fun n => (μs n).toMeasure.real (E m)) atTop (𝓝 (μ.toMeasure.real (E m))))
    (hdom : ∀ n, (μs n).toMeasure.real (E n) ≤ μ.toMeasure.real (E n)) :
    Tendsto (fun n => (μs n).toMeasure.real (E n)) atTop (𝓝 (μ.toMeasure.real (⋃ n, E n))) := by
  have hcont : Tendsto (fun n => μ.toMeasure.real (E n)) atTop (𝓝 (μ.toMeasure.real (⋃ n, E n))) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp (tendsto_measure_iUnion_atTop hE)
  refine tendsto_order.2 ⟨eventually_lt_of_lower_limits hcont hlocal ?_, ?_⟩
  · exact fun m => (eventually_ge_atTop m).mono fun _ hn => measureReal_mono (hE hn)
  · intro b hb
    exact (hcont.eventually (gt_mem_nhds hb)).mono fun n hn => (hdom n).trans_lt hn

/-- Decreasing wired events may grow with the volume if every finite law
 dominates the limiting law on that event. -/
theorem decreasing_event_diagonal_tendsto (μs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (E : ℕ → Set X) (hE : Antitone E) (hmeas : ∀ n, MeasurableSet (E n))
    (hlocal : ∀ m, Tendsto (fun n => (μs n).toMeasure.real (E m)) atTop (𝓝 (μ.toMeasure.real (E m))))
    (hdom : ∀ n, μ.toMeasure.real (E n) ≤ (μs n).toMeasure.real (E n)) :
    Tendsto (fun n => (μs n).toMeasure.real (E n)) atTop (𝓝 (μ.toMeasure.real (⋂ n, E n))) := by
  have hcont : Tendsto (fun n => μ.toMeasure.real (E n)) atTop (𝓝 (μ.toMeasure.real (⋂ n, E n))) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
      (tendsto_measure_iInter_atTop (fun n => (hmeas n).nullMeasurableSet) hE ⟨0, measure_ne_top _ _⟩)
  refine tendsto_order.2 ⟨?_, eventually_lt_of_lower_limits (α := ℝᵒᵈ) hcont hlocal ?_⟩
  · intro a ha
    exact (hcont.eventually (lt_mem_nhds ha)).mono fun n hn => hn.trans_le (hdom n)
  · exact fun m => (eventually_ge_atTop m).mono fun _ hn => measureReal_mono (hE hn)

end
end PottsDiscontinuity.Potts
