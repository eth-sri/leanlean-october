module

public import PottsDiscontinuity.Potts.MonotoneEventLimits

/-! Transfer of connection-data limits through uniformly positive conditioning. -/

@[expose] public section

namespace PottsDiscontinuity.Potts

open MeasureTheory Filter Topology
noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- A bounded density and the same local limit transfer a decreasing diagonal
 event limit. This applies to the four-corner conditioning with `δ = (1-p)^4`. -/
theorem decreasing_event_limit_of_density
    (μs νs : ℕ → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (E : ℕ → Set X) (hE : Antitone E) (hmeas : ∀ n, MeasurableSet (E n))
    (δ : ℝ) (hδ : 0 < δ)
    (hdensity : ∀ᶠ n : ℕ in atTop, ∀ S : Set X, MeasurableSet S →
      δ * (νs n).toMeasure.real S ≤ (μs n).toMeasure.real S)
    (hμlocal : ∀ m, Tendsto (fun n => (μs n).toMeasure.real (E m)) atTop (𝓝 (μ.toMeasure.real (E m))))
    (hνlocal : ∀ m, Tendsto (fun n => (νs n).toMeasure.real (E m)) atTop (𝓝 (μ.toMeasure.real (E m))))
    (hdiag : Tendsto (fun n => (μs n).toMeasure.real (E n)) atTop (𝓝 (μ.toMeasure.real (⋂ n, E n)))) :
    Tendsto (fun n => (νs n).toMeasure.real (E n)) atTop (𝓝 (μ.toMeasure.real (⋂ n, E n))) := by
  let L := μ.toMeasure.real (⋂ n, E n)
  have hcont : Tendsto (fun n => μ.toMeasure.real (E n)) atTop (𝓝 L) :=
    (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp
      (tendsto_measure_iInter_atTop (fun n => (hmeas n).nullMeasurableSet) hE ⟨0, measure_ne_top _ _⟩)
  have hlower (m : ℕ) : ∀ᶠ n : ℕ in atTop,
      (νs n).toMeasure.real (E m) -
        ((μs n).toMeasure.real (E m) - (μs n).toMeasure.real (E n)) / δ ≤
      (νs n).toMeasure.real (E n) := by
    filter_upwards [hdensity, eventually_ge_atTop m] with n hn hmn
    have hd := hn (E m \ E n) ((hmeas m).diff (hmeas n))
    rw [measureReal_sdiff (hE hmn) (hmeas n),
      measureReal_sdiff (hE hmn) (hmeas n)] at hd
    have hle :=
      (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using hd)
    linarith
  have halimit : Tendsto (fun m => μ.toMeasure.real (E m) - (μ.toMeasure.real (E m) - L) / δ)
      atTop (𝓝 L) := by
    have ht := hcont.sub ((hcont.sub (tendsto_const_nhds (x := L))).div_const δ)
    simpa using ht
  refine tendsto_order.2 ⟨eventually_lt_of_lower_limits halimit ?_ hlower,
    eventually_lt_of_lower_limits (α := ℝᵒᵈ) hcont hνlocal ?_⟩
  · exact fun m => (hνlocal m).sub (((hμlocal m).sub hdiag).div_const δ)
  · exact fun m => (eventually_ge_atTop m).mono fun _ hn => measureReal_mono (hE hn)

end
end PottsDiscontinuity.Potts
