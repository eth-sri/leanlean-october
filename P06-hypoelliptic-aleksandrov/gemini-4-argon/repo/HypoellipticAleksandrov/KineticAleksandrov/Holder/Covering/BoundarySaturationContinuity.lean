module

public import HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering.BoundarySaturationGeometry
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.Tactic

/-! # Continuity of cylinder intersection volume along continuous centers -/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering

open Set MeasureTheory Filter
open scoped Topology

/- A strict comparison of continuous real functions is locally constant away from equality. -/
theorem eventually_lt_iff_of_ne {f g : ℝ → ℝ} {r : ℝ}
    (hf : ContinuousAt f r) (hg : ContinuousAt g r) (hne : f r ≠ g r) :
    ∀ᶠ s in 𝓝 r, f s < g s ↔ f r < g r := by
  by_cases h : f r < g r
  · filter_upwards [hf.eventually_lt hg h] with s hs
    exact ⟨fun _ => h, fun _ => hs⟩
  · have hgt : g r < f r := lt_of_le_of_ne (le_of_not_gt h) hne.symm
    filter_upwards [hg.eventually_lt hf hgt] with s hs
    exact ⟨fun hlt => (not_lt_of_ge hs.le hlt).elim, fun hlt => (h hlt).elim⟩

/- A null equality fiber is avoided almost everywhere. -/
theorem ae_ne_of_null_fiber {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ℝ) (c : ℝ) (h : μ {x | f x = c} = 0) : ∀ᵐ x ∂μ, f x ≠ c := by
  simpa only [ae_iff, not_not] using h

/- Cylinder membership is locally constant in radius away from the four null faces. -/
end HypoellipticAleksandrov.KineticAleksandrov.Holder.Covering
