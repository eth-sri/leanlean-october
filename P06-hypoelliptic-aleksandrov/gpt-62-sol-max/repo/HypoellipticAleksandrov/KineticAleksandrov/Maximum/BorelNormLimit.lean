module

public import HypoellipticAleksandrov.KineticAleksandrov.Maximum.BorelDominated
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! # Source norm stability under the vanishing classical coefficient error -/

@[expose] public section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Filter
open scoped Topology

/-- An error tending to zero in Lp controls the distance of the source norms. -/
theorem borel_source_norm_tendsto {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {p : ℝ} (hp : 1 ≤ p) {F : E → ℝ} {G e : ℕ → E → ℝ}
    (hF : MemLp F (ENNReal.ofReal p) μ)
    (he : ∀ j, MemLp (e j) (ENNReal.ofReal p) μ)
    (hGm : ∀ j, AEStronglyMeasurable (G j) μ)
    (hclose : ∀ j, ∀ᵐ z ∂μ, |G j z - F z| ≤ |e j z|)
    (ht : Tendsto (fun j => (eLpNorm (e j) (ENNReal.ofReal p) μ).toReal) atTop (𝓝 0)) :
    Tendsto (fun j => (eLpNorm (G j) (ENNReal.ofReal p) μ).toReal) atTop
      (𝓝 (eLpNorm F (ENNReal.ofReal p) μ).toReal) := by
  have hsub j := (hGm j).sub hF.aestronglyMeasurable
  have hle j := hclose j
  have hG j : MemLp (G j) (ENNReal.ofReal p) μ := by
    simpa using (((he j).of_le (hsub j) (hle j)).add hF)
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  suffices h : Tendsto (fun j => (hG j).toLp (G j)) atTop (𝓝 (hF.toLp F)) by
    simpa using h.norm
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ => dist_nonneg) (fun j => ?_) ht
  rw [Lp.dist_edist, Lp.edist_toLp_toLp]
  exact ENNReal.toReal_mono (he j).eLpNorm_ne_top (eLpNorm_mono_ae (hsub j) (hle j))

end HypoellipticAleksandrov.KineticAleksandrov
