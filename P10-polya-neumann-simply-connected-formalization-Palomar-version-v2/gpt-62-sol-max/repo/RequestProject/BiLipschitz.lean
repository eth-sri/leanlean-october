module

public import RequestProject.LipschitzChange
public import RequestProject.Defs

/-! Bounded pullback in `L²` for a homeomorphism with Lipschitz inverse. -/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace PolyaNeumann

variable {Ω : Set ℂ} {f : ℂ ≃ₜ ℂ} {K : NNReal}


/-- A map that is Lipschitz on an open set is differentiable almost everywhere on it. -/
lemma ae_differentiableAt_of_lipschitzOnWith {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ}
    (hF : LipschitzOnWith K F U) : ∀ᵐ x ∂(volume.restrict U), DifferentiableAt ℝ F x := by
  have h := hF.ae_differentiableWithinAt_of_mem (μ := volume)
  rw [ae_restrict_iff' hU.measurableSet]
  filter_upwards [h] with x hx hxU
  exact (hx hxU).differentiableAt (hU.mem_nhds hxU)

/-- The restricted pushforward is bounded by the area distortion of the inverse. -/
theorem map_volume_restrict_le (hg : LipschitzOnWith K f.symm (f '' Ω)) :
    Measure.map f (volume.restrict Ω) ≤ (K : ℝ≥0∞)^2 • volume.restrict (f '' Ω) := by
  refine Measure.le_iff.mpr fun s hs => ?_
  have e : f.symm '' (s ∩ f '' Ω) = f ⁻¹' s ∩ Ω := by ext x; simp
  rw [Measure.map_apply f.continuous.measurable hs,
    Measure.restrict_apply (f.continuous.measurable hs), Measure.smul_apply,
    Measure.restrict_apply hs, ← e]
  exact volume_image_le_of_lipschitzOnWith (hg.mono inter_subset_right)

theorem quasiMeasurePreserving_restrict (hg : LipschitzOnWith K f.symm (f '' Ω)) :
    Measure.QuasiMeasurePreserving f (volume.restrict Ω) (volume.restrict (f '' Ω)) :=
  ⟨f.continuous.measurable, Measure.absolutelyContinuous_of_le_smul (map_volume_restrict_le hg)⟩

theorem eLpNorm_comp_bilip_le (hg : LipschitzOnWith K f.symm (f '' Ω)) (H : ℂ → ℂ) :
    eLpNorm (H ∘ f) 2 (volume.restrict Ω) ≤ K * eLpNorm H 2 (volume.restrict (f '' Ω)) := by
  have hf : MeasurableEmbedding (f : ℂ → ℂ) := f.toMeasurableEquiv.measurableEmbedding
  rw [← hf.eLpNorm_map_measure]
  have h := eLpNorm_le_of_measure_le_smul (f := H) (p := 2) (map_volume_restrict_le hg)
  rwa [show (1 / (2 : ℝ≥0∞)).toReal = (2 : ℝ)⁻¹ by norm_num,
    ← ENNReal.rpow_two, ENNReal.rpow_rpow_inv (by norm_num)] at h

theorem memLp_comp_bilip (hg : LipschitzOnWith K f.symm (f '' Ω)) {H : ℂ → ℂ}
    (hH : MemLp H 2 (volume.restrict (f '' Ω))) : MemLp (H ∘ f) 2 (volume.restrict Ω) :=
  (hH.of_measure_le_smul (by simp) (map_volume_restrict_le hg)).comp_of_map
    f.continuous.measurable.aemeasurable

def bilipPull (hg : LipschitzOnWith K f.symm (f '' Ω)) (v : L2 (f '' Ω)) : L2 Ω :=
  (memLp_comp_bilip hg (Lp.memLp v)).toLp _

theorem bilipPull_ae (hg : LipschitzOnWith K f.symm (f '' Ω)) (v : L2 (f '' Ω)) :
    (bilipPull hg v : ℂ → ℂ) =ᵐ[volume.restrict Ω] fun x => v (f x) :=
  (memLp_comp_bilip hg (Lp.memLp v)).coeFn_toLp

end PolyaNeumann

end
