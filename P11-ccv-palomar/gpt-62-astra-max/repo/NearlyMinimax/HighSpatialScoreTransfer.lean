module

public import NearlyMinimax.HighPatchProductMeasure
public import NearlyMinimax.HighSelectedScoreEnergy

@[expose] public section

/-! Actual local spatial envelopes transfer through the periodic chart
and the true normalized design likelihood, with source fixed C_sharp.
Both integrability statements are derived from the genuine Q^r envelope. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem high_raw_square_patch_integrable_bound {d k r : ℕ} [NeZero k]
    (hk : 4 ≤ k) {j : HighWindowLabels d k}
    {R : (DesignSample d r) → (TernaryVector r) → ℝ}
    (hR : ∀ y, Measurable (fun x => R x y))
    {H : (DesignSample d r) → ℝ}
    (hH : Integrable H (Measure.pi (fun _ => volume.restrict (spatialPatchBox d))))
    (hH0 : ∀ u, 0 ≤ H u)
    (hdom : ∀ x, (∀ i, x i ∈ highTorusPatch j) →
      selectedRawSquareEnergy R x ≤ H (highPatchProductChart j x)) :
    Integrable (selectedRawSquareEnergy R)
      (Measure.pi (fun _ => (cubeVolume d).restrict (highTorusPatch j))) ∧
    (∫ x, selectedRawSquareEnergy R x
      ∂Measure.pi (fun _ => (cubeVolume d).restrict (highTorusPatch j))) ≤
      ((2 / k) ^ d) ^ r *
        ∫ u, H u ∂Measure.pi (fun _ => volume.restrict (spatialPatchBox d)) := by
  let _ := cubeVolume_isProbability d
  have hrawMeas : Measurable (selectedRawSquareEnergy R) :=
    Finset.measurable_sum _ (fun y _ => (hR y).pow_const 2)
  have hraw0 x : 0 ≤ selectedRawSquareEnergy R x :=
    Finset.sum_nonneg (fun y _ => sq_nonneg _)
  have heval := by have hm := (hH.smul_measure ENNReal.ofReal_ne_top).mono_measure (highPatchProductChart_map_le hk j); exact hm.comp_measurable (highPatchProductChart_measurable j)
  have hmem : ∀ᵐ x ∂Measure.pi (fun _ : Fin r => (cubeVolume d).restrict (highTorusPatch j)),
      ∀ i, x i ∈ highTorusPatch j :=
    ae_all_iff.mpr (fun i => Measure.tendsto_eval_ae_ae.eventually
      (ae_restrict_mem (highTorusPatch_measurableSet ..)))
  have hrawI : Integrable (selectedRawSquareEnergy R)
      (Measure.pi (fun _ => (cubeVolume d).restrict (highTorusPatch j))) := by
    apply heval.mono' hrawMeas.aestronglyMeasurable
    filter_upwards [hmem] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hraw0 x)]
    exact hdom x hx
  refine ⟨hrawI, ?_⟩
  calc
    _ ≤ _ :=
      integral_mono_ae hrawI heval (hmem.mono (fun x hx => hdom x hx))
    _ ≤ _ := by
      simpa using highPatchProductChart_integral_le hk j hH hH0

end NearlyMinimax
