module

public import RequestProject.MollifierEstimate
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# `L²` convergence of mollifications

For a normalized bump function `ρ = φ.normed volume` and `H ∈ L²(ℂ)`:

* `eLpNorm_mollify_le`: `‖ρ ⋆ H‖₂ ≤ ‖H‖₂` (Young's inequality for a probability kernel);
* `tendsto_mollify_L2`: `ρ_k ⋆ H → H` in `L²(ℂ)` when the radii of the bumps tend to `0`.
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal

noncomputable section

namespace PolyaNeumann

variable {H : ℂ → ℂ}

lemma mollify_apply ρ H x :
    mollify ρ H x = ∫ t, ρ t • H (x - t) := by
  simp [mollify, convolution_def]
/-- Jensen's inequality for a probability density: `(∫ ρ h)² ≤ ∫ ρ h²`. -/
lemma lintegral_mul_sq_le {ρ : ℂ → ℝ≥0∞}  (hρ : AEMeasurable ρ volume)
    (hh : AEMeasurable h volume) (h1 : ∫⁻ t, ρ t = 1) :
    (∫⁻ t, ρ t * h t) ^ 2 ≤ ∫⁻ t, ρ t * h t ^ 2 := by
  have key := ENNReal.lintegral_mul_le_Lp_mul_Lq volume (show (2:ℝ).HolderConjugate 2 by
    rw [Real.holderConjugate_iff]; norm_num) (hρ.pow_const (1/2 : ℝ))
    ((hρ.pow_const (1/2 : ℝ)).mul hh)
  have e2 : ∀ t, (ρ t ^ (1/2 : ℝ)) ^ (2:ℝ) = ρ t := by
    intro t; rw [← ENNReal.rpow_mul]; norm_num
  simp only [Pi.mul_apply, show ∀ t, ρ t ^ (1/2 : ℝ) * (ρ t ^ (1/2 : ℝ) * h t) = ρ t * h t by
    intro t
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num, e2, show ∀ t, (ρ t ^ (1/2 : ℝ) * h t) ^ (2:ℝ) = ρ t * h t ^ 2 by
    intro t
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), e2]
    norm_cast, h1, ENNReal.one_rpow, one_mul] at key
  calc _ ≤ ((∫⁻ t, ρ t * h t ^ 2) ^ (1/2:ℝ)) ^ 2 := by gcongr
    _ = _ := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

/-- Young's inequality for a normalized bump: `‖ρ ⋆ H‖₂ ≤ ‖H‖₂`. -/
lemma eLpNorm_mollify_le (φ : ContDiffBump 0) 
    (hH : AEStronglyMeasurable H volume) :
    eLpNorm (mollify (φ.normed volume) H) 2 volume ≤ eLpNorm H 2 volume := by
  set ρ : ℂ → ℝ≥0∞ := fun t => ENNReal.ofReal (φ.normed volume t)
  have hρm : Measurable ρ := ENNReal.measurable_ofReal.comp φ.continuous_normed.measurable
  have hρ1 : ∫⁻ t, ρ t = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal φ.integrable_normed
      (Eventually.of_forall φ.nonneg_normed), φ.integral_normed, ENNReal.ofReal_one]
  have hHm := hH.enorm
  have key : ∫⁻ x, ‖mollify (φ.normed volume) H x‖ₑ ^ 2 ≤ ∫⁻ x, ‖H x‖ₑ ^ 2 := by
    calc _
        ≤ ∫⁻ x, (∫⁻ t, ρ t * ‖H (x - t)‖ₑ) ^ 2 := by
          gcongr with x; exact (by
            rw [mollify_apply]
            refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
            refine lintegral_congr fun t => ?_
            rw [enorm_smul, Real.enorm_of_nonneg (φ.nonneg_normed t)])
      _ ≤ ∫⁻ x, ∫⁻ t, ρ t * ‖H (x - t)‖ₑ ^ 2 := by
          gcongr with x
          exact lintegral_mul_sq_le hρm.aemeasurable
            (hHm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left_of_right_invariant volume x)) hρ1
      _ = _ := by
          refine lintegral_lintegral_swap ?_
          exact hρm.aemeasurable.comp_snd.mul ((hHm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_of_right_invariant volume volume)).pow_const 2)
      _ = ∫⁻ t, ρ t * ∫⁻ x, ‖H x‖ₑ ^ 2 := by
          refine lintegral_congr fun t => ?_
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_sub_right_eq_self (fun x => ‖H x‖ₑ ^ 2) t]
      _ = ∫⁻ x, ‖H x‖ₑ ^ 2 := by
          rw [lintegral_mul_const _ hρm, hρ1, one_mul]
  have hmm : AEStronglyMeasurable (mollify (φ.normed volume) H) volume :=
    AEStronglyMeasurable.convolution (L := ContinuousLinearMap.lsmul ℝ ℝ)
      φ.continuous_normed.aestronglyMeasurable hH
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hmm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hH]
  simp
  gcongr
lemma integrable_mollify_integrand (φ : ContDiffBump 0) 
    (h : LocallyIntegrable H volume) x :
    Integrable (fun t => (φ.normed volume t) • H (x - t)) volume :=
  HasCompactSupport.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    φ.hasCompactSupport_normed φ.continuous_normed h x

lemma mollify_sub (φ : ContDiffBump 0)  (h1 : LocallyIntegrable H₁ volume)
    (h2 : LocallyIntegrable H₂ volume) :
    mollify (φ.normed volume) (H₁ - H₂) =
      mollify (φ.normed volume) H₁ - mollify (φ.normed volume) H₂ := by
  ext x
  simp [mollify_apply, smul_sub]
  exact integral_sub (integrable_mollify_integrand φ h1 x) (integrable_mollify_integrand φ h2 x)

lemma mollify_eq_zero_of_notMem (φ : ContDiffBump 0)  
    (hx : x ∉ cthickening φ.rOut (tsupport F)) : mollify (φ.normed volume) F x = 0 := by
  rw [mollify_apply]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ Function.support (φ.normed volume)
  · rw [φ.support_normed_eq, mem_ball_zero_iff] at ht
    simp [image_eq_zero_of_notMem_tsupport (by
      intro h
      apply hx
      refine mem_cthickening_of_dist_le x (x - t) _ _ h ?_
      simp [ht.le])]
  · simp [Function.notMem_support.mp ht]

lemma tendsto_zero_of_eventually_le_mul {f : ℕ → ℝ≥0∞}  (hC : C ≠ ⊤)
    (h : ∀ ε > 0, ∀ᶠ k in atTop, f k ≤ ENNReal.ofReal ε * C) : Tendsto f atTop (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun e he => ?_
  obtain ⟨ε, hε1, hε2⟩ := (((show Tendsto (fun ε => ENNReal.ofReal ε * C) (𝓝[>] 0) (𝓝 0) by
    simpa using (ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0))) (Or.inr hC))).eventually (eventually_le_nhds he.bot_lt)).and
    self_mem_nhdsWithin).exists
  filter_upwards [h ε hε2] with k hk using hk.trans hε1

/-- Mollifications of a continuous compactly supported function converge in `L²`. -/
lemma tendsto_mollify_L2_of_continuous {φ : ℕ → ContDiffBump 0}
    (hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0)) {F : ℂ → ℂ} (hF : Continuous F)
    (hFs : HasCompactSupport F) :
    Tendsto (fun k => eLpNorm (mollify ((φ k).normed volume) F - F) 2 volume) atTop (𝓝 0) := by
  set S := cthickening 1 (tsupport F)
  have hS : IsCompact S := hFs.isCompact.cthickening
  set C := volume S ^ (1 / (2 : ℝ≥0∞).toReal)
  exact tendsto_zero_of_eventually_le_mul (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hS.measure_lt_top.ne : C ≠ ⊤) (by
    intro ε hε
    obtain ⟨δ, hδ, hδF⟩ := Metric.uniformContinuous_iff.mp (hFs.uniformContinuous_of_continuous hF) ε hε
    filter_upwards [hφ.eventually (gt_mem_nhds (lt_min hδ one_pos))] with k hk
    refine eLpNorm_sub_le_of_dist_bdd volume (by norm_num) hS.isClosed.measurableSet.nullMeasurableSet hε.le
      ?_ (fun x => ?_) (fun x hx => ?_) (fun x hx => ?_)
    · exact ((HasCompactSupport.continuous_convolution_left _ (φ k).hasCompactSupport_normed (φ k).continuous_normed hF.locallyIntegrable).sub hF).aestronglyMeasurable
    · refine ContDiffBump.dist_normed_convolution_le hF.aestronglyMeasurable fun y hy => ?_
      exact (hδF (lt_of_lt_of_le (mem_ball.mp hy) ((min_le_left _ _).trans' hk.le))).le
    · by_contra hxS
      refine hx (mollify_eq_zero_of_notMem _ fun h => hxS ?_)
      exact cthickening_mono ((lt_min_iff.mp hk).2.le) _ h
    · exact self_subset_cthickening _ (subset_tsupport F hx))
/-- Mollifications of an `L²` function converge to it in `L²`. -/
theorem tendsto_mollify_L2 {φ : ℕ → ContDiffBump 0}
    (hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0))  (hH : MemLp H 2 volume) :
    Tendsto (fun k => eLpNorm (mollify ((φ k).normed volume) H - H) 2 volume) atTop (𝓝 0) := by
  refine tendsto_zero_of_eventually_le_mul (C := 3) (by norm_num) fun ε hε => ?_
  obtain ⟨G, hGs, hHG, hG, hGL⟩ := hH.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num)
    (ENNReal.ofReal_pos.mpr hε).ne'
  filter_upwards [(tendsto_mollify_L2_of_continuous hφ hG hGs).eventually
    (eventually_le_nhds (ENNReal.ofReal_pos.mpr hε))] with k hk
  rw [show mollify ((φ k).normed volume) H - H = mollify ((φ k).normed volume) (H - G) + (mollify ((φ k).normed volume) G - G) + (G - H) by
    rw [mollify_sub _ (hH.locallyIntegrable (by norm_num)) (hGL.locallyIntegrable (by norm_num))]; abel]
  calc _
      ≤ eLpNorm (mollify ((φ k).normed volume) (H - G)) 2 volume
        + eLpNorm (mollify ((φ k).normed volume) G - G) 2 volume + eLpNorm (G - H) 2 volume := by
        refine (eLpNorm_add_le (by norm_num)).trans ?_
        gcongr
        exact eLpNorm_add_le (by norm_num)
    _ ≤ ENNReal.ofReal ε + ENNReal.ofReal ε + ENNReal.ofReal ε := by
        gcongr
        · exact (eLpNorm_mollify_le _ (hH.aestronglyMeasurable.sub hG.aestronglyMeasurable)).trans hHG
        · rw [eLpNorm_sub_comm]; exact hHG
    _ = _ := by ring
end PolyaNeumann

end
