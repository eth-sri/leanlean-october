module

public import DedekindZetaZeroFree.Adeles.Quotients.Sobolev.CompactWeightedL2Transport
public import DedekindZetaZeroFree.Analysis.Sobolev.Approximation.CompactInteriorH1Density

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPCompactInteriorH1

open MeasureTheory Filter Topology
open scoped Convolution

section Helpers

 section

variable {n r : ℕ} (f : Lp (V r) 2 (volume : Measure (E n)))

def translateL2V (t : E n) :
    Lp (V r) 2 (volume : Measure (E n)) :=
  Lp.compMeasurePreserving (fun x => x - t) (measurePreserving_sub_right volume t) f

private theorem translateL2V_continuous : Continuous (translateL2V f) := by
  let g : E n → C(E n, E n) := fun t => ⟨fun x => x - t, by fun_prop⟩
  have hg : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : E n × E n => p.2 - p.1)
    fun_prop
  exact continuous_const.compMeasurePreservingLp hg
    (fun t => measurePreserving_sub_right volume t) (by norm_num)

private theorem translateL2V_zero : translateL2V f 0 = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right volume (0 : E n))]
    with x hx
  simpa [translateL2V] using hx

end

private theorem averaged_translateL2V_tendsto {n r : ℕ}
    (f : Lp (V r) 2 (volume : Measure (E n)))
    (φ : ℕ → ContDiffBump (0 : E n))
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ t, (φ m).normed volume t • translateL2V f t) atTop (𝓝 f) := by
  simpa [convolution_def, ContinuousLinearMap.lsmul_apply, translateL2V_zero] using (ContDiffBump.convolution_tendsto_right_of_continuous
     hφ
    ((translateL2V_continuous f).comp continuous_neg) (0 : E n))

variable {n r : ℕ}

private theorem averaged_translateL2V_ae (F : E n → V r)
    (hF : MemLp F 2 volume) (hF1 : Integrable F volume)
    (φ : ContDiffBump (0 : E n)) :
    (∫ t, φ.normed volume t • translateL2V (hF.toLp F) t) =ᵐ[volume]
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F) := by
  let f := hF.toLp F
  let a : Lp (V r) 2 (volume : Measure (E n)) :=
    ∫ t, φ.normed volume t • translateL2V f t
  let c := φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F
  have hc : Continuous c := φ.hasCompactSupport_normed.continuous_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (φ.contDiff_normed (n := (⊤ : ℕ∞))).continuous
    hF1.locallyIntegrable
  apply ae_eq_of_integral_contDiff_smul_eq
    (Lp.memLp a |>.locallyIntegrable (by norm_num)) hc.locallyIntegrable
  intro q hq hqc
  have hqLp : MemLp q 2 (volume : Measure (E n)) :=
    hq.continuous.memLp_of_hasCompactSupport hqc
  let Q := hqLp.toLp q
  let L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] V r →L[ℝ] V r).lpPairing
    (volume : Measure (E n)) 2 2
  have hpair (v : Lp (V r) 2 (volume : Measure (E n))) : L Q v = ∫ x, q x • v x := by
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hqLp.coeFn_toLp] with x hx
    simp [Q, hx]
  have hbase := (φ.integrable_normed (μ := (volume : Measure (E n)))).convolution_integrand
    (ContinuousLinearMap.lsmul ℝ ℝ) hF1
  obtain ⟨C, hC⟩ := (hqc.isCompact_range hq.continuous).isBounded.exists_norm_le
  have hC' (x : E n) : ‖q x‖ ≤ C := hC _ (Set.mem_range_self x)
  have htriple : Integrable (fun p : E n × E n =>
      q p.1 • (φ.normed volume p.2 • F (p.1 - p.2))) (volume.prod volume) := by
    exact hbase.bdd_smul C (hq.continuous.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall (fun p => hC' p.1))
  have ht (t : E n) : L Q (translateL2V f t) = ∫ x, q x • F (x - t) := by
    rw [hpair]
    apply integral_congr_ae
    have he := Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right volume t)
    have hf := (measurePreserving_sub_right volume t).quasiMeasurePreserving.ae (hF.coeFn_toLp)
    filter_upwards [he, hf] with x hx hxg
    simp only [Function.comp_apply] at hx
    change q x • (Lp.compMeasurePreserving (fun x => x - t) _ f) x = _
    rw [hx]
    change q x • (hF.toLp F) (x - t) = _
    rw [hxg]
  rw [← hpair a]
  dsimp only [a]
  rw [← ContinuousLinearMap.integral_comp_comm (L Q) (by
    apply Continuous.integrable_of_hasCompactSupport
    · exact (φ.contDiff_normed (n := (⊤ : ℕ∞))).continuous.smul (translateL2V_continuous f)
    · exact φ.hasCompactSupport_normed.smul_right)]
  simp_rw [map_smul, ht]
  simp_rw [← integral_smul]
  have hswap : Integrable (Function.uncurry fun t x =>
      φ.normed volume t • q x • F (x - t)) (volume.prod volume) := by
    have heq : (Function.uncurry fun t x => φ.normed volume t • q x • F (x - t))
        = fun p : E n × E n => q p.2 • (φ.normed volume p.1 • F (p.2 - p.1)) := by
      funext p
      exact smul_comm (φ.normed volume p.1) (q p.2) (F (p.2 - p.1))
    rw [heq]
    exact htriple.swap
  rw [integral_integral_swap hswap]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [c, convolution_def, ContinuousLinearMap.lsmul_apply]
    rw [← integral_smul]
    apply integral_congr_ae
    exact Eventually.of_forall fun t => smul_comm _ _ _

private theorem integrable_of_memLp_two_of_support_subset_compact
    {C : Set (E n)} (hC : IsCompact C) {F : E n → V r}
    (hF : MemLp F 2 volume) (hFC : ∀ x, x ∉ C → F x = 0) : Integrable F volume := by
  haveI : IsFiniteMeasure (volume.restrict C) := by
    rw [isFiniteMeasure_restrict]; exact hC.measure_lt_top.ne
  exact (integrableOn_iff_integrable_of_support_subset (fun x hx => by
    by_contra h
    exact hx (hFC x h))).mp
    (memLp_one_iff_integrable.mp ((hF.mono_measure Measure.restrict_le_self).mono_exponent (by norm_num)))

private theorem l2Norm_eq_norm_toLp {g : E n → V r} (hg : MemLp g 2 volume) :
    l2Norm volume g hg = ‖hg.toLp g‖ := by
  have hsqrt : Real.sqrt (∫ x, ‖g x‖ ^ (2 : ℕ) ∂volume)
      = Real.sqrt (∫ x, ‖g x‖ ^ (2 : ℝ) ∂volume) := by
    congr 1
    apply integral_congr_ae
    refine Eventually.of_forall fun x => ?_
    simp
  rw [l2Norm, Lp.norm_toLp, toReal_eLpNorm, (lpNorm_eq_integral_norm_rpow_toReal
    (by norm_num) (by norm_num) hg.aestronglyMeasurable)]
  rw [show (2 : ENNReal).toReal = 2 by norm_num]
  rw [show ((2 : ℝ)⁻¹) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  exact hsqrt

private theorem l2Norm_congr {g g' : E n → V r} (hg : MemLp g 2 volume)
    (hg' : MemLp g' 2 volume) (h : g =ᵐ[volume] g') :
    l2Norm volume g hg = l2Norm volume g' hg' := by
  rw [l2Norm, l2Norm]
  congr 1
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

end Helpers

def mollifyVector {n r : ℕ} (φ : ContDiffBump (0 : E n))
    (F : E n → V r) : E n → V r :=
  φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F

variable {n r : ℕ} (hn : 0 < n) (hr : 0 < r) (C : Set (E n)) (hC : IsCompact C) (F : E n → V r)
    (hF : MemLp F 2 volume) (hFC : ∀ x, x ∉ C → F x = 0)

include hn hr hC hF hFC in
theorem mollification_memLp
    (φ : ContDiffBump (0 : E n)) :
    MemLp (mollifyVector φ F) 2 volume := by
  exact MemLp.ae_eq (averaged_translateL2V_ae F hF (integrable_of_memLp_two_of_support_subset_compact hC hF hFC) φ) (Lp.memLp (∫ t, φ.normed volume t • translateL2V (hF.toLp F) t))

theorem mollification_l2_tendsto
    (φ : ℕ → ContDiffBump (0 : E n))
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0)) :
    Tendsto (fun m => l2Norm volume (mollifyVector (φ m) F - F)
      ((mollification_memLp hn hr C hC F hF hFC (φ m)).sub hF))
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun m =>
      ‖(∫ t, (φ m).normed volume t • translateL2V (hF.toLp F) t) - hF.toLp F‖)
      atTop (𝓝 0) := by
    have h : Tendsto (fun m =>
        (∫ t, (φ m).normed volume t • translateL2V (hF.toLp F) t) - hF.toLp F)
        atTop (𝓝 (hF.toLp F - hF.toLp F)) :=
      (averaged_translateL2V_tendsto (hF.toLp F) φ hφ).sub tendsto_const_nhds
    simpa using h.norm
  refine hlim.congr (fun m => ?_)
  have hae' : (mollifyVector (φ m) F - F) =ᵐ[volume]
      (⇑((∫ t, (φ m).normed volume t • translateL2V (hF.toLp F) t) - hF.toLp F)) := by
    filter_upwards [(averaged_translateL2V_ae F hF (integrable_of_memLp_two_of_support_subset_compact hC hF hFC) (φ m)), Lp.coeFn_sub (∫ t, (φ m).normed volume t • translateL2V (hF.toLp F) t) (hF.toLp F),
      hF.coeFn_toLp] with x hx hsub hFc
    show mollifyVector (φ m) F x - F x =
      (⇑((∫ t, (φ m).normed volume t • translateL2V (hF.toLp F) t) - hF.toLp F)) x
    rw [hsub, Pi.sub_apply, hx, hFc]
    simp [mollifyVector]
  rw [l2Norm_congr ((mollification_memLp hn hr C hC F hF hFC (φ m)).sub hF)
      (Lp.memLp ((∫ t, (φ m).normed volume t • translateL2V (hF.toLp F) t) - hF.toLp F)) hae']
  rw [l2Norm_eq_norm_toLp, Lp.toLp_coeFn]

end DedekindZetaZeroFree.KPCompactInteriorH1

end
