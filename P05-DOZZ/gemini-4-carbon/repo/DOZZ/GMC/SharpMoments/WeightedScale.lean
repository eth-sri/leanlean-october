/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.WeightedGmcBallMoment
public import DOZZ.GMC.SharpMoments.OpenSetScale

/-! # Exact scaling of singular weighted GMC masses -/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

private def wsProfile (β : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (min (n : ℝ≥0∞) (ENNReal.ofReal t ^ β)).toReal

private lemma wsProfile_ne_top (β : ℝ) (n : ℕ) (t : ℝ) :
    min (n : ℝ≥0∞) (ENNReal.ofReal t ^ β) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_left _ _)

private def wsTest (β R : ℝ) (n : ℕ) : BoundedContinuousFunction ℂ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => wsProfile β n ‖x‖ * openSetApproxFun (Metric.ball 0 R) n x)
    (((ENNReal.continuousOn_toReal.comp_continuous
      (continuous_const.min (ENNReal.continuous_rpow_const.comp ENNReal.continuous_ofReal))
      (wsProfile_ne_top β n)).comp continuous_norm).mul (openSetApproxFun_continuous _ n))
    n fun x => by
      have hnn : 0 ≤ wsProfile β n ‖x‖ * openSetApproxFun (Metric.ball 0 R) n x :=
        mul_nonneg ENNReal.toReal_nonneg (openSetApproxFun_bounds _ n x).1
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact (mul_le_of_le_one_right ENNReal.toReal_nonneg (openSetApproxFun_bounds _ n x).2).trans
        ((ENNReal.toReal_mono (ENNReal.natCast_ne_top n) (min_le_left _ _)).trans_eq (ENNReal.toReal_natCast n))

private def wsScaled (β c R : ℝ) (n : ℕ) : BoundedContinuousFunction ℂ ℝ :=
  (c ^ β) • (wsTest β R n).compContinuous ⟨fun x : ℂ => c⁻¹ • x, by fun_prop⟩

@[simp] private lemma wsTest_apply (β R : ℝ) (n : ℕ) (x : ℂ) :
    wsTest β R n x = wsProfile β n ‖x‖ * openSetApproxFun (Metric.ball 0 R) n x := rfl

@[simp] private lemma wsScaled_apply (β c R : ℝ) (n : ℕ) (x : ℂ) :
    wsScaled β c R n x = c ^ β * wsTest β R n (c⁻¹ • x) := rfl






/-- Exact scaling of the `p`th moment of the singular weighted mass about the center `0`. -/
theorem gmc_weighted_ball_moment_scale
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (α : ℝ)
    {c R : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hR : 0 < R) (hRsmall : R < 1) (p : ℝ) :
    weightedGmcBallMoment P M γ α 0 (c * R) p =
      ENNReal.ofReal (c ^ ((2 - γ * α) * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2)) *
        weightedGmcBallMoment P M γ α 0 R p := by
  have ws_tsupport_test (β R : ℝ) (n : ℕ) : tsupport (wsTest β R n : ℂ → ℝ) ⊆ Metric.closedBall 0 R := 
    closure_minimal (fun x hx => by
      by_contra hxc
      exact hx (by simp [openSetApproxFun_eq_zero_of_notMem
        (fun hb => hxc (Metric.ball_subset_closedBall hb)) n])) Metric.isClosed_closedBall
  have ws_iSup_integral {μ : Measure ℂ} [IsFiniteMeasure μ] (h : ℕ → BoundedContinuousFunction ℂ ℝ) (hnn : ∀ n x, 0 ≤ h n x) (hmono : ∀ x, Monotone fun n => h n x) {F : ℂ → ℝ≥0∞} (hlim : ∀ x, Tendsto (fun n => ENNReal.ofReal (h n x)) atTop (𝓝 (F x))) : ⨆ n, ENNReal.ofReal (∫ x, h n x ∂μ) = ∫⁻ x, F x ∂μ := by
    simp_rw [ofReal_integral_eq_lintegral_ofReal ((h _).integrable μ) (ae_of_all _ (hnn _))]
    exact tendsto_nhds_unique
      (tendsto_atTop_iSup fun _ _ hmn => lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hmono x hmn))
      (lintegral_tendsto_of_tendsto_of_monotone
        (fun n => (ENNReal.measurable_ofReal.comp (h n).continuous.measurable).aemeasurable)
        (ae_of_all _ fun x _ _ hmn => ENNReal.ofReal_le_ofReal (hmono x hmn)) (ae_of_all _ hlim))
  have wsTest_tendsto (β R : ℝ) (x : ℂ) : Tendsto (fun n : ℕ => ENNReal.ofReal (wsTest β R n x)) atTop
        (𝓝 ((Metric.ball (0 : ℂ) R).indicator (fun z => ENNReal.ofReal ‖z‖ ^ β) x)) := by
    by_cases hx : x ∈ Metric.ball (0 : ℂ) R
    · rw [Set.indicator_of_mem hx]
      have hev : ∀ᶠ n : ℕ in atTop, openSetApproxFun (Metric.ball 0 R) n x = 1 :=
        ((tendsto_natCast_atTop_atTop.atTop_mul_const
          ((Metric.isOpen_ball.isClosed_compl.notMem_iff_infDist_pos
            (openSetScale_compl_nonempty Metric.ball_subset_closedBall)).1
            (by simpa using hx))).eventually_ge_atTop 1).mono fun n hn => by simp [openSetApproxFun, hn]
      have hp : Tendsto (fun n : ℕ => ENNReal.ofReal (wsProfile β n ‖x‖)) atTop (𝓝 (ENNReal.ofReal ‖x‖ ^ β)) := by
        simp_rw [wsProfile, ENNReal.ofReal_toReal (wsProfile_ne_top β _ _)]
        simpa using ENNReal.tendsto_nat_nhds_top.min (tendsto_const_nhds (x := ENNReal.ofReal ‖x‖ ^ β))
      exact hp.congr' (hev.mono fun n hn => by simp [hn])
    · rw [Set.indicator_of_notMem hx]
      exact tendsto_const_nhds.congr' (Eventually.of_forall fun n => by
        simp [openSetApproxFun_eq_zero_of_notMem hx n])
  have wsTest_mono (β R : ℝ) (x : ℂ) : Monotone fun n => wsTest β R n x := 
    fun m n h => mul_le_mul
      (ENNReal.toReal_mono (wsProfile_ne_top β n _) (min_le_min_right _ (Nat.cast_le.2 h)))
      (min_le_min_left 1 (mul_le_mul_of_nonneg_right (Nat.cast_le.2 h) Metric.infDist_nonneg))
      (openSetApproxFun_bounds _ m x).1 ENNReal.toReal_nonneg
  have ws_iSup_test_eq (r : ℝ) (μ : Measure ℂ) [IsFiniteMeasure μ] : ⨆ n, ENNReal.ofReal (∫ x, wsTest (-γ * α) r n x ∂μ) = weightedGmcBallMass γ μ α 0 r := by
    rw [weightedGmcBallMass, ← lintegral_indicator Metric.isOpen_ball.measurableSet]
    simp only [sub_zero, ENNReal.rpow_eq_pow]
    exact ws_iSup_integral _ (fun n x => mul_nonneg ENNReal.toReal_nonneg (openSetApproxFun_bounds _ n x).1)
      (wsTest_mono _ r) (wsTest_tendsto _ r)
  let _ := hX.1
  let G := gaussianReal 0 ⟨-Real.log c, neg_nonneg.2 (Real.log_nonpos hc.le hc1)⟩
  let _ : IsProbabilityMeasure G := instIsProbabilityMeasureGaussianReal 0 _
  let β := -γ * α
  have hcR : c * R ≤ 1 := (mul_le_of_le_one_left hR.le hc1).trans hRsmall.le
  have hsc_nn (n : ℕ) (x : ℂ) : 0 ≤ wsScaled β c R n x :=
    mul_nonneg (Real.rpow_nonneg hc.le β)
      (mul_nonneg ENNReal.toReal_nonneg (openSetApproxFun_bounds _ n _).1)
  have hsc_supp (n : ℕ) : tsupport (wsScaled β c R n : ℂ → ℝ) ⊆ Metric.closedBall 0 (c * R) :=
    closure_minimal (fun x hx => by
      by_contra hxc
      have hnot : c⁻¹ • x ∉ Metric.ball (0 : ℂ) R := fun hm => hxc (Metric.ball_subset_closedBall (by
        simp only [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hc.le)] at hm ⊢
        exact (inv_mul_lt_iff₀ hc).1 hm))
      exact hx (by simp only [wsScaled_apply, wsTest_apply, openSetApproxFun_eq_zero_of_notMem hnot n, mul_zero]))
      Metric.isClosed_closedBall
  have hint_ae {r : ℝ} (hr : r ≤ 1) (f : BoundedContinuousFunction ℂ ℝ)
      (hf : tsupport (f : ℂ → ℝ) ⊆ Metric.closedBall 0 r) :
      AEMeasurable (fun ω => ∫ x, f x ∂M ω) P :=
    openSetScale_test_integral_aemeasurable P X hX γ M hM (Metric.closedBall 0 r)
      Metric.isClosed_closedBall.measurableSet (fun x hx => (by simpa using hx : ‖x‖ ≤ r).trans hr) f
      (boundedContinuousFunction_eq_zero_off_tsupport_subset f _ hf)
  have hmass_ae {r : ℝ} (hr : r ≤ 1) : AEMeasurable (fun ω => weightedGmcBallMass γ (M ω) α 0 r) P := by
    have heq : (fun ω => weightedGmcBallMass γ (M ω) α 0 r) =
        fun ω => ⨆ n, ENNReal.ofReal (∫ x, wsTest β r n x ∂M ω) :=
      funext fun ω => by let _ := hM.1 ω; exact (ws_iSup_test_eq r (M ω)).symm
    rw [heq]
    exact AEMeasurable.iSup fun n => ENNReal.measurable_ofReal.comp_aemeasurable
      (hint_ae hr _ (ws_tsupport_test β r n))
  -- Law of scaled mass via monotone supremum
  let s (w : ℝ) := c ^ 2 * Real.exp (γ * w - γ ^ 2 / 2 * (-Real.log c))
  have hs_m : Measurable s := by dsimp [s]; fun_prop
  have hTsmall : ‖(0 : ℂ)‖ + c * R < 1 := by simp [lt_of_le_of_lt (mul_le_of_le_one_left hR.le hc1) hRsmall]
  have hlaw_n (n : ℕ) :
      Measure.map (fun ω => ENNReal.ofReal (∫ x, wsScaled β c R n x ∂M ω)) P =
      Measure.map (fun q : Ω × ℝ => ENNReal.ofReal (s q.2) *
        (ENNReal.ofReal (c ^ β) * ENNReal.ofReal (∫ x, wsTest β R n x ∂M q.1))) (P.prod G) := by
    have hvec := gmc_affine_test_vector_law P X hX γ M hM (a := 0) hc hc1 hR hRsmall hTsmall
      (fun _ : Fin 1 => wsScaled β c R n) (fun _ => hsc_nn n) (fun _ => hsc_supp n)
    have hcomp (μ : Measure ℂ) : ∫ x, wsScaled β c R n (0 + c • x) ∂μ = c ^ β * ∫ x, wsTest β R n x ∂μ := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall fun x => by simp [hc.ne'])
    have hΦ : Measurable fun v : Fin 1 → ℝ => ENNReal.ofReal (v 0) :=
      ENNReal.measurable_ofReal.comp (measurable_pi_apply 0)
    have hx := hint_ae hcR _ (hsc_supp n)
    have hy : AEMeasurable (fun q : Ω × ℝ => s q.2 * (c ^ β * ∫ x, wsTest β R n x ∂M q.1)) (P.prod G) :=
      (hs_m.comp measurable_snd).aemeasurable.mul
        (aemeasurable_const.mul ((hint_ae hRsmall.le _ (ws_tsupport_test β R n)).comp_fst))
    have h1 := (AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable (aemeasurable_pi_iff.2 fun _ => hx)).symm.trans
      ((congrArg (Measure.map _) (by simpa only [hcomp] using hvec)).trans
        (AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable (aemeasurable_pi_iff.2 fun _ => hy)))
    refine h1.trans (congrArg (fun F => Measure.map F (P.prod G)) (funext fun q => ?_))
    dsimp only [Function.comp_apply]
    rw [ENNReal.ofReal_mul (by dsimp [s]; positivity), ENNReal.ofReal_mul (Real.rpow_nonneg hc.le β)]
  have hsc_iSup (μ : Measure ℂ) [IsFiniteMeasure μ] :
      ⨆ n, ENNReal.ofReal (∫ x, wsScaled β c R n x ∂μ) = weightedGmcBallMass γ μ α 0 (c * R) := by
    rw [weightedGmcBallMass, ← lintegral_indicator Metric.isOpen_ball.measurableSet]
    simp only [sub_zero, ENNReal.rpow_eq_pow]
    refine ws_iSup_integral _ hsc_nn
      (fun x _ _ h => mul_le_mul_of_nonneg_left (wsTest_mono β R _ h) (Real.rpow_nonneg hc.le β)) fun x => ?_
    have ht := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (c ^ β))
      (wsTest_tendsto β R (c⁻¹ • x)) (Or.inr ENNReal.ofReal_ne_top)
    have heq_fn : (fun n : ℕ => ENNReal.ofReal (wsScaled β c R n x)) =
        fun n => ENNReal.ofReal (c ^ β) * ENNReal.ofReal (wsTest β R n (c⁻¹ • x)) :=
      funext fun n => by simp [ENNReal.ofReal_mul (Real.rpow_nonneg hc.le β)]
    rw [heq_fn]
    convert ht using 2
    have hm_iff : c⁻¹ • x ∈ Metric.ball (0 : ℂ) R ↔ x ∈ Metric.ball (0 : ℂ) (c * R) := by
      simp only [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hc.le)]
      exact inv_mul_lt_iff₀ hc
    by_cases hx : x ∈ Metric.ball (0 : ℂ) (c * R)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hm_iff.2 hx)]
      have hc' := inv_nonneg.2 hc.le
      rw [norm_smul, Real.norm_of_nonneg hc', ENNReal.ofReal_mul hc',
        ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
        ENNReal.ofReal_rpow_of_pos (inv_pos.2 hc), ← mul_assoc,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le β), ← Real.mul_rpow hc.le hc',
        mul_inv_cancel₀ hc.ne', Real.one_rpow, ENNReal.ofReal_one, one_mul]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt hm_iff.1 hx), mul_zero]
  have hlaw_mass :
      Measure.map (fun ω => weightedGmcBallMass γ (M ω) α 0 (c * R)) P =
      Measure.map (fun q : Ω × ℝ => ENNReal.ofReal (s q.2) *
        (ENNReal.ofReal (c ^ β) * weightedGmcBallMass γ (M q.1) α 0 R)) (P.prod G) := by
    let aF (n : ℕ) (ω : Ω) := ENNReal.ofReal (∫ x, wsScaled β c R n x ∂M ω)
    let bF (n : ℕ) (q : Ω × ℝ) := ENNReal.ofReal (s q.2) *
      (ENNReal.ofReal (c ^ β) * ENNReal.ofReal (∫ x, wsTest β R n x ∂M q.1))
    have ha_ae (n : ℕ) : AEMeasurable (aF n) P :=
      ENNReal.measurable_ofReal.comp_aemeasurable (hint_ae hcR _ (hsc_supp n))
    have hb_ae (n : ℕ) : AEMeasurable (bF n) (P.prod G) :=
      (ENNReal.measurable_ofReal.comp (hs_m.comp measurable_snd)).aemeasurable.mul
        (aemeasurable_const.mul ((ENNReal.measurable_ofReal.comp_aemeasurable
          (hint_ae hRsmall.le _ (ws_tsupport_test β R n))).comp_fst))
    have ham (ω : Ω) : Monotone fun n => aF n ω := fun _ _ h => by
      let _ := hM.1 ω
      exact ENNReal.ofReal_le_ofReal (integral_mono ((wsScaled β c R _).integrable _)
        ((wsScaled β c R _).integrable _) fun x =>
          mul_le_mul_of_nonneg_left (wsTest_mono β R _ h) (Real.rpow_nonneg hc.le β))
    have hbm (q : Ω × ℝ) : Monotone fun n => bF n q := fun _ _ h => by
      let _ := hM.1 q.1
      exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal
        (integral_mono ((wsTest β R _).integrable _) ((wsTest β R _).integrable _)
          fun x => wsTest_mono β R x h)))
    have hsup : Measure.map (fun ω => ⨆ n, aF n ω) P = Measure.map (fun q => ⨆ n, bF n q) (P.prod G) := by
      refine Measure.ext_of_Iic _ _ fun t => ?_
      rw [← compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi, prob_compl_eq_one_sub measurableSet_Ioi]
      congr 1
      have hma : Monotone fun n => aF n ⁻¹' Ioi t := fun _ _ h _ hz => lt_of_lt_of_le hz (ham _ h)
      have hmb : Monotone fun n => bF n ⁻¹' Ioi t := fun _ _ h _ hz => lt_of_lt_of_le hz (hbm _ h)
      rw [Measure.map_apply_of_aemeasurable (AEMeasurable.iSup ha_ae) measurableSet_Ioi,
        Measure.map_apply_of_aemeasurable (AEMeasurable.iSup hb_ae) measurableSet_Ioi,
        show (fun b => ⨆ i, aF i b) ⁻¹' Ioi t = ⋃ n, aF n ⁻¹' Ioi t by ext; simp [lt_iSup_iff],
        show (fun b => ⨆ i, bF i b) ⁻¹' Ioi t = ⋃ n, bF n ⁻¹' Ioi t by ext; simp [lt_iSup_iff],
        hma.measure_iUnion, hmb.measure_iUnion]
      refine iSup_congr fun n => ?_
      rw [← Measure.map_apply_of_aemeasurable (ha_ae n) measurableSet_Ioi,
        ← Measure.map_apply_of_aemeasurable (hb_ae n) measurableSet_Ioi, hlaw_n n]
    have hA_eq : (fun ω => ⨆ n, aF n ω) = fun ω => weightedGmcBallMass γ (M ω) α 0 (c * R) :=
      funext fun ω => by let _ := hM.1 ω; exact hsc_iSup (M ω)
    have hB_eq : (fun q => ⨆ n, bF n q) = fun q : Ω × ℝ => ENNReal.ofReal (s q.2) *
        (ENNReal.ofReal (c ^ β) * weightedGmcBallMass γ (M q.1) α 0 R) :=
      funext fun q => by
        let _ := hM.1 q.1
        dsimp only [bF, β]
        rw [← ws_iSup_test_eq R (M q.1), ENNReal.mul_iSup, ENNReal.mul_iSup]
    rwa [hA_eq, hB_eq] at hsup
  -- Transfer p-th moment
  let A_f (w : ℝ) := ENNReal.ofReal (s w)
  let K := ENNReal.ofReal (c ^ β)
  have hK0 : K ≠ 0 := (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hc β)).ne'
  have hψ : Measurable fun x : ℝ≥0∞ => x ^ p := ENNReal.continuous_rpow_const.measurable
  have hWt := hmass_ae hcR
  have hWR := hmass_ae hRsmall.le
  have hWs : AEMeasurable (fun q : Ω × ℝ => A_f q.2 * (K * weightedGmcBallMass γ (M q.1) α 0 R)) (P.prod G) :=
    ((ENNReal.measurable_ofReal.comp hs_m).comp measurable_snd).aemeasurable.mul
      (aemeasurable_const.mul hWR.comp_fst)
  have hpow_ae : AEMeasurable (fun ω => weightedGmcBallMass γ (M ω) α 0 R ^ p) P := hψ.comp_aemeasurable hWR
  have hgauss := gaussianScaleFactor_rpow_integral γ c p hc hc1
  unfold weightedGmcBallMoment
  simp only [ENNReal.rpow_eq_pow] at hgauss ⊢
  calc ∫⁻ ω, weightedGmcBallMass γ (M ω) α 0 (c * R) ^ p ∂P
    _ = ∫⁻ x, x ^ p ∂Measure.map (fun ω => weightedGmcBallMass γ (M ω) α 0 (c * R)) P :=
        (lintegral_map' hψ.aemeasurable hWt).symm
    _ = ∫⁻ q, (A_f q.2 * (K * weightedGmcBallMass γ (M q.1) α 0 R)) ^ p ∂P.prod G := by
        rw [hlaw_mass]; exact lintegral_map' hψ.aemeasurable hWs
    _ = ∫⁻ q, (K ^ p * weightedGmcBallMass γ (M q.1) α 0 R ^ p) * A_f q.2 ^ p ∂P.prod G := by
        refine lintegral_congr fun q => ?_
        have hA0 : A_f q.2 ≠ 0 := (ENNReal.ofReal_pos.2 (by dsimp [s]; positivity)).ne'
        simp [ENNReal.mul_rpow_eq_ite, hA0, ENNReal.ofReal_ne_top, hK0, K, A_f, mul_comm]
    _ = (K ^ p * ∫⁻ ω, weightedGmcBallMass γ (M ω) α 0 R ^ p ∂P) * ∫⁻ w, A_f w ^ p ∂G := by
        rw [lintegral_prod_mul (f := fun ω => K ^ p * weightedGmcBallMass γ (M ω) α 0 R ^ p)
            (g := fun w => A_f w ^ p) (aemeasurable_const.mul hpow_ae)
            (hψ.comp_aemeasurable (ENNReal.measurable_ofReal.comp hs_m).aemeasurable),
          lintegral_const_mul'' _ hpow_ae]
    _ = _ := by
        dsimp [A_f, s, G, K, β] at hgauss ⊢
        rw [hgauss, mul_right_comm, ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hc _),
          ← Real.rpow_mul hc.le, ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _), ← Real.rpow_add hc]
        congr 2; ring

end DOZZ.Proofs
