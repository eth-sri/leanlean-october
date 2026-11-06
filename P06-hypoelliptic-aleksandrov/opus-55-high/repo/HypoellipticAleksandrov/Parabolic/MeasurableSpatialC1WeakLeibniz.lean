module

public import HypoellipticAleksandrov.Parabolic.MeasurableSpatialC1RawWeakDerivative
public import HypoellipticAleksandrov.Parabolic.TimeVelocitySmoothCompactPlateau
public import HypoellipticAleksandrov.Parabolic.WeakJetProduct
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesCompactGlobalization
public import HypoellipticAleksandrov.Parabolic.WeakDerivativeSpacetimeMollification
public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifierL2
public import HypoellipticAleksandrov.Analysis.L2ProductConvergence
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import HypoellipticAleksandrov.Parabolic.LocalWeakTimeProduct

/-!
# Weak Leibniz rule for measurable-time, spatially smooth multipliers

This module proves the quantitative weak velocity product rule for bounded
jointly measurable scalar multipliers whose fixed-time spatial slices are
`C¹`.
-/

@[expose] public section


namespace HypoellipticAleksandrov.Parabolic

open Filter Function MeasureTheory Set Topology
open scoped ENNReal Topology
open SpacetimeMollifier




variable {d : ℕ} {U : Set (TimeVelocity d)}


private theorem velocityGradient_eq_zero_of_eq_one_on
     {b : TimeVelocity d → ℝ} {K : Set (TimeVelocity d)}
    {δ : ℝ} (hδ : 0 < δ) (hb : Set.EqOn b 1 (Metric.cthickening δ K))
    (k : Fin d) {z : TimeVelocity d} (hz : z ∈ K) :
    velocityGradient b z k = 0 := by
  have heq : b =ᶠ[𝓝 z] (fun _ => (1)) := by
    filter_upwards [Metric.ball_mem_nhds z hδ] with y hy
    apply hb
    exact Metric.mem_cthickening_of_dist_le y z δ K hz (le_of_lt hy)
  unfold velocityGradient
  rw [heq.fderiv_eq]
  simp

private theorem velocityGradient_tsupport_subset
     (b : TimeVelocity d → ℝ) (k : Fin d) :
    tsupport (fun z => velocityGradient b z k) ⊆ tsupport b := by
  unfold velocityGradient
  exact (closure_mono fun z hz => by
    aesop).trans (tsupport_fderiv_subset ℝ)



private theorem bounded_weak_mul_l
     (hU : IsOpen U)
    (k : Fin d) (Bq Bdq : ℝ) (hBq : 0 ≤ Bq) (hBdq : 0 ≤ Bdq)
    (q dq u du : TimeVelocity d → ℝ)
    (hqMeas : AEStronglyMeasurable q (timeVelocityVolumeOn U))
    (hdqMeas : AEStronglyMeasurable dq (timeVelocityVolumeOn U))
    (hqBound : ∀ z ∈ U, |q z| ≤ Bq)
    (hdqBound : ∀ z ∈ U, |dq z| ≤ Bdq)
    (hqWeak : HasWeakVelocityPartialDerivOn U k q dq)
    (hu : ParabolicMemLpOn U 2 u) (hdu : ParabolicMemLpOn U 2 du)
    (hweak : HasWeakVelocityPartialDerivOn U k u du) :
    HasWeakVelocityPartialDerivOn U k (fun z => q z * u z)
      (fun z => q z * du z + dq z * u z) := by
  have hUmeas  := hU.measurableSet
  have hqAE : ∀ᵐ z ∂timeVelocityVolumeOn U, |q z| ≤ Bq :=
    ae_restrict_of_forall_mem U hUmeas hqBound
  have hdqAE : ∀ᵐ z ∂timeVelocityVolumeOn U, |dq z| ≤ Bdq :=
    ae_restrict_of_forall_mem U hUmeas hdqBound
  have hqTop : MemLp q ∞ _ :=
    memLp_top_of_bound hqMeas Bq (by omega)
  have hdqTop : MemLp dq ∞ _ :=
    memLp_top_of_bound hdqMeas Bdq (by omega)
  have hqLoc : LocallyIntegrableOn q U volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hqTop.locallyIntegrable (by simp))
  have hdqLoc : LocallyIntegrableOn dq U volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hdqTop.locallyIntegrable (by simp))
  intro φ hφ hφCompact hφSub
  obtain ⟨δ, hδ, b, hb, hbCompact, hbSub, hbOne⟩ :=
    exists_contDiff_one_on_cthickening_tsupport_subset
      hU hφCompact.isCompact hφSub
  let Q  := fun z => b z * q z
  let DQ  := fun z => b z * dq z + q z * velocityGradient b z k
  have hQWeakU : HasWeakVelocityPartialDerivOn U k Q DQ := by
    simpa using
      hqWeak.mul_contDiff hb hqLoc hdqLoc
  have hQSupp : tsupport Q ⊆ U := (tsupport_mul_subset_left (f := b) (g := q)).trans hbSub
  have hDQSuppB : tsupport DQ ⊆ tsupport b := (tsupport_add _ _).trans (union_subset
      (tsupport_mul_subset_left (f := b) (g := dq))
      ((tsupport_mul_subset_right (f := q)
        (g := fun z => velocityGradient b z k)).trans
          (velocityGradient_tsupport_subset b k)))
  have hDQSupp : tsupport DQ ⊆ U := hDQSuppB.trans hbSub
  have hQWeak  :=
    hQWeakU.univ_of_tsupport_subset hU hQSupp hDQSupp
  have hQSupport : Function.support Q ⊆ U := (subset_tsupport Q).trans hQSupp
  have hDQSupport : Function.support DQ ⊆ U := (subset_tsupport DQ).trans hDQSupp
  have hbMeasU : AEStronglyMeasurable b (timeVelocityVolumeOn U) :=
    hb.continuous.aestronglyMeasurable
  have hdbMeasU : AEStronglyMeasurable (fun z => velocityGradient b z k)
      (timeVelocityVolumeOn U) := by
    unfold velocityGradient
    fun_prop
  have hQMeasU : AEStronglyMeasurable Q _ :=
    hbMeasU.mul hqMeas
  have hDQMeasU : AEStronglyMeasurable DQ _ :=
    (hbMeasU.mul hdqMeas).add (hqMeas.mul hdbMeasU)
  have hQMeas  :=
    aestronglyMeasurable_of_restrict_of_support_subset hUmeas hQMeasU hQSupport
  have hDQMeas  :=
    aestronglyMeasurable_of_restrict_of_support_subset hUmeas hDQMeasU hDQSupport
  obtain ⟨Cb, hCb⟩ := hb.continuous.bounded_above_of_compact_support hbCompact
  have hdbCont : Continuous (fun z => velocityGradient b z k) := (hb.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdbCompact  := HasCompactSupport.of_support_subset_isCompact hbCompact.isCompact
      ((subset_tsupport _).trans (velocityGradient_tsupport_subset b k))
  obtain ⟨Cdb, hCdb⟩ := hdbCont.bounded_above_of_compact_support hdbCompact
  have hQPoint : ∀ z, ‖Q z‖ ≤ |Cb| * Bq := by
    intro z
    by_cases hz : z ∈ U
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (le_trans (hCb z) (le_abs_self Cb)) (hqBound z hz)
        (abs_nonneg _) (abs_nonneg _)
    · have hQz : Q z = 0 := by
        by_contra hn
        simp_all
      simp [hQz, mul_nonneg _ hBq]
  have hDQPoint : ∀ z, ‖DQ z‖ ≤ |Cb| * Bdq + Bq * |Cdb| := by
    intro z
    by_cases hz : z ∈ U
    · calc
        |b z * dq z + q z * velocityGradient b z k| ≤
            |b z| * |dq z| + |q z| * |velocityGradient b z k| := by
              simpa using abs_add_le (b z * dq z) (q z * velocityGradient b z k)
        _ ≤ |Cb| * Bdq + Bq * |Cdb| := add_le_add
            (mul_le_mul (le_trans (hCb z) (le_abs_self Cb)) (hdqBound z hz)
              (abs_nonneg _) (abs_nonneg _))
            (mul_le_mul (hqBound z hz) (le_trans (hCdb z) (le_abs_self Cdb))
              (abs_nonneg _) hBq)
    · have hDQz : DQ z = 0 := by
        by_contra hn
        simp_all
      rw [hDQz, norm_zero]
      positivity
  have hQCompact  := HasCompactSupport.of_support_subset_isCompact hbCompact.isCompact
      ((subset_tsupport Q).trans
        (tsupport_mul_subset_left (f := b) (g := q)))
  have hQMem : MemLp Q (2) volume :=
    hQCompact.memLp_of_bound hQMeas _ (Eventually.of_forall hQPoint)
  have hDQCompact  := HasCompactSupport.of_support_subset_isCompact hbCompact.isCompact
      ((subset_tsupport _).trans hDQSuppB)
  have hDQMem : MemLp DQ (2) volume :=
    hDQCompact.memLp_of_bound hDQMeas _
      (Eventually.of_forall hDQPoint)
  have hφTop : MemLp φ ∞ _ :=
    hφ.continuous.memLp_top_of_hasCompactSupport hφCompact volume
  have hgradCont : Continuous (fun z => velocityGradient φ z k) := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgradCompact  := HasCompactSupport.of_support_subset_isCompact hφCompact.isCompact
      ((subset_tsupport _).trans (velocityGradient_tsupport_subset φ k))
  have hgradTop : MemLp (fun z => velocityGradient φ z k) ∞
      _ :=
    hgradCont.memLp_top_of_hasCompactSupport hgradCompact volume
  have huφR : ParabolicMemLpOn U 2 (fun z => u z * φ z) := by
    simpa using hu.mul' (hφTop.restrict U)
  have hduφR : ParabolicMemLpOn U 2 (fun z => du z * φ z) := by
    simpa using hdu.mul' (hφTop.restrict U)
  have huGradR : ParabolicMemLpOn U 2
      (fun z => u z * velocityGradient φ z k) := by
    simpa using hu.mul' (hgradTop.restrict U)
  have huφSupp : Function.support (fun z => u z * φ z) ⊆ U :=
    (Function.support_mul_subset_right u φ).trans (subset_tsupport φ |>.trans hφSub)
  have hduφSupp : Function.support (fun z => du z * φ z) ⊆ U :=
    (Function.support_mul_subset_right du φ).trans (subset_tsupport φ |>.trans hφSub)
  have huGradSupp : Function.support (fun z => u z * velocityGradient φ z k) ⊆ U :=
    (Function.support_mul_subset_right u _).trans
      ((subset_tsupport _).trans ((velocityGradient_tsupport_subset φ k).trans hφSub))
  have huφ  :=
    huφR.memLp_of_support_subset hUmeas huφSupp
  have hduφ  :=
    hduφR.memLp_of_support_subset hUmeas hduφSupp
  have huGrad  :=
    huGradR.memLp_of_support_subset hUmeas huGradSupp
  have hQlim := tendsto_integral_spacetimeMollification_mul_fixed Q
    _ hQMem huGrad
  have hQdulim := tendsto_integral_spacetimeMollification_mul_fixed Q
    _ hQMem hduφ
  have hDQlim := tendsto_integral_spacetimeMollification_mul_fixed DQ
    _ hDQMem huφ
  have hsmooth (ε : ℝ) (hε : 0 < ε)  := by
    have hQεsmooth := contDiff_spacetimeMollification hε Q
      (hQMem.locallyIntegrable (by norm_num))
    have hcomm := velocityGradient_spacetimeMollification hε k Q DQ
      (hQMem.locallyIntegrable (by norm_num))
      (hDQMem.locallyIntegrable (by norm_num)) hQWeak
    have hp := hweak.mul_contDiff hQεsmooth
      (hu.locallyIntegrableOn (by norm_num)) (hdu.locallyIntegrableOn (by norm_num))
    have hcommPoint (z : TimeVelocity d)  := congrFun hcomm z
    simp_rw [hcommPoint] at hp
    exact hp
  have hid : ∀ ε ∈ Ioi (0),
      (∫ z : TimeVelocity d, spacetimeMollification ε Q z *
        (u z * velocityGradient φ z k) ∂volume) =
      -((∫ z : TimeVelocity d, spacetimeMollification ε Q z *
          (du z * φ z) ∂volume) +
        ∫ z : TimeVelocity d, spacetimeMollification ε DQ z *
          (u z * φ z) ∂volume) := by
    intro ε hε
    have hw := hsmooth ε hε φ hφ hφCompact hφSub
    have hleft := integral_univ_eq_setIntegral_of_support_subset hUmeas
      (fun z => spacetimeMollification ε Q z * (u z * velocityGradient φ z k))
      ((Function.support_mul_subset_right _ _).trans huGradSupp)
    have hright₁ := integral_univ_eq_setIntegral_of_support_subset hUmeas
      (fun z => spacetimeMollification ε Q z * (du z * φ z))
      ((Function.support_mul_subset_right _ _).trans hduφSupp)
    have hright₂ := integral_univ_eq_setIntegral_of_support_subset hUmeas
      (fun z => spacetimeMollification ε DQ z * (u z * φ z))
      ((Function.support_mul_subset_right _ _).trans huφSupp)
    rw [hleft, hright₁, hright₂]
    calc
      (∫ z in U, spacetimeMollification ε Q z *
          (u z * velocityGradient φ z k) ∂volume) =
          ∫ z in U, (spacetimeMollification ε Q z * u z) *
            velocityGradient φ z k ∂volume := by
              ring
      _ = -∫ z in U, (spacetimeMollification ε Q z * du z +
          u z * spacetimeMollification ε DQ z) * φ z ∂volume := hw
      _ = -((∫ z in U, spacetimeMollification ε Q z * (du z * φ z) ∂volume) +
          ∫ z in U, spacetimeMollification ε DQ z * (u z * φ z) ∂volume) := by
            rw [← integral_add]
            · grind
            · exact ((SpacetimeMollifierL2.spacetimeMollification_memLp hε Q hQMem)
                |>.integrable_mul hduφ).restrict
            · exact ((SpacetimeMollifierL2.spacetimeMollification_memLp hε DQ hDQMem)
                |>.integrable_mul huφ).restrict
  have hlimitRight := hQdulim.add hDQlim |>.neg
  have heqEventually : ∀ᶠ ε in 𝓝[>] (0),
      (∫ z : TimeVelocity d, spacetimeMollification ε Q z *
        (u z * velocityGradient φ z k) ∂volume) =
      -((∫ z : TimeVelocity d, spacetimeMollification ε Q z *
          (du z * φ z) ∂volume) +
        ∫ z : TimeVelocity d, spacetimeMollification ε DQ z *
          (u z * φ z) ∂volume) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp_all
  have hlimEq  :=
    tendsto_nhds_unique hQlim
      (hlimitRight.congr' (heqEventually.mono fun _ h => h.symm))
  have hQeq (z : TimeVelocity d) (hz : z ∈ tsupport φ) : Q z = q z := by
    have hbz := hbOne (Metric.self_subset_cthickening _ hz)
    aesop
  have hDQeq (z : TimeVelocity d) (hz : z ∈ tsupport φ) : DQ z = dq z := by
    have hbz := hbOne (Metric.self_subset_cthickening _ hz)
    have hdbz := velocityGradient_eq_zero_of_eq_one_on hδ hbOne k hz
    aesop
  rw [integral_univ_eq_setIntegral_of_support_subset hUmeas _
      ((Function.support_mul_subset_right _ _).trans huGradSupp),
    integral_univ_eq_setIntegral_of_support_subset hUmeas _
      ((Function.support_mul_subset_right _ _).trans hduφSupp),
    integral_univ_eq_setIntegral_of_support_subset hUmeas _
      ((Function.support_mul_subset_right _ _).trans huφSupp)] at hlimEq
  calc
    (∫ z in U, (q z * u z) * velocityGradient φ z k ∂volume) =
        ∫ z in U, Q z * (u z * velocityGradient φ z k) ∂volume := by
          apply integral_congr_ae
          exact Eventually.of_forall fun z => by
            by_cases hdφ : velocityGradient φ z k = 0
            · simp_all
            · have hzts  :=
                (velocityGradient_tsupport_subset φ k)
                  (subset_tsupport _ (Function.mem_support.mpr hdφ))
              grind
    _ = -((∫ z in U, Q z * (du z * φ z) ∂volume) +
        ∫ z in U, DQ z * (u z * φ z) ∂volume) := hlimEq
    _ = -∫ z in U, (q z * du z + dq z * u z) * φ z ∂volume := by
      rw [← integral_add]
      · congr 1
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by
          by_cases hzφ : φ z = 0
          · simp_all
          · have hzts  := subset_tsupport φ
                (Function.mem_support.mpr hzφ)
            grind
      · exact (hQMem.integrable_mul hduφ).restrict
      · exact (hDQMem.integrable_mul huφ).restrict

/-- A scalar that is `C¹` on an open time--velocity carrier has its literal
velocity derivative as its raw weak velocity derivative there. -/
theorem contDiffOn_one_hasWeakVelocityPartialDerivOn
     (U : Set (TimeVelocity d)) (hU : IsOpen U)
    (i : Fin d)
    (q : TimeVelocity d → ℝ) (hq : ContDiffOn ℝ 1 q U) :
    HasWeakVelocityPartialDerivOn U i q
      (fun z => velocityGradient q z i) := by
  intro φ hφ hφCompact hφSub
  let p  := fun z => q z * φ z
  let v : TimeVelocity d := (0, Pi.single i 1)
  have hp : ContDiff ℝ 1 p := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ U
    · exact (hq.contDiffAt (hU.mem_nhds hz)).mul
        ((hφ.of_le (by norm_num)).contDiffAt)
    · have hzφ  := fun h => hz (hφSub h)
      have heq : p =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hzφ] with y hy
        simp [p, hy]
      exact (contDiffAt_const (x := z) (n := 1) (c := (0))).congr_of_eventuallyEq heq
  have hpCompact : HasCompactSupport p := hφCompact.mul_left
  have hdpCompact : HasCompactSupport (fun z => fderiv ℝ p z v) :=
    hpCompact.fderiv_apply ℝ v
  have hpInt : Integrable p := hp.continuous.integrable_of_hasCompactSupport hpCompact
  have hdpInt : Integrable (fun z => fderiv ℝ p z v) :=
    ((hp.continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport hdpCompact
  have hzero : (∫ z, fderiv ℝ p z v ∂volume) = 0 := by
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := volume) (v := v)
      (f := fun _ : TimeVelocity d => (1)) (g := p)
      (by simp) (by simpa using hdpInt) (by simpa using hpInt)
      (by fun_prop) (fun x _ => hp.differentiable (by norm_num) x)
    simpa using h
  have hprod (z : TimeVelocity d) (hz : z ∈ U) :
      fderiv ℝ p z v =
        velocityGradient q z i * φ z + q z * velocityGradient φ z i := by
    rw [show p = fun y => q y * φ y from rfl]
    rw [fderiv_fun_mul ((hq.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))
      (hφ.differentiable (by simp) z)]
    simp [v, velocityGradient, add_comm, mul_comm]
  have houtside (z : TimeVelocity d) (hz : z ∉ U) :
      fderiv ℝ p z v = 0 := congrArg (fun L => L v)
      (fderiv_of_notMem_tsupport ℝ
        (fun hp' => hz (hφSub (tsupport_mul_subset_right hp'))))
  have hglobal : (∫ z, fderiv ℝ p z v ∂volume) =
      ∫ z in U, (velocityGradient q z i * φ z +
        q z * velocityGradient φ z i) ∂volume := by
    rw [← integral_indicator hU.measurableSet]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      by_cases hz : z ∈ U
      · simp [Set.indicator_of_mem hz, hprod z hz]
      · simp [Set.indicator_of_notMem hz, houtside z hz]
  rw [hglobal] at hzero
  have hleft : IntegrableOn (fun z => q z * velocityGradient φ z i) U := by
    have hc : Continuous (fun z => q z * velocityGradient φ z i) := by
      rw [continuous_iff_continuousAt]
      intro z
      by_cases hz : z ∈ U
      · exact (hq.contDiffAt (hU.mem_nhds hz)).continuousAt.mul
          ((hφ.continuous_fderiv (by simp)).clm_apply
            continuous_const).continuousAt
      · have hzφ  := fun h => hz (hφSub h)
        have hd := (notMem_tsupport_iff_eventuallyEq.mp hzφ).fderiv (𝕜 := ℝ)
        exact continuousAt_const.congr_of_eventuallyEq (hd.mono fun y hy => by
          change q y * fderiv ℝ φ y _ = 0
          rw [hy]
          simp)
    exact (hc.integrable_of_hasCompactSupport
      ((hφCompact.fderiv_apply ℝ
        _).mul_left)).integrableOn
  have hright : IntegrableOn (fun z => velocityGradient q z i * φ z) U := by
    have hc : Continuous (fun z => velocityGradient q z i * φ z) := by
      rw [continuous_iff_continuousAt]
      intro z
      by_cases hz : z ∈ U
      · unfold velocityGradient
        exact (((hq.contDiffAt (hU.mem_nhds hz)).continuousAt_fderiv
          (by norm_num)).clm_apply
            continuousAt_const).mul
          hφ.continuous.continuousAt
      · have hzφ  := fun h => hz (hφSub h)
        have heq := notMem_tsupport_iff_eventuallyEq.mp hzφ
        exact continuousAt_const.congr_of_eventuallyEq (heq.mono fun y hy => by
          change velocityGradient q y i * φ y = 0
          simp [hy])
    exact (hc.integrable_of_hasCompactSupport hφCompact.mul_left).integrableOn
  rw [integral_add hright hleft] at hzero
  linarith

/-- A bounded `C¹` multiplier obeys the weak velocity Leibniz rule on an
arbitrary open carrier, with sharp componentwise `L²` bounds. -/
theorem velocityC1_mul_hasWeakVelocityPartialDerivOn_memLp_eLpNorm_le
     (hU : IsOpen U)
    (i : Fin d)
    (Bq Bdi : ℝ) (hBq : 0 ≤ Bq) (hBdi : 0 ≤ Bdi)
    (q : TimeVelocity d → ℝ) (hqC1 : ContDiffOn ℝ 1 q U)
    (hqBound : ∀ z ∈ U, |q z| ≤ Bq)
    (hdiBound : ∀ z ∈ U, |velocityGradient q z i| ≤ Bdi)
    (u dui : TimeVelocity d → ℝ)
    (hu : ParabolicMemLpOn U 2 u)
    (hdui : ParabolicMemLpOn U 2 dui)
    (hweak : HasWeakVelocityPartialDerivOn U i u dui) :
    AEStronglyMeasurable (fun z => velocityGradient q z i)
        (timeVelocityVolumeOn U) ∧
      ParabolicMemLpOn U 2 (fun z => q z * u z) ∧
      ParabolicMemLpOn U 2
        (fun z => q z * dui z + velocityGradient q z i * u z) ∧
      HasWeakVelocityPartialDerivOn U i
        (fun z => q z * u z)
        (fun z => q z * dui z + velocityGradient q z i * u z) ∧
      ENNReal.toReal
          (eLpNorm (fun z => q z * u z) 2 (timeVelocityVolumeOn U)) ≤
        Bq * ENNReal.toReal
          (eLpNorm u 2 (timeVelocityVolumeOn U)) ∧
      ENNReal.toReal
          (eLpNorm
            (fun z => q z * dui z + velocityGradient q z i * u z)
            2 (timeVelocityVolumeOn U)) ≤
        Bq * ENNReal.toReal
          (eLpNorm dui 2 (timeVelocityVolumeOn U)) +
        Bdi * ENNReal.toReal
          (eLpNorm u 2 (timeVelocityVolumeOn U)) := by
  have hUmeas  := hU.measurableSet
  have hqMeas : AEStronglyMeasurable q (timeVelocityVolumeOn U) :=
    hqC1.continuousOn.aestronglyMeasurable hUmeas
  have hdiMeas : AEStronglyMeasurable (fun z => velocityGradient q z i)
      (timeVelocityVolumeOn U) := by
    have hc : ContinuousOn (fun z => velocityGradient q z i) U := fun z hz => by
      exact ((hqC1.contDiffAt (hU.mem_nhds hz)).continuousAt_fderiv
        (by norm_num)).clm_apply
          continuousAt_const
        |>.continuousWithinAt
    exact hc.aestronglyMeasurable hUmeas
  have hqAE : ∀ᵐ z ∂timeVelocityVolumeOn U, |q z| ≤ Bq :=
    ae_restrict_of_forall_mem U hUmeas hqBound
  have hdiAE : ∀ᵐ z ∂timeVelocityVolumeOn U,
      |velocityGradient q z i| ≤ Bdi :=
    ae_restrict_of_forall_mem U hUmeas hdiBound
  obtain ⟨hqu, hquNorm⟩ := toReal_eLpNorm_mul_le hBq hqMeas hu hqAE
  obtain ⟨hqdui, hqduiNorm⟩ := toReal_eLpNorm_mul_le hBq hqMeas hdui hqAE
  obtain ⟨hdiu, hdiuNorm⟩ := toReal_eLpNorm_mul_le hBdi hdiMeas hu hdiAE
  have hsum : ParabolicMemLpOn U 2
      (fun z => q z * dui z + velocityGradient q z i * u z) := hqdui.add hdiu
  have hsumNorm : ENNReal.toReal
      (eLpNorm (fun z => q z * dui z + velocityGradient q z i * u z) 2
        (timeVelocityVolumeOn U)) ≤
      Bq * ENNReal.toReal (eLpNorm dui 2 (timeVelocityVolumeOn U)) +
        Bdi * ENNReal.toReal (eLpNorm u 2 (timeVelocityVolumeOn U)) := by
    have htri : eLpNorm
        _ 2
        _ ≤
        eLpNorm (fun z => q z * dui z) 2 _ +
          eLpNorm (fun z => velocityGradient q z i * u z) 2
            (timeVelocityVolumeOn U) := eLpNorm_add_le (by norm_num)
    have hreal := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨hqdui.eLpNorm_ne_top, hdiu.eLpNorm_ne_top⟩) htri
    rw [ENNReal.toReal_add hqdui.eLpNorm_ne_top hdiu.eLpNorm_ne_top] at hreal
    exact hreal.trans (add_le_add hqduiNorm hdiuNorm)
  have hqWeak := contDiffOn_one_hasWeakVelocityPartialDerivOn U hU i q hqC1
  have hmulWeak  :=
    bounded_weak_mul_l hU i Bq Bdi hBq hBdi q _ u dui
      hqMeas hdiMeas hqBound hdiBound hqWeak hu hdui hweak
  simp_all

end HypoellipticAleksandrov.Parabolic
