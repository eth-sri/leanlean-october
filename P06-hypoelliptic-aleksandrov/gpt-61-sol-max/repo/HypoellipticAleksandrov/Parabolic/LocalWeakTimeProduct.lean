module

public import HypoellipticAleksandrov.Parabolic.WeakJetProduct
public import HypoellipticAleksandrov.Parabolic.TimeVelocitySmoothCompactPlateau
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesCompactGlobalization
public import HypoellipticAleksandrov.Parabolic.WeakDerivativeSpacetimeMollification
public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifierL2
public import HypoellipticAleksandrov.Analysis.L2ProductConvergence
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Aesop
import Mathlib.Tactic.Ring
public import HypoellipticAleksandrov.Measure.TimeVelocity




/-!
# Local weak-time product rule for jointly `C¹` multipliers

This module proves the raw weak time derivative of a jointly `C¹` scalar and
the quantitative weak time product rule for bounded jointly `C¹` multipliers.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal Topology
open SpacetimeMollifier

variable {α : Type*}

private theorem ae_restrict_of_forall_mem
     [MeasurableSpace α] {μ : Measure α}
    (S : Set α) (hS : MeasurableSet S) {P : α → Prop} (hP : ∀ x ∈ S, P x) :
    ∀ᵐ x ∂μ.restrict S, P x := by
  filter_upwards [ae_restrict_mem hS] with x hx
  exact hP x hx

private theorem memLp_mul_of_abs_le
     [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} {a f : α → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (ha : AEStronglyMeasurable a μ)
    (hf : MemLp f p μ) (haM : ∀ᵐ x ∂μ, |a x| ≤ M) :
    MemLp (fun x => a x * f x) p μ ∧
      eLpNorm (fun x => a x * f x) p μ ≤
        ENNReal.ofReal M * eLpNorm f p μ := by
  have hmeas  := ha.mul hf.aestronglyMeasurable
  have hpoint : ∀ᵐ x ∂μ, ‖a x * f x‖ ≤ M * ‖f x‖ := by
    filter_upwards [haM] with x hx
    simpa only [Real.norm_eq_abs, abs_mul] using
      mul_le_mul hx le_rfl (abs_nonneg (f x)) hM
  exact ⟨MemLp.of_le_mul hf hmeas hpoint,
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas hpoint p⟩

private theorem toReal_eLpNorm_mul_le
     [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} {a f : α → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (ha : AEStronglyMeasurable a μ)
    (hf : MemLp f p μ) (haM : ∀ᵐ x ∂μ, |a x| ≤ M) :
    MemLp (fun x => a x * f x) p μ ∧
      ENNReal.toReal (eLpNorm (fun x => a x * f x) p μ) ≤
        M * ENNReal.toReal (eLpNorm f p μ) := by
  obtain ⟨haf, hle⟩ := memLp_mul_of_abs_le hM ha hf haM
  refine ⟨haf, ?_⟩


  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM] using (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top) hle)

variable {d : ℕ}

private theorem aestronglyMeasurable_of_restrict_of_support_subset
     {U : HypoellipticAleksandrov.Parabolic.Region d} (hU : MeasurableSet U)
    {f : TimeVelocity d → ℝ}
    (hf : AEStronglyMeasurable f (timeVelocityVolumeOn U))
    (hsupp : Function.support f ⊆ U) :
    AEStronglyMeasurable f  := by
  have hindicator : U.indicator f = f := by
    funext z
    by_cases hz : z ∈ U
    · simp [hz]
    · have hfz : f z = 0 := by
        by_contra hn
        exact hz (hsupp (Function.mem_support.mpr hn))
      simp [hz, hfz]
  rw [← hindicator]
  exact (aestronglyMeasurable_indicator_iff hU).2 hf

private theorem timeDerivative_eq_zero_of_eq_one_on
     {b : TimeVelocity d → ℝ} {K : HypoellipticAleksandrov.Parabolic.Region d}
    {δ : ℝ} (hδ : 0 < δ) (hb : Set.EqOn b 1 (Metric.cthickening δ K))
    {z : TimeVelocity d} (hz : z ∈ K) :
    timeDerivative b z = 0 := by
  have heq : b =ᶠ[𝓝 z] (fun _ => (1 )) := by
    filter_upwards [Metric.ball_mem_nhds z hδ] with y hy
    apply hb
    exact Metric.mem_cthickening_of_dist_le y z δ K hz (le_of_lt hy)
  unfold timeDerivative
  rw [heq.fderiv_eq]
  simp

private theorem timeDerivative_tsupport_subset_local
     (b : TimeVelocity d → ℝ) :
    tsupport ((timeDerivative b)) ⊆ tsupport b := by
  unfold timeDerivative
  change closure (Function.support
    (fun z => fderiv ℝ b z ((1, 0) ))) ⊆ tsupport b
  exact (closure_mono fun z hz => by
    aesop).trans (tsupport_fderiv_subset ℝ)

private theorem tendsto_integral_spacetimeMollification_mul_fixed
     (f g : TimeVelocity d → ℝ)
    (hf : MemLp f (2 ) )
    (hg : MemLp g (2 ) ) :
    Tendsto
      (fun ε  => ∫ z : TimeVelocity d,
        spacetimeMollification ε f z * g z)
      (𝓝[>] 0) (𝓝 (∫ z : TimeVelocity d, f z * g z)) := by
  apply HypoellipticAleksandrov.Analysis.tendsto_integral_mul_of_tendsto_eLpNorm_two
      (fun ε => spacetimeMollification ε f) (fun _ => g) f g
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact SpacetimeMollifierL2.spacetimeMollification_memLp hε f hf
  · exact Eventually.of_forall fun _ => hg
  · exact hf
  · exact hg
  · exact
      SpacetimeMollifierL2.tendsto_eLpNorm_spacetimeMollification_sub f hf
  · simp_all

private theorem integral_univ_eq_setIntegral_of_support_subset
     {U : HypoellipticAleksandrov.Parabolic.Region d} (hU : MeasurableSet U)
    (f : TimeVelocity d → ℝ) (hsupp : Function.support f ⊆ U) :
    (∫ z : TimeVelocity d, f z) = ∫ z in U, f z := by
  rw [← integral_indicator hU]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    by_cases hz : z ∈ U
    · simp [hz]
    · have hfz : f z = 0 := by
        by_contra hn
        exact hz (hsupp (Function.mem_support.mpr hn))
      simp [hz, hfz]

/-- A scalar that is `C¹` on an open time--velocity carrier has its literal
time derivative as its raw weak time derivative there. -/
theorem contDiffOn_one_hasWeakTimeDerivOn
     (U : HypoellipticAleksandrov.Parabolic.Region d) (hU : IsOpen U)
    (q : TimeVelocity d → ℝ) (hq : ContDiffOn ℝ 1 q U) :
    HasWeakTimeDerivOn U q (timeDerivative q) := by
  intro φ hφ hφCompact hφSub
  let p  := fun z => q z * φ z
  have hp : ContDiff ℝ 1 p := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ U
    · exact (hq.contDiffAt (hU.mem_nhds hz)).mul
        ((hφ.of_le (by norm_num)).contDiffAt)
    · have hzφ  := fun h => hz (hφSub h)

      exact (contDiffAt_const (x := z) (n := 1) (c := (0 : ℝ))).congr_of_eventuallyEq (by
          filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hzφ] with y hy
          simp [p, hy])
  have hpCompact : HasCompactSupport p := hφCompact.mul_left


  have hdpInt : Integrable (fun z => fderiv ℝ p z ((1, 0) )) :=
    ((hp.continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport (hpCompact.fderiv_apply ℝ ((1, 0) ))
  have hzero : (∫ z, fderiv ℝ p z ((1, 0) )) = 0 := by
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := volume) (v := ((1, 0) ))
      (f := fun _ : TimeVelocity d => (1 : ℝ)) (g := p)
      (by simp) (by simpa using hdpInt) (by simpa using (hp.continuous.integrable_of_hasCompactSupport hpCompact))
      (by fun_prop) (fun z _ => hp.differentiable (by norm_num) z)
    simpa using h
  have hprod (z : TimeVelocity d) (hz : z ∈ U) :
      fderiv ℝ p z ((1, 0) ) =
        timeDerivative q z * φ z + q z * timeDerivative φ z := by
    rw [show p = fun y => q y * φ y from rfl]
    rw [fderiv_fun_mul ((hq.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))
      (hφ.differentiable (by simp) z)]
    simp [timeDerivative, add_comm, mul_comm]
  have houtside (z : TimeVelocity d) (hz : z ∉ U) :
      fderiv ℝ p z ((1, 0) ) = 0 := by
    exact congrArg (fun L => L ((1, 0) ))
      (fderiv_of_notMem_tsupport ℝ
        (fun hp' => hz (hφSub (tsupport_mul_subset_right hp'))))
  have hglobal : (∫ z, fderiv ℝ p z ((1, 0) )) =
      ∫ z in U, (timeDerivative q z * φ z + q z * timeDerivative φ z) := by
    rw [← integral_indicator hU.measurableSet]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      by_cases hz : z ∈ U
      · simp [Set.indicator_of_mem hz, hprod z hz]
      · simp [Set.indicator_of_notMem hz, houtside z hz]
  rw [hglobal] at hzero


  rw [integral_add (by
      have hc : Continuous (fun z => timeDerivative q z * φ z) := by
        rw [continuous_iff_continuousAt]
        intro z
        by_cases hz : z ∈ U
        · unfold timeDerivative
          exact (((hq.contDiffAt (hU.mem_nhds hz)).continuousAt_fderiv (by norm_num)).clm_apply
            (continuousAt_const : ContinuousAt (fun _ => ((1, 0) : TimeVelocity d)) z)).mul
            hφ.continuous.continuousAt
        ·

          exact continuousAt_const.congr_of_eventuallyEq ((notMem_tsupport_iff_eventuallyEq.mp (fun h => hz (hφSub h))).mono fun y hy => by
            change timeDerivative q y * φ y = 0
            simp [hy])
      exact (hc.integrable_of_hasCompactSupport hφCompact.mul_left).integrableOn) (by
      have hc : Continuous (fun z => q z * timeDerivative φ z) := by
        rw [continuous_iff_continuousAt]
        intro z
        by_cases hz : z ∈ U
        · exact (hq.contDiffAt (hU.mem_nhds hz)).continuousAt.mul
            ((hφ.continuous_fderiv (by simp)).clm_apply
              (continuous_const : Continuous (fun _ => ((1, 0) : TimeVelocity d)))).continuousAt
        ·

          exact continuousAt_const.congr_of_eventuallyEq (((notMem_tsupport_iff_eventuallyEq.mp (fun h => hz (hφSub h))).fderiv (𝕜 := ℝ)).mono fun y hy => by
            change q y * fderiv ℝ φ y ((1, 0) ) = 0
            rw [hy]
            simp)
      exact (hc.integrable_of_hasCompactSupport
        ((hφCompact.fderiv_apply ℝ ((1, 0) )).mul_left)).integrableOn)] at hzero
  linarith

variable {U : HypoellipticAleksandrov.Parabolic.Region d} (hU : IsOpen U)

include hU
private theorem bounded_weak_mul

    (Bq Bdq : ℝ) (hBq : 0 ≤ Bq) (hBdq : 0 ≤ Bdq)
    (q dq u du : TimeVelocity d → ℝ)
    (hqMeas : AEStronglyMeasurable q (timeVelocityVolumeOn U))
    (hdqMeas : AEStronglyMeasurable dq (timeVelocityVolumeOn U))
    (hqBound : ∀ z ∈ U, |q z| ≤ Bq)
    (hdqBound : ∀ z ∈ U, |dq z| ≤ Bdq)
    (hqWeak : HasWeakTimeDerivOn U q dq)
    (hu : ParabolicMemLpOn U 2 u) (hdu : ParabolicMemLpOn U 2 du)
    (hweak : HasWeakTimeDerivOn U u du) :
    HasWeakTimeDerivOn U (fun z => q z * u z)
      (fun z => q z * du z + dq z * u z) := by
  let sharedTerm_5147203612 := ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))
  have hUmeas  := hU.measurableSet


  have hqTop  :=
    memLp_top_of_bound hqMeas Bq ((ae_restrict_of_forall_mem U hUmeas hqBound))
  have hdqTop  :=
    memLp_top_of_bound hdqMeas Bdq ((ae_restrict_of_forall_mem U hUmeas hdqBound))


  intro φ hφ hφCompact hφSub
  obtain ⟨δ, hδ, b, hb, hbCompact, hbSub, hbOne⟩ :=
    exists_contDiff_one_on_cthickening_tsupport_subset
      hU hφCompact.isCompact hφSub
  let Q  := fun z => b z * q z
  let DQ  := fun z => b z * dq z + q z * timeDerivative b z

  have hQSupp  := (tsupport_mul_subset_left (f := b) (g := q)).trans hbSub
  have hDQSuppB : tsupport DQ ⊆ tsupport b := (tsupport_add _ _).trans (union_subset
      (tsupport_mul_subset_left  )
      ((tsupport_mul_subset_right (f := q)
        (g := (timeDerivative b))).trans
          (timeDerivative_tsupport_subset_local b)))
  have hDQSupp  := hDQSuppB.trans hbSub

  have hQSupport  := (subset_tsupport Q).trans hQSupp
  have hDQSupport  := (subset_tsupport DQ).trans hDQSupp
  have hbMeasU : AEStronglyMeasurable b (timeVelocityVolumeOn U) :=
    hb.continuous.aestronglyMeasurable





  obtain ⟨Cb, hCb⟩ := hb.continuous.bounded_above_of_compact_support hbCompact
  have hdbCont : Continuous ((timeDerivative b)) := by
    unfold timeDerivative
    exact (hb.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdbCompact  := HasCompactSupport.of_support_subset_isCompact hbCompact.isCompact
      ((subset_tsupport _).trans (timeDerivative_tsupport_subset_local b))
  obtain ⟨Cdb, hCdb⟩ := hdbCont.bounded_above_of_compact_support hdbCompact


  have hQCompact  := HasCompactSupport.of_support_subset_isCompact hbCompact.isCompact
      ((subset_tsupport Q).trans
        (tsupport_mul_subset_left  ))
  have hQMem : MemLp Q (2 ) sharedTerm_5147203612 :=
    hQCompact.memLp_of_bound (aestronglyMeasurable_of_restrict_of_support_subset hUmeas (hbMeasU.mul hqMeas) hQSupport) (|Cb| * Bq) (Eventually.of_forall (by
        intro z
        by_cases hz : z ∈ U
        · dsimp only [Q]
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (le_trans (hCb z) (le_abs_self Cb)) (hqBound z hz)
            (abs_nonneg _) (abs_nonneg _)
        · have hQz : Q z = 0 := by
            by_contra hn
            exact hz (hQSupport (Function.mem_support.mpr hn))
          simp [hQz, mul_nonneg (abs_nonneg Cb) hBq]))
  have hDQCompact  := HasCompactSupport.of_support_subset_isCompact hbCompact.isCompact
      ((subset_tsupport _).trans hDQSuppB)
  have hDQMem : MemLp DQ (2 ) sharedTerm_5147203612 :=
    hDQCompact.memLp_of_bound (aestronglyMeasurable_of_restrict_of_support_subset hUmeas ((hbMeasU.mul hdqMeas).add (hqMeas.mul (show AEStronglyMeasurable ((timeDerivative b))
      (timeVelocityVolumeOn U) by
        unfold timeDerivative
        exact ((hb.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable))) hDQSupport) _
      (Eventually.of_forall (by
          intro z
          by_cases hz : z ∈ U
          · dsimp only [DQ]
            rw [Real.norm_eq_abs]
            calc
              |b z * dq z + q z * timeDerivative b z| ≤
                  |b z| * |dq z| + |q z| * |timeDerivative b z| := by
                    simpa only [abs_mul] using abs_add_le (b z * dq z) (q z * timeDerivative b z)
              _ ≤ |Cb| * Bdq + Bq * |Cdb| := add_le_add
                  (mul_le_mul (le_trans (hCb z) (le_abs_self Cb)) (hdqBound z hz)
                    (abs_nonneg _) (abs_nonneg _))
                  (mul_le_mul (hqBound z hz) (le_trans (hCdb z) (le_abs_self Cdb))
                    (abs_nonneg _) hBq)
          · have hDQz : DQ z = 0 := by
              by_contra hn
              exact hz (hDQSupport (Function.mem_support.mpr hn))
            rw [hDQz, norm_zero]
            exact add_nonneg (mul_nonneg (abs_nonneg Cb) hBdq)
              (mul_nonneg hBq (abs_nonneg Cdb))))
  have hφTop : MemLp φ ∞ sharedTerm_5147203612 :=
    hφ.continuous.memLp_top_of_hasCompactSupport hφCompact volume
  have hgradCont : Continuous ((timeDerivative φ)) := by
    unfold timeDerivative
    exact (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgradCompact  := HasCompactSupport.of_support_subset_isCompact hφCompact.isCompact
      ((subset_tsupport _).trans (timeDerivative_tsupport_subset_local φ))




  have huφSupp  :=
    (Function.support_mul_subset_right u φ).trans (subset_tsupport φ |>.trans hφSub)
  have hduφSupp  :=
    (Function.support_mul_subset_right du φ).trans (subset_tsupport φ |>.trans hφSub)
  have huGradSupp  :=
    (Function.support_mul_subset_right u _).trans
      ((subset_tsupport _).trans ((timeDerivative_tsupport_subset_local φ).trans hφSub))
  have huφ  :=
    (show ParabolicMemLpOn U 2 (fun z => u z * φ z) by
        simpa only using hu.mul' (hφTop.restrict U)).memLp_of_support_subset hUmeas huφSupp
  have hduφ  :=
    (show ParabolicMemLpOn U 2 (fun z => du z * φ z) by
        simpa only using hdu.mul' (hφTop.restrict U)).memLp_of_support_subset hUmeas hduφSupp

  have hQlim := tendsto_integral_spacetimeMollification_mul_fixed Q
    _ hQMem ((show ParabolicMemLpOn U 2
      (fun z => u z * timeDerivative φ z) by
        simpa only using hu.mul' ((hgradCont.memLp_top_of_hasCompactSupport hgradCompact volume).restrict U)).memLp_of_support_subset hUmeas huGradSupp)
  have hQdulim := tendsto_integral_spacetimeMollification_mul_fixed Q
    _ hQMem hduφ
  have hDQlim := tendsto_integral_spacetimeMollification_mul_fixed DQ
    _ hDQMem huφ
  have hsmooth (ε : ℝ) (hε : 0 < ε) :
      HasWeakTimeDerivOn U
        (fun z => spacetimeMollification ε Q z * u z)
        (fun z => spacetimeMollification ε Q z * du z +
          u z * spacetimeMollification ε DQ z) := by
    have hQεsmooth := contDiff_spacetimeMollification hε Q
      (hQMem.locallyIntegrable (by norm_num))
    have hcomm := timeDerivative_spacetimeMollification hε Q DQ
      (hQMem.locallyIntegrable (by norm_num))
      (hDQMem.locallyIntegrable (by norm_num)) ((show HasWeakTimeDerivOn U Q DQ by
          exact hqWeak.mul_contDiff hb (locallyIntegrableOn_of_locallyIntegrable_restrict (hqTop.locallyIntegrable (by simp))) (locallyIntegrableOn_of_locallyIntegrable_restrict (hdqTop.locallyIntegrable (by simp)))).univ_of_tsupport_subset hU hQSupp hDQSupp)
    have hp := hweak.mul_contDiff hQεsmooth
      (hu.locallyIntegrableOn (by norm_num)) (hdu.locallyIntegrableOn (by norm_num))
    have hcommPoint (z : TimeVelocity d)  := congrFun hcomm z
    simp_rw [hcommPoint] at hp
    exact hp



  have hlimEq  :=
    tendsto_nhds_unique hQlim
      ((hQdulim.add hDQlim |>.neg).congr' ((show ∀ᶠ ε in 𝓝[>] (0 ),
      (∫ z : TimeVelocity d, spacetimeMollification ε Q z *
        (u z * timeDerivative φ z)) =
      -((∫ z : TimeVelocity d, spacetimeMollification ε Q z *
          (du z * φ z)) +
        ∫ z : TimeVelocity d, spacetimeMollification ε DQ z *
          (u z * φ z)) by
          filter_upwards [self_mem_nhdsWithin] with ε hε
          exact (show ∀ ε ∈ Ioi (0 : ℝ),
            (∫ z : TimeVelocity d, spacetimeMollification ε Q z *
              (u z * timeDerivative φ z)) =
            -((∫ z : TimeVelocity d, spacetimeMollification ε Q z *
                (du z * φ z)) +
              ∫ z : TimeVelocity d, spacetimeMollification ε DQ z *
                (u z * φ z)) by
              intro ε hε

              have hleft := integral_univ_eq_setIntegral_of_support_subset hUmeas
                (fun z => spacetimeMollification ε Q z * (u z * timeDerivative φ z))
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
                    (u z * timeDerivative φ z)) =
                    ∫ z in U, (spacetimeMollification ε Q z * u z) *
                      timeDerivative φ z := by
                        ring
                _ = -∫ z in U, (spacetimeMollification ε Q z * du z +
                    u z * spacetimeMollification ε DQ z) * φ z := (hsmooth ε hε φ hφ hφCompact hφSub)
                _ = -((∫ z in U, spacetimeMollification ε Q z * (du z * φ z)) +
                    ∫ z in U, spacetimeMollification ε DQ z * (u z * φ z)) := by
                      rw [← integral_add]
                      · congr 1
                        apply integral_congr_ae
                        exact Eventually.of_forall fun z => by ring
                      · exact ((SpacetimeMollifierL2.spacetimeMollification_memLp hε Q hQMem)
                          |>.integrable_mul hduφ).restrict
                      · exact ((SpacetimeMollifierL2.spacetimeMollification_memLp hε DQ hDQMem)
                          |>.integrable_mul huφ).restrict) ε hε).mono fun _ h => h.symm))
  have hQeq (z : TimeVelocity d) (hz : z ∈ tsupport φ) : Q z = q z := by

    simp [Q, (hbOne (Metric.self_subset_cthickening (tsupport φ) hz))]
  have hDQeq (z : TimeVelocity d) (hz : z ∈ tsupport φ) : DQ z = dq z := by


    simp [DQ, (hbOne (Metric.self_subset_cthickening (tsupport φ) hz)), (timeDerivative_eq_zero_of_eq_one_on hδ hbOne hz)]
  rw [integral_univ_eq_setIntegral_of_support_subset hUmeas _
      ((Function.support_mul_subset_right _ _).trans huGradSupp),
    integral_univ_eq_setIntegral_of_support_subset hUmeas _
      ((Function.support_mul_subset_right _ _).trans hduφSupp),
    integral_univ_eq_setIntegral_of_support_subset hUmeas _
      ((Function.support_mul_subset_right _ _).trans huφSupp)] at hlimEq
  calc
    (∫ z in U, (q z * u z) * timeDerivative φ z) =
        ∫ z in U, Q z * (u z * timeDerivative φ z) := by
          apply integral_congr_ae
          exact Eventually.of_forall fun z => by
            by_cases hdφ : timeDerivative φ z = 0
            · simp [hdφ]
            · have hzts  :=
                (timeDerivative_tsupport_subset_local φ)
                  (subset_tsupport _ (Function.mem_support.mpr hdφ))
              change q z * u z * timeDerivative φ z =
                Q z * (u z * timeDerivative φ z)
              rw [hQeq z hzts]
              ring
    _ = -((∫ z in U, Q z * (du z * φ z)) +
        ∫ z in U, DQ z * (u z * φ z)) := hlimEq
    _ = -∫ z in U, (q z * du z + dq z * u z) * φ z := by
      rw [← integral_add]
      · congr 1
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by
          by_cases hzφ : φ z = 0
          · simp [hzφ]
          · have hzts  := subset_tsupport φ
                (Function.mem_support.mpr hzφ)
            change Q z * (du z * φ z) + DQ z * (u z * φ z) =
              (q z * du z + dq z * u z) * φ z
            rw [hQeq z hzts, hDQeq z hzts]
            ring
      · exact (hQMem.integrable_mul hduφ).restrict
      · exact (hDQMem.integrable_mul huφ).restrict

/-- A bounded jointly `C¹` multiplier obeys the weak time Leibniz rule on an
open carrier, with quantitative `L²` control. -/
theorem timeC1_mul_hasWeakTimeDerivOn_memLp_eLpNorm_le

    (Bq Bdt : ℝ) (hBq : 0 ≤ Bq) (hBdt : 0 ≤ Bdt)
    (q : TimeVelocity d → ℝ) (hqC1 : ContDiffOn ℝ 1 q U)
    (hqBound : ∀ z ∈ U, |q z| ≤ Bq)
    (hdtqBound : ∀ z ∈ U, |timeDerivative q z| ≤ Bdt)
    (u ut : TimeVelocity d → ℝ)
    (hu : ParabolicMemLpOn U 2 u)
    (hut : ParabolicMemLpOn U 2 ut)
    (hweak : HasWeakTimeDerivOn U u ut) :
    AEStronglyMeasurable (timeDerivative q) (timeVelocityVolumeOn U) ∧
      ParabolicMemLpOn U 2 (fun z ↦ q z * u z) ∧
      ParabolicMemLpOn U 2
        (fun z ↦ q z * ut z + timeDerivative q z * u z) ∧
      HasWeakTimeDerivOn U (fun z ↦ q z * u z)
        (fun z ↦ q z * ut z + timeDerivative q z * u z) ∧
      ENNReal.toReal (eLpNorm (fun z ↦ q z * u z) 2
          (timeVelocityVolumeOn U)) ≤
        Bq * ENNReal.toReal (eLpNorm u 2 (timeVelocityVolumeOn U)) ∧
      ENNReal.toReal (eLpNorm
          (fun z ↦ q z * ut z + timeDerivative q z * u z) 2
          (timeVelocityVolumeOn U)) ≤
        Bq * ENNReal.toReal (eLpNorm ut 2 (timeVelocityVolumeOn U)) +
          Bdt * ENNReal.toReal (eLpNorm u 2 (timeVelocityVolumeOn U)) := by

  have hUmeas  := hU.measurableSet
  have hqMeas : AEStronglyMeasurable q (timeVelocityVolumeOn U) :=
    hqC1.continuousOn.aestronglyMeasurable hUmeas
  have hdtqMeas : AEStronglyMeasurable (timeDerivative q)
      (timeVelocityVolumeOn U) := by
    have hc : ContinuousOn (timeDerivative q) U := fun z hz => by
      unfold timeDerivative
      exact ((hqC1.contDiffAt (hU.mem_nhds hz)).continuousAt_fderiv
        (by norm_num)).clm_apply
          (continuousAt_const : ContinuousAt (fun _ => ((1, 0) : TimeVelocity d)) z)
        |>.continuousWithinAt
    exact hc.aestronglyMeasurable hUmeas
  have hqAE : ∀ᵐ z ∂timeVelocityVolumeOn U, |q z| ≤ Bq :=
    ae_restrict_of_forall_mem U hUmeas hqBound

  obtain ⟨hqu, hquNorm⟩ := toReal_eLpNorm_mul_le hBq hqMeas hu hqAE
  obtain ⟨hqut, hqutNorm⟩ := toReal_eLpNorm_mul_le hBq hqMeas hut hqAE
  obtain ⟨hdtqu, hdtquNorm⟩ :=
    toReal_eLpNorm_mul_le hBdt hdtqMeas hu (ae_restrict_of_forall_mem U hUmeas hdtqBound)



  have hmulWeak : HasWeakTimeDerivOn U (fun z => q z * u z)
      (((fun z => q z * ut z + timeDerivative q z * u z))) :=
    bounded_weak_mul hU Bq Bdt hBq hBdt q (timeDerivative q) u ut
      hqMeas hdtqMeas hqBound hdtqBound (contDiffOn_one_hasWeakTimeDerivOn U hU q hqC1) hu hut hweak
  exact ⟨hdtqMeas, hqu, (hqut.add hdtqu), hmulWeak, hquNorm, (by

      have hreal := ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr ⟨hqut.eLpNorm_ne_top, hdtqu.eLpNorm_ne_top⟩) (eLpNorm_add_le (by norm_num))
      rw [ENNReal.toReal_add hqut.eLpNorm_ne_top hdtqu.eLpNorm_ne_top] at hreal
      exact hreal.trans (add_le_add hqutNorm hdtquNorm))⟩

end HypoellipticAleksandrov.Parabolic
