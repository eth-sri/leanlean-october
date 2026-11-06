module

public import HypoellipticAleksandrov.Parabolic.MeasurableSpatialC1RawWeakDerivative
public import HypoellipticAleksandrov.Parabolic.TimeVelocitySmoothCompactPlateau
public import HypoellipticAleksandrov.Parabolic.WeakJetProduct
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesCompactGlobalization
public import HypoellipticAleksandrov.Parabolic.WeakDerivativeSpacetimeMollification
public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifierL2
public import HypoellipticAleksandrov.Analysis.L2ProductConvergence
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Ring
import all HypoellipticAleksandrov.Parabolic.LocalWeakTimeProduct
import all HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
public import HypoellipticAleksandrov.Measure.TimeVelocity


open private HypoellipticAleksandrov.Parabolic.tendsto_integral_spacetimeMollification_mul_fixed from HypoellipticAleksandrov.Parabolic.LocalWeakTimeProduct
open private HypoellipticAleksandrov.Parabolic.memLp_mul_of_abs_le from HypoellipticAleksandrov.Parabolic.LocalWeakTimeProduct
open private HypoellipticAleksandrov.Parabolic.toReal_eLpNorm_mul_le from HypoellipticAleksandrov.Parabolic.LocalWeakTimeProduct
open private HypoellipticAleksandrov.Parabolic.aestronglyMeasurable_of_restrict_of_support_subset from HypoellipticAleksandrov.Parabolic.LocalWeakTimeProduct
open private HypoellipticAleksandrov.Parabolic.integral_univ_eq_setIntegral_of_support_subset from HypoellipticAleksandrov.Parabolic.LocalWeakTimeProduct
open private HypoellipticAleksandrov.Parabolic.ae_restrict_of_forall_mem from HypoellipticAleksandrov.Parabolic.LocalWeakTimeProduct
section
open private HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_tsupport_subset from HypoellipticAleksandrov.Parabolic.WeakDerivativesUnique
private alias _sharedProof_198_2 := HypoellipticAleksandrov.Parabolic.ParabolicW12Function.velocityGradient_tsupport_subset
end


/-!
# Weak Leibniz rule for measurable-time, spatially smooth multipliers

This module proves the quantitative weak velocity product rule for bounded
jointly measurable scalar multipliers whose fixed-time spatial slices are
`C¹`.
-/

 public section



namespace HypoellipticAleksandrov.Parabolic

open Filter MeasureTheory Set
open scoped ENNReal Topology
open SpacetimeMollifier










variable {d : ℕ}




private theorem velocityGradient_eq_zero_of_eq_one_on
     {b : TimeVelocity d → ℝ} {K : HypoellipticAleksandrov.Parabolic.Region d}
    {δ : ℝ} (hδ : 0 < δ) (hb : Set.EqOn b 1 (Metric.cthickening δ K))
    (k : Fin d) {z : TimeVelocity d} (hz : z ∈ K) :
    velocityGradient b z k = 0 := by
  have heq : b =ᶠ[𝓝 z] (fun _ => (1 )) := by
    filter_upwards [Metric.ball_mem_nhds z hδ] with y hy
    apply hb
    exact Metric.mem_cthickening_of_dist_le y z δ K hz (le_of_lt hy)
  unfold velocityGradient
  rw [heq.fderiv_eq]
  simp

private theorem velocityGradient_tsupport_subset
     (b : TimeVelocity d → ℝ) (k : Fin d) :
    tsupport (fun z => velocityGradient b z k) ⊆ tsupport b := _sharedProof_198_2



variable {U : HypoellipticAleksandrov.Parabolic.Region d}




private theorem bounded_weak_mul
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
  let sharedTerm_21a18e91a1 := ((HypoellipticAleksandrov.Parabolic.timeVelocityVolume d))
  have hUmeas  := hU.measurableSet


  have hqTop  :=
    memLp_top_of_bound hqMeas Bq ((_root_.HypoellipticAleksandrov.Parabolic.ae_restrict_of_forall_mem U hUmeas hqBound))
  have hdqTop  :=
    memLp_top_of_bound hdqMeas Bdq ((_root_.HypoellipticAleksandrov.Parabolic.ae_restrict_of_forall_mem U hUmeas hdqBound))


  intro φ hφ hφCompact hφSub
  obtain ⟨δ, hδ, b, hb, hbCompact, hbSub, hbOne⟩ :=
    exists_contDiff_one_on_cthickening_tsupport_subset
      hU hφCompact.isCompact hφSub
  let Q  := fun z => b z * q z
  let DQ  := fun z => b z * dq z + q z * velocityGradient b z k

  have hQSupp  := (tsupport_mul_subset_left (f := b) (g := q)).trans hbSub
  have hDQSuppB : tsupport DQ ⊆ tsupport b := (tsupport_add _ _).trans (union_subset
      (tsupport_mul_subset_left  )
      ((tsupport_mul_subset_right (f := q)
        (g := fun z => velocityGradient b z k)).trans
          (velocityGradient_tsupport_subset b k)))
  have hDQSupp  := hDQSuppB.trans hbSub

  have hQSupport  := (subset_tsupport Q).trans hQSupp
  have hDQSupport  := (subset_tsupport DQ).trans hDQSupp
  have hbMeasU : AEStronglyMeasurable b (timeVelocityVolumeOn U) :=
    hb.continuous.aestronglyMeasurable





  obtain ⟨Cb, hCb⟩ := hb.continuous.bounded_above_of_compact_support hbCompact
  have hdbCont : Continuous (fun z => velocityGradient b z k) := by
    unfold velocityGradient
    exact (hb.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdbCompact  := HasCompactSupport.of_support_subset_isCompact hbCompact.isCompact
      ((subset_tsupport _).trans (velocityGradient_tsupport_subset b k))
  obtain ⟨Cdb, hCdb⟩ := hdbCont.bounded_above_of_compact_support hdbCompact


  have hQCompact  := HasCompactSupport.of_support_subset_isCompact hbCompact.isCompact
      ((subset_tsupport Q).trans
        (tsupport_mul_subset_left  ))
  have hQMem : MemLp Q (2 ) sharedTerm_21a18e91a1 :=
    hQCompact.memLp_of_bound (_root_.HypoellipticAleksandrov.Parabolic.aestronglyMeasurable_of_restrict_of_support_subset hUmeas (hbMeasU.mul hqMeas) hQSupport) (|Cb| * Bq) (Eventually.of_forall (by
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
  have hDQMem : MemLp DQ (2 ) sharedTerm_21a18e91a1 :=
    hDQCompact.memLp_of_bound (_root_.HypoellipticAleksandrov.Parabolic.aestronglyMeasurable_of_restrict_of_support_subset hUmeas ((hbMeasU.mul hdqMeas).add (hqMeas.mul (show AEStronglyMeasurable (fun z => velocityGradient b z k)
      (timeVelocityVolumeOn U) by
        unfold velocityGradient
        exact ((hb.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable))) hDQSupport) _
      (Eventually.of_forall (by
          intro z
          by_cases hz : z ∈ U
          · dsimp only [DQ]
            rw [Real.norm_eq_abs]
            calc
              |b z * dq z + q z * velocityGradient b z k| ≤
                  |b z| * |dq z| + |q z| * |velocityGradient b z k| := by
                    simpa only [abs_mul] using abs_add_le (b z * dq z) (q z * velocityGradient b z k)
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
  have hφTop : MemLp φ ∞ sharedTerm_21a18e91a1 :=
    hφ.continuous.memLp_top_of_hasCompactSupport hφCompact volume
  have hgradCont : Continuous (fun z => velocityGradient φ z k) := by
    unfold velocityGradient
    exact (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgradCompact  := HasCompactSupport.of_support_subset_isCompact hφCompact.isCompact
      ((subset_tsupport _).trans (velocityGradient_tsupport_subset φ k))




  have huφSupp  :=
    (Function.support_mul_subset_right u φ).trans (subset_tsupport φ |>.trans hφSub)
  have hduφSupp  :=
    (Function.support_mul_subset_right du φ).trans (subset_tsupport φ |>.trans hφSub)
  have huGradSupp  :=
    (Function.support_mul_subset_right u _).trans
      ((subset_tsupport _).trans ((velocityGradient_tsupport_subset φ k).trans hφSub))
  have huφ  :=
    (show ParabolicMemLpOn U 2 (fun z => u z * φ z) by
        simpa only using hu.mul' (hφTop.restrict U)).memLp_of_support_subset hUmeas huφSupp
  have hduφ  :=
    (show ParabolicMemLpOn U 2 (fun z => du z * φ z) by
        simpa only using hdu.mul' (hφTop.restrict U)).memLp_of_support_subset hUmeas hduφSupp

  have hQlim := _root_.HypoellipticAleksandrov.Parabolic.tendsto_integral_spacetimeMollification_mul_fixed Q
    _ hQMem ((show ParabolicMemLpOn U 2
      (fun z => u z * velocityGradient φ z k) by
        simpa only using hu.mul' ((hgradCont.memLp_top_of_hasCompactSupport hgradCompact volume).restrict U)).memLp_of_support_subset hUmeas huGradSupp)
  have hQdulim := _root_.HypoellipticAleksandrov.Parabolic.tendsto_integral_spacetimeMollification_mul_fixed Q
    _ hQMem hduφ
  have hDQlim := _root_.HypoellipticAleksandrov.Parabolic.tendsto_integral_spacetimeMollification_mul_fixed DQ
    _ hDQMem huφ
  have hsmooth (ε : ℝ) (hε : 0 < ε) :
      HasWeakVelocityPartialDerivOn U k
        (fun z => spacetimeMollification ε Q z * u z)
        (fun z => spacetimeMollification ε Q z * du z +
          u z * spacetimeMollification ε DQ z) := by
    have hQεsmooth := contDiff_spacetimeMollification hε Q
      (hQMem.locallyIntegrable (by norm_num))
    have hcomm := velocityGradient_spacetimeMollification hε k Q DQ
      (hQMem.locallyIntegrable (by norm_num))
      (hDQMem.locallyIntegrable (by norm_num)) ((show HasWeakVelocityPartialDerivOn U k Q DQ by
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
        (u z * velocityGradient φ z k)) =
      -((∫ z : TimeVelocity d, spacetimeMollification ε Q z *
          (du z * φ z)) +
        ∫ z : TimeVelocity d, spacetimeMollification ε DQ z *
          (u z * φ z)) by
          filter_upwards [self_mem_nhdsWithin] with ε hε
          exact (show ∀ ε ∈ Ioi (0 : ℝ),
            (∫ z : TimeVelocity d, spacetimeMollification ε Q z *
              (u z * velocityGradient φ z k)) =
            -((∫ z : TimeVelocity d, spacetimeMollification ε Q z *
                (du z * φ z)) +
              ∫ z : TimeVelocity d, spacetimeMollification ε DQ z *
                (u z * φ z)) by
              intro ε hε

              have hleft := _root_.HypoellipticAleksandrov.Parabolic.integral_univ_eq_setIntegral_of_support_subset hUmeas
                (fun z => spacetimeMollification ε Q z * (u z * velocityGradient φ z k))
                ((Function.support_mul_subset_right _ _).trans huGradSupp)
              have hright₁ := _root_.HypoellipticAleksandrov.Parabolic.integral_univ_eq_setIntegral_of_support_subset hUmeas
                (fun z => spacetimeMollification ε Q z * (du z * φ z))
                ((Function.support_mul_subset_right _ _).trans hduφSupp)
              have hright₂ := _root_.HypoellipticAleksandrov.Parabolic.integral_univ_eq_setIntegral_of_support_subset hUmeas
                (fun z => spacetimeMollification ε DQ z * (u z * φ z))
                ((Function.support_mul_subset_right _ _).trans huφSupp)
              rw [hleft, hright₁, hright₂]
              calc
                (∫ z in U, spacetimeMollification ε Q z *
                    (u z * velocityGradient φ z k)) =
                    ∫ z in U, (spacetimeMollification ε Q z * u z) *
                      velocityGradient φ z k := by
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


    simp [DQ, (hbOne (Metric.self_subset_cthickening (tsupport φ) hz)), (velocityGradient_eq_zero_of_eq_one_on hδ hbOne k hz)]
  rw [_root_.HypoellipticAleksandrov.Parabolic.integral_univ_eq_setIntegral_of_support_subset hUmeas _
      ((Function.support_mul_subset_right _ _).trans huGradSupp),
    _root_.HypoellipticAleksandrov.Parabolic.integral_univ_eq_setIntegral_of_support_subset hUmeas _
      ((Function.support_mul_subset_right _ _).trans hduφSupp),
    _root_.HypoellipticAleksandrov.Parabolic.integral_univ_eq_setIntegral_of_support_subset hUmeas _
      ((Function.support_mul_subset_right _ _).trans huφSupp)] at hlimEq
  calc
    (∫ z in U, (q z * u z) * velocityGradient φ z k) =
        ∫ z in U, Q z * (u z * velocityGradient φ z k) := by
          apply integral_congr_ae
          exact Eventually.of_forall fun z => by
            by_cases hdφ : velocityGradient φ z k = 0
            · simp [hdφ]
            · have hzts  :=
                (velocityGradient_tsupport_subset φ k)
                  (subset_tsupport _ (Function.mem_support.mpr hdφ))
              change q z * u z * velocityGradient φ z k =
                Q z * (u z * velocityGradient φ z k)
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

/-- A scalar that is `C¹` on an open time--velocity carrier has its literal
velocity derivative as its raw weak velocity derivative there. -/
theorem contDiffOn_one_hasWeakVelocityPartialDerivOn
     (U : HypoellipticAleksandrov.Parabolic.Region d) (hU : IsOpen U)
    (i : Fin d)
    (q : TimeVelocity d → ℝ) (hq : ContDiffOn ℝ 1 q U) :
    HasWeakVelocityPartialDerivOn U i q
      (fun z => velocityGradient q z i) := by
  let sharedTerm_b23fc06bbc := (((0, Pi.single i 1) : TimeVelocity d))
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

      exact (contDiffAt_const (x := z) (n := 1) (c := (0 : ℝ))).congr_of_eventuallyEq (by
          filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hzφ] with y hy
          simp [p, hy])
  have hpCompact : HasCompactSupport p := hφCompact.mul_left


  have hdpInt : Integrable (fun z => fderiv ℝ p z v) :=
    ((hp.continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport (hpCompact.fderiv_apply ℝ v)
  have hzero : (∫ z, fderiv ℝ p z v) = 0 := by
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := volume) (v := v)
      (f := fun _ : TimeVelocity d => (1 : ℝ)) (g := p)
      (by simp) (by simpa using hdpInt) (by simpa using (hp.continuous.integrable_of_hasCompactSupport hpCompact))
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
      fderiv ℝ p z v = 0 := by
    exact congrArg (fun L => L v)
      (fderiv_of_notMem_tsupport ℝ
        (fun hp' => hz (hφSub (tsupport_mul_subset_right hp'))))
  have hglobal : (∫ z, fderiv ℝ p z v) =
      ∫ z in U, (velocityGradient q z i * φ z +
        q z * velocityGradient φ z i) := by
    rw [← integral_indicator hU.measurableSet]
    apply integral_congr_ae
    exact Eventually.of_forall fun z => by
      by_cases hz : z ∈ U
      · simp [Set.indicator_of_mem hz, hprod z hz]
      · simp [Set.indicator_of_notMem hz, houtside z hz]
  rw [hglobal] at hzero


  rw [integral_add (by
      have hc : Continuous (fun z => velocityGradient q z i * φ z) := by
        rw [continuous_iff_continuousAt]
        intro z
        by_cases hz : z ∈ U
        · unfold velocityGradient
          exact (((hq.contDiffAt (hU.mem_nhds hz)).continuousAt_fderiv
            (by norm_num)).clm_apply
              (continuousAt_const : ContinuousAt (fun _ =>
                sharedTerm_b23fc06bbc) z)).mul
            hφ.continuous.continuousAt
        ·

          exact continuousAt_const.congr_of_eventuallyEq ((notMem_tsupport_iff_eventuallyEq.mp (fun h => hz (hφSub h))).mono fun y hy => by
            change velocityGradient q y i * φ y = 0
            simp [hy])
      exact (hc.integrable_of_hasCompactSupport hφCompact.mul_left).integrableOn) (by
      have hc : Continuous (fun z => q z * velocityGradient φ z i) := by
        rw [continuous_iff_continuousAt]
        intro z
        by_cases hz : z ∈ U
        · exact (hq.contDiffAt (hU.mem_nhds hz)).continuousAt.mul
            ((hφ.continuous_fderiv (by simp)).clm_apply
              (continuous_const : Continuous (fun _ =>
                sharedTerm_b23fc06bbc))).continuousAt
        ·

          exact continuousAt_const.congr_of_eventuallyEq (((notMem_tsupport_iff_eventuallyEq.mp (fun h => hz (hφSub h))).fderiv (𝕜 := ℝ)).mono fun y hy => by
            change q y * fderiv ℝ φ y sharedTerm_b23fc06bbc = 0
            rw [hy]
            simp)
      exact (hc.integrable_of_hasCompactSupport
        ((hφCompact.fderiv_apply ℝ
          sharedTerm_b23fc06bbc).mul_left)).integrableOn)] at hzero
  linarith

/-- A bounded `C¹` multiplier obeys the weak velocity Leibniz rule on an
arbitrary open carrier, with sharp componentwise `L²` bounds. -/
theorem velocityC1_mul_hasWeakVelocityPartialDerivOn_memLp_eLpNorm_le
     {U : HypoellipticAleksandrov.Parabolic.Region d} (hU : IsOpen U)
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
      unfold velocityGradient
      exact ((hqC1.contDiffAt (hU.mem_nhds hz)).continuousAt_fderiv
        (by norm_num)).clm_apply
          (continuousAt_const : ContinuousAt (fun _ =>
            ((0, Pi.single i 1) : TimeVelocity d)) z)
        |>.continuousWithinAt
    exact hc.aestronglyMeasurable hUmeas
  have hqAE : ∀ᵐ z ∂timeVelocityVolumeOn U, |q z| ≤ Bq :=
    _root_.HypoellipticAleksandrov.Parabolic.ae_restrict_of_forall_mem U hUmeas hqBound

  obtain ⟨hqu, hquNorm⟩ := _root_.HypoellipticAleksandrov.Parabolic.toReal_eLpNorm_mul_le hBq hqMeas hu hqAE
  obtain ⟨hqdui, hqduiNorm⟩ := _root_.HypoellipticAleksandrov.Parabolic.toReal_eLpNorm_mul_le hBq hqMeas hdui hqAE
  obtain ⟨hdiu, hdiuNorm⟩ := _root_.HypoellipticAleksandrov.Parabolic.toReal_eLpNorm_mul_le hBdi hdiMeas hu (_root_.HypoellipticAleksandrov.Parabolic.ae_restrict_of_forall_mem U hUmeas hdiBound)



  have hmulWeak : HasWeakVelocityPartialDerivOn U i
      (fun z => q z * u z)
      (((fun z => q z * dui z + velocityGradient q z i * u z))) :=
    bounded_weak_mul hU i Bq Bdi hBq hBdi q (fun z => velocityGradient q z i) u dui
      hqMeas hdiMeas hqBound hdiBound (contDiffOn_one_hasWeakVelocityPartialDerivOn U hU i q hqC1) hu hdui hweak
  exact ⟨hdiMeas, hqu, (hqdui.add hdiu), hmulWeak, hquNorm, (by

      have hreal := ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr ⟨hqdui.eLpNorm_ne_top, hdiu.eLpNorm_ne_top⟩) (eLpNorm_add_le (by norm_num))
      rw [ENNReal.toReal_add hqdui.eLpNorm_ne_top hdiu.eLpNorm_ne_top] at hreal
      exact hreal.trans (add_le_add hqduiNorm hdiuNorm))⟩

end HypoellipticAleksandrov.Parabolic
