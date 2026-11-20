module

public import HypoellipticAleksandrov.Parabolic.WeakJetProduct
public import HypoellipticAleksandrov.Parabolic.TimeVelocitySmoothCompactPlateau
public import HypoellipticAleksandrov.Parabolic.WeakDerivativesCompactGlobalization
public import HypoellipticAleksandrov.Parabolic.WeakDerivativeSpacetimeMollification
public import HypoellipticAleksandrov.Parabolic.SpacetimeMollifierL2
public import HypoellipticAleksandrov.Analysis.L2ProductConvergence
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import HypoellipticAleksandrov.Analysis.BoundedMultiplierLp

/-!
# Local weak-time product rule for jointly `C¹` multipliers

This module proves the raw weak time derivative of a jointly `C¹` scalar and
the quantitative weak time product rule for bounded jointly `C¹` multipliers.
-/

@[expose] public section

noncomputable section

namespace HypoellipticAleksandrov.Parabolic

open Filter Function MeasureTheory Set Topology
open scoped ENNReal Topology
open SpacetimeMollifier
open HypoellipticAleksandrov.Analysis

private theorem tendsto_integral_spacetimeMollification_mul_fixed
    {d : ℕ} (f g : TimeVelocity d → ℝ)
    (hf : MemLp f (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d)))
    (hg : MemLp g (2 : ℝ≥0∞) (volume : Measure (TimeVelocity d))) :
    Tendsto
      (fun ε : ℝ => ∫ z : TimeVelocity d,
        spacetimeMollification ε f z * g z ∂volume)
      (𝓝[>] 0) (𝓝 (∫ z : TimeVelocity d, f z * g z ∂volume)) := (SpacetimeMollifierL2.spacetimeMollification_strongL2 hf).pairing (StrongL2Limit.const hg)

private theorem integral_univ_eq_setIntegral_of_support_subset
    {d : ℕ} {U : Set (TimeVelocity d)} 
    (f : TimeVelocity d → ℝ) (hsupp : Function.support f ⊆ U) :
    (∫ z : TimeVelocity d, f z ∂volume) = ∫ z in U, f z ∂volume := (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
    notMem_support.mp (fun hn => hz (hsupp hn))).symm

section
variable {d : ℕ} {U : Set (TimeVelocity d)} (hU : IsOpen U)
include hU

private theorem continuousOn_fderiv_apply_one {q : TimeVelocity d → ℝ}
    (hq : ContDiffOn ℝ 1 q U) (e : TimeVelocity d) :
    ContinuousOn (fun z => fderiv ℝ q z e) U :=
  fun z hz => (((hq.contDiffAt (hU.mem_nhds hz)).continuousAt_fderiv (by norm_num)).clm_apply
    continuousAt_const).continuousWithinAt

/-- A `C¹` representative has its classical directional derivative as a weak derivative. -/
theorem contDiffOn_one_hasWeakFDerivApplyOn (e : TimeVelocity d)
    {q : TimeVelocity d → ℝ} (hq : ContDiffOn ℝ 1 q U) :
    HasWeakFDerivApplyOn U e q (fun z => fderiv ℝ q z e) := by
  intro φ hφ hc hs
  have hInt {f g : TimeVelocity d → ℝ} (hf : ContinuousOn f U)
      (hg : Continuous g) (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ U) :
      Integrable (f * g) volume :=
    (integrableOn_iff_integrable_of_support_subset
      ((support_mul_subset_right f g).trans ((subset_tsupport g).trans hgs))).mp
      (integrable_restrict_mul_of_locallyIntegrableOn (hf.locallyIntegrableOn hU.measurableSet) hg hgc hgs)
  have hds := (tsupport_fderiv_apply_subset ℝ (f := φ) e).trans hs
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (hInt (continuousOn_fderiv_apply_one hU hq e) hφ.continuous hc hs)
    (hInt hq.continuousOn ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hc.fderiv_apply ℝ e) hds) (hInt hq.continuousOn hφ.continuous hc hs)
    (fun z hz => (hq.contDiffAt (hU.mem_nhds (hs hz))).differentiableAt (by norm_num))
    (fun z _ => hφ.differentiable (by simp) z)
  rwa [integral_univ_eq_setIntegral_of_support_subset _
      ((support_mul_subset_right _ _).trans ((subset_tsupport _).trans hds)),
    integral_univ_eq_setIntegral_of_support_subset _
      ((support_mul_subset_right _ _).trans ((subset_tsupport _).trans hs))] at h

/-- A bounded coefficient with bounded weak derivative obeys the weak product rule. -/
private theorem bounded_weak_mul {e : TimeVelocity d}
    {q dq u du : TimeVelocity d → ℝ}
    (hq : ParabolicMemLpOn U ∞ q) (hdq : ParabolicMemLpOn U ∞ dq)
    (hqWeak : HasWeakFDerivApplyOn U e q dq)
    (hu : ParabolicMemLpOn U 2 u) (hdu : ParabolicMemLpOn U 2 du)
    (hweak : HasWeakFDerivApplyOn U e u du) :
    HasWeakFDerivApplyOn U e (q * u) (q * du + dq * u) := by
  intro φ hφ hφc hφU
  let D (f : TimeVelocity d → ℝ) := fun z => fderiv ℝ f z e
  have hD {f} (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous (D f) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDs (f) : tsupport (D f) ⊆ tsupport f := tsupport_fderiv_apply_subset ℝ e
  have hloc {f : TimeVelocity d → ℝ} {p : ℝ≥0∞} (hf : ParabolicMemLpOn U p f) (hp : 1 ≤ p) :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hf.locallyIntegrable hp)
  obtain ⟨δ, hδ, b, hb, hbc, hbU, hb1⟩ :=
    exists_contDiff_one_on_cthickening_tsupport_subset hU hφc.isCompact hφU
  let Q := b * q
  let DQ := b * dq + q * D b
  have hQs : tsupport Q ⊆ U := tsupport_mul_subset_left.trans hbU
  have hDQs : tsupport DQ ⊆ U := (tsupport_add _ _).trans (union_subset
    (tsupport_mul_subset_left.trans hbU) (tsupport_mul_subset_right.trans ((hDs b).trans hbU)))
  have hQWeak : HasWeakFDerivApplyOn univ e Q DQ :=
    (hqWeak.mul_contDiff hb (hloc hq (by simp)) (hloc hdq (by simp))).univ_of_tsupport_subset hU hQs hDQs
  have hb2 : ParabolicMemLpOn U 2 b := hb.continuous.memLp_of_hasCompactSupport hbc
  have hDb2 : ParabolicMemLpOn U 2 (D b) := (hD hb).memLp_of_hasCompactSupport (hbc.fderiv_apply ℝ e)
  have hQ : MemLp Q 2 volume := ParabolicMemLpOn.memLp_of_support_subset hU.measurableSet (hb2.mul hq)
    ((subset_tsupport _).trans hQs)
  have hDQ : MemLp DQ 2 volume := ParabolicMemLpOn.memLp_of_support_subset hU.measurableSet
    ((hb2.mul hdq).add (hq.mul hDb2)) ((subset_tsupport _).trans hDQs)
  have htest {f g : TimeVelocity d → ℝ} (hf : ParabolicMemLpOn U 2 f)
      (hg : Continuous g) (hgc : HasCompactSupport g) (hgs : tsupport g ⊆ U) :
      MemLp (f * g) 2 volume :=
    ParabolicMemLpOn.memLp_of_support_subset hU.measurableSet
      (hf.mul (hg.memLp_top_of_hasCompactSupport hgc (timeVelocityVolumeOn U))) ((support_mul_subset_right _ _).trans ((subset_tsupport _).trans hgs))
  have hp := htest hu (hD hφ) (hφc.fderiv_apply ℝ e) ((hDs φ).trans hφU)
  have hv := htest hdu hφ.continuous hφc hφU
  have hw := htest hu hφ.continuous hφc hφU
  let I (f g : TimeVelocity d → ℝ) := ∫ z in U, f z * g z
  have hconv (f g : TimeVelocity d → ℝ) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume)
      (hgs : Function.support g ⊆ U) :
      Tendsto (fun ε => I (spacetimeMollification ε f) g) (𝓝[>] 0) (𝓝 (I f g)) := by
    have hpair (F : TimeVelocity d → ℝ) : (∫ z, F z * g z) = I F g :=
      integral_univ_eq_setIntegral_of_support_subset _ ((support_mul_subset_right _ _).trans hgs)
    simpa only [hpair] using tendsto_integral_spacetimeMollification_mul_fixed f g hf hg
  have hs {f g : TimeVelocity d → ℝ} (hgs : tsupport g ⊆ U) : Function.support (f * g) ⊆ U :=
    (support_mul_subset_right _ _).trans ((subset_tsupport _).trans hgs)
  have hsplit (F G : TimeVelocity d → ℝ) (hF : MemLp F 2 volume) (hG : MemLp G 2 volume) :
      (∫ z in U, (F z * du z + G z * u z) * φ z) = I F (du * φ) + I G (u * φ) := by
    simpa only [I, Pi.mul_apply, add_mul, mul_assoc] using
      integral_add ((hF.integrable_mul hv).restrict (s := U)) ((hG.integrable_mul hw).restrict (s := U))
  have hEq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), I (spacetimeMollification ε Q) (u * D φ) =
      -(I (spacetimeMollification ε Q) (du * φ) + I (spacetimeMollification ε DQ) (u * φ)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hm := contDiff_spacetimeMollification hε Q (hQ.locallyIntegrable (by norm_num))
    have h := (hweak.mul_contDiff hm (hloc hu (by norm_num)) (hloc hdu (by norm_num))) φ hφ hφc hφU
    simp_rw [fderiv_spacetimeMollification_apply hε Q DQ (hQ.locallyIntegrable (by norm_num))
      (hDQ.locallyIntegrable (by norm_num)) e hQWeak] at h
    have h' : I (spacetimeMollification ε Q) (u * D φ) =
        -∫ z in U, (spacetimeMollification ε Q z * du z + spacetimeMollification ε DQ z * u z) * φ z := by
      simpa only [I, D, Pi.mul_apply, mul_assoc, mul_comm (u _)] using h
    rw [h', hsplit _ _ (SpacetimeMollifierL2.spacetimeMollification_memLp hε Q hQ)
      (SpacetimeMollifierL2.spacetimeMollification_memLp hε DQ hDQ)]
  have hLim := tendsto_nhds_unique (hconv Q _ hQ hp (hs ((hDs φ).trans hφU)))
    (((hconv Q _ hQ hv (hs hφU)).add (hconv DQ _ hDQ hw (hs hφU))).neg.congr' (hEq.mono fun _ h => h.symm))
  have hb_eq {z : TimeVelocity d} (hz : z ∈ tsupport φ) : b =ᶠ[𝓝 z] 1 := by
    filter_upwards [Metric.isOpen_thickening.mem_nhds (Metric.self_subset_thickening hδ _ hz)] with w hw
    exact hb1 (Metric.thickening_subset_cthickening _ _ hw)
  have hQeq {z : TimeVelocity d} (hz : z ∈ tsupport φ) : Q z = q z := by
    simp [Q, (hb_eq hz).eq_of_nhds]
  have hDQeq {z : TimeVelocity d} (hz : z ∈ tsupport φ) : DQ z = dq z := by
    have hbz := (hb_eq hz).fderiv_eq (𝕜 := ℝ)
    simp [DQ, D, hbz, (hb_eq hz).eq_of_nhds]
  have hchange {f g w : TimeVelocity d → ℝ} (hfg : Set.EqOn f g (tsupport φ))
      (hw : Function.support w ⊆ tsupport φ) : I f w = I g w := by
    refine integral_congr_ae (.of_forall fun z => ?_)
    by_cases hz : z ∈ tsupport φ
    · simp only [hfg hz]
    · simp [notMem_support.mp (fun h => hz (hw h))]
  have hleft : I Q (u * D φ) = I q (u * D φ) := hchange (fun _ hz => hQeq hz)
    ((support_mul_subset_right u (D φ)).trans ((subset_tsupport _).trans (hDs φ)))
  have hright : (∫ z in U, (DQ z * u z + Q z * du z) * φ z) =
      ∫ z in U, (dq z * u z + q z * du z) * φ z := by
    refine integral_congr_ae (.of_forall fun z => ?_)
    by_cases hz : z ∈ tsupport φ
    · simp only [hDQeq hz, hQeq hz]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  rw [hleft, ← hsplit Q DQ hQ hDQ] at hLim
  simpa only [I, D, Pi.mul_apply, Pi.add_apply, ← mul_assoc, add_comm] using
    hLim.trans (congrArg Neg.neg (by simpa only [add_comm] using hright))

/-- The weak product rule with componentwise `L²` bounds for a `C¹` coefficient. -/
theorem fderivApplyC1_mul_hasWeakFDerivApplyOn_memLp_eLpNorm_le (e : TimeVelocity d)
    (Bq Bdq : ℝ) (hBq : 0 ≤ Bq) (hBdq : 0 ≤ Bdq)
    (q : TimeVelocity d → ℝ) (hq : ContDiffOn ℝ 1 q U)
    (hqBound : ∀ z ∈ U, |q z| ≤ Bq) (hdqBound : ∀ z ∈ U, |fderiv ℝ q z e| ≤ Bdq)
    (u du : TimeVelocity d → ℝ) (hu : ParabolicMemLpOn U 2 u) (hdu : ParabolicMemLpOn U 2 du)
    (hweak : HasWeakFDerivApplyOn U e u du) :
    let dq := fun z => fderiv ℝ q z e
    let μ := timeVelocityVolumeOn U
    AEStronglyMeasurable dq μ ∧ MemLp (q * u) 2 μ ∧ MemLp (q * du + dq * u) 2 μ ∧
      HasWeakFDerivApplyOn U e (q * u) (q * du + dq * u) ∧
      (eLpNorm (q * u) 2 μ).toReal ≤ Bq * (eLpNorm u 2 μ).toReal ∧
      (eLpNorm (q * du + dq * u) 2 μ).toReal ≤
        Bq * (eLpNorm du 2 μ).toReal + Bdq * (eLpNorm u 2 μ).toReal := by
  intro dq μ
  have hqM := hq.continuousOn.aestronglyMeasurable (μ := volume) hU.measurableSet
  have hdqM := (continuousOn_fderiv_apply_one hU hq e).aestronglyMeasurable (μ := volume) hU.measurableSet
  have hqB := ae_restrict_of_forall_mem (μ := volume) hU.measurableSet hqBound
  have hdqB := ae_restrict_of_forall_mem (μ := volume) hU.measurableSet hdqBound
  obtain ⟨hqu, hquN⟩ := memLp_mul_eLpNorm_toReal_le_of_ae_abs_le hBq hqM hu hqB
  obtain ⟨hqdu, hqduN⟩ := memLp_mul_eLpNorm_toReal_le_of_ae_abs_le hBq hqM hdu hqB
  obtain ⟨hdqu, hdquN⟩ := memLp_mul_eLpNorm_toReal_le_of_ae_abs_le hBdq hdqM hu hdqB
  refine ⟨hdqM, hqu, hqdu.add hdqu, ?_, hquN, ?_⟩
  · exact bounded_weak_mul hU
      (memLp_top_of_bound hqM Bq (by simpa only [Real.norm_eq_abs] using hqB))
      (memLp_top_of_bound hdqM Bdq (by simpa only [Real.norm_eq_abs] using hdqB))
      (contDiffOn_one_hasWeakFDerivApplyOn hU e hq) hu hdu hweak
  · have hsum := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hqdu.eLpNorm_ne_top, hdqu.eLpNorm_ne_top⟩)
      (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2))
    rw [ENNReal.toReal_add hqdu.eLpNorm_ne_top hdqu.eLpNorm_ne_top] at hsum
    exact hsum.trans (add_le_add hqduN hdquN)

end

/-- A scalar that is `C¹` on an open time--velocity carrier has its literal
 time derivative as its raw weak time derivative there. -/
theorem contDiffOn_one_hasWeakTimeDerivOn
    {d : ℕ} (U : Set (TimeVelocity d)) (hU : IsOpen U)
    (q : TimeVelocity d → ℝ) (hq : ContDiffOn ℝ 1 q U) :
    HasWeakTimeDerivOn U q (timeDerivative q) := contDiffOn_one_hasWeakFDerivApplyOn hU (1, 0) hq

end HypoellipticAleksandrov.Parabolic
