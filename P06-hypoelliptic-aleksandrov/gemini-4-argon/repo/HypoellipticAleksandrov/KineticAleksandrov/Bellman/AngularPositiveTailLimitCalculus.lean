module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularPositiveTailSecondMoment
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularPositiveTailGrowth
import Mathlib.Tactic
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularIntegratedCalculus
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularPositiveTailMoments
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularDensitiesMoments
import HypoellipticAleksandrov.KineticAleksandrov.Bellman.AngularPositiveTailFirstMoment
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # The actual positive-tail limit and its flux normalization -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set Filter
open scoped Topology

/- A nonnegative integrated angular solution has zero linear growth at positive infinity. -/
theorem bellmanAngularPositiveTail_limit (R β ) (hR : 1 ≤ R) (hβ : 3 ≤ β)
    (f h J : ℝ → ℝ) (hf : LocallyIntegrable f volume)
    (hn : ∀ᵐ z ∂volume, 0 ≤ f z) (hh : ∀ y : ℝ, 0 ≤ h y)
    (hcomp : ∀ᵐ y ∂volume, h y ≤ R * f y)
    (he : ∀ y : ℝ, h y = h 0 + J 0 * y - ((β - 2) / 3) * y *
      bellmanAngularFirstMoment f y + ((β - 3) / 3) * bellmanAngularSecondMoment f y)
    (htail : IntegrableOn (fun y => f y * |y| ^ (β - 4)) {y : ℝ | 2 < |y|} volume) :
    ∃ L : ℝ, 0 ≤ L ∧ Tendsto (bellmanAngularFirstMoment f) atTop (𝓝 L) ∧
      Tendsto (fun y => bellmanAngularSecondMoment f y / y) atTop (𝓝 0) ∧
      J 0 = ((β - 2) / 3) * L ∧ ∀ y : ℝ, 0 < y → h 0 ≤ h y := by
  have hi := bellmanAngularFirstMoment_integrable β f h J hβ hf hn hh he
  let L := ∫ z in Ioi 0, z * f z
  have hL : 0 ≤ ∫ z in Ioi 0, z * f z := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hn] with z hz hfz
    exact mul_nonneg hz.le hfz
  have hI := bellmanAngularFirstMoment_tendsto f hi
  have hM : Tendsto (fun y => bellmanAngularSecondMoment f y / y) atTop (𝓝 0) := by
    let G := fun y : ℝ => (Iic y).indicator (fun z => (z / y) * (z * f z))
    have hmeas : ∀ᶠ y : ℝ in atTop,
        AEStronglyMeasurable (G y) (volume.restrict (Ioi 0)) := by
      apply Eventually.of_forall
      intro y
      exact ((measurable_id.div_const y).aestronglyMeasurable.mul
        hi.aestronglyMeasurable).indicator measurableSet_Iic
    have hbound : ∀ᶠ y : ℝ in atTop, ∀ᵐ z ∂volume.restrict (Ioi 0),
        ‖G y z‖ ≤ ‖z * f z‖ := by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      by_cases hzy : z ≤ y
      · rw [show G y z = (z / y) * (z * f z) from indicator_of_mem (show z ∈ Iic y from hzy) _]
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hz.le (by linarith))]
        apply mul_le_of_le_one_left (norm_nonneg _)
        exact (div_le_one (by linarith : 0 < y)).mpr hzy
      · rw [show G y z = 0 from indicator_of_notMem (show z ∉ Iic y from hzy) _]
        simpa only [norm_zero] using norm_nonneg (z * f z)
    have hlim : ∀ᵐ z ∂volume.restrict (Ioi 0),
        Tendsto (fun y => G y z) atTop (𝓝 (0 : ℝ)) := by
      apply ae_of_all
      intro z
      have he : (fun y => G y z) =ᶠ[atTop] (fun y => (z / y) * (z * f z)) := by
        filter_upwards [eventually_ge_atTop z] with y hy
        exact indicator_of_mem (show z ∈ Iic y from hy) _
      have hr : Tendsto (fun y : ℝ => z / y) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have ht := hr.mul_const (z * f z)
      simpa only [zero_mul] using ht.congr' he.symm
    have ht := tendsto_integral_filter_of_dominated_convergence
      (fun z => ‖z * f z‖) hmeas hbound hi.norm hlim
    simp only [integral_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    dsimp [G]
    rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      show Iic y ∩ Ioi (0 : ℝ) = Ioc 0 y from
        Set.ext (fun z => by simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_Ioc]; tauto),
      bellmanAngularSecondMoment, intervalIntegral.integral_of_le (by linarith : 0 ≤ y)]
    rw [← integral_div]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro z _
    ring
  have h0 : Tendsto (fun y : ℝ => h 0 / y) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hdiv : Tendsto (fun y => h y / y) atTop (𝓝 (J 0 - ((β - 2) / 3) * L)) := by
    have ht := ((h0.add (tendsto_const_nhds (x := J 0))).sub
      (hI.const_mul ((β - 2) / 3))).add (hM.const_mul ((β - 3) / 3))
    simp only [zero_add, mul_zero, add_zero] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    rw [he y]
    field_simp
  have hlower : 0 ≤ J 0 - ((β - 2) / 3) * L := by
    apply ge_of_tendsto hdiv
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    exact div_nonneg (hh y) hy
  have hz : J 0 - ((β - 2) / 3) * L = 0 := by
    by_contra hne
    have hp : 0 < J 0 - ((β - 2) / 3) * L := lt_of_le_of_ne hlower (Ne.symm hne)
    exact bellmanAngularTail_no_positive_linear_limit R β hR hβ f h htail hcomp _ hp hdiv
  have hj : J 0 = ((β - 2) / 3) * L := by linarith
  refine ⟨L, hL, hI, hM, hj, ?_⟩
  intro y hy
  have hIy : bellmanAngularFirstMoment f y ≤ L := by
    rw [bellmanAngularFirstMoment, intervalIntegral.integral_of_le hy.le]
    apply setIntegral_mono_set hi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae hn] with z hz hnz
      exact mul_nonneg hz.le hnz
    · exact Eventually.of_forall (fun z hz => hz.1)
  have hMy := bellmanAngularSecondMoment_nonneg hn hy.le
  rw [he y, hj]
  have hc : 0 ≤ (β - 2) / 3 := by linarith
  have hd : 0 ≤ (β - 3) / 3 := by linarith
  have hp := mul_nonneg (mul_nonneg hc hy.le) (sub_nonneg.mpr hIy)
  have hq := mul_nonneg hd hMy
  nlinarith

end HypoellipticAleksandrov.KineticAleksandrov
