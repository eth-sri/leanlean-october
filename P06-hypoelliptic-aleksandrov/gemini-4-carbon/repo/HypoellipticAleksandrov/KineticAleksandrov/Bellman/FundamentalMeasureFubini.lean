module

public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureJets
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureMajorant
import Mathlib.Tactic
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureTimeScaling
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasureRadon
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Order.LeftRight
public import HypoellipticAleksandrov.KineticAleksandrov.Bellman.FundamentalMeasurePlaneScaling
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod

@[expose] public noncomputable section

namespace HypoellipticAleksandrov.KineticAleksandrov
open MeasureTheory Set Filter
open scoped Topology

/-- The scalar time chart of the literal positive-time Gaussian. -/
def bellmanGaussianTimeChart (s : ℝ) (q : ℝ × ℝ) : ℝ :=
  Real.sqrt 3 / (2 * Real.pi * s ^ 2) *
    Real.exp (-3 * q.1 ^ 2 / s ^ 3 + 3 * q.1 * q.2 / s ^ 2 - q.2 ^ 2 / s)

/-- The coefficient of the Gaussian in its time derivative. -/
def bellmanGaussianTimeCoefficient (s : ℝ) (q : ℝ × ℝ) : ℝ :=
  9 * q.1 ^ 2 / s ^ 4 - 6 * q.1 * q.2 / s ^ 3 + q.2 ^ 2 / s ^ 2 - 2 / s

/-- A continuous polynomial bound for the time-derivative coefficient. -/
def bellmanGaussianTimeWeight (q : ℝ × ℝ) : ℝ :=
  9 * q.1 ^ 2 + 6 * |q.1 * q.2| + q.2 ^ 2 + 2

/-- The time chart has the polynomial Gaussian derivative on positive time. -/
theorem hasDerivAt_bellmanGaussianTimeChart (t : BellmanPositiveTime) (q : ℝ × ℝ) :
    HasDerivAt (fun s => bellmanGaussianTimeChart s q)
      (bellmanGaussianTimeCoefficient t.val q * bellmanGaussianKernel t q) t.val := by
  convert hasDerivAt_bellmanGaussianKernel_time t q.1 q.2 using 1
  · rfl
  · rw [(hasDerivAt_bellmanGaussianKernel_position t q.1 q.2).deriv,
      (hasDerivAt_deriv_bellmanGaussianKernel_velocity t q.1 q.2).deriv]
    dsimp [bellmanGaussianTimeCoefficient]
    field_simp [ne_of_gt t.property]
    ring

/-- Sixth-order exponential decay dominates the inverse-power singularity. -/
theorem bellman_exp_neg_le_inv_six (y : ℝ) (hy : 0 < y) :
    Real.exp (-y) ≤ 720 / y ^ 6 := by
  have hm := mul_le_mul_of_nonneg_right (Real.pow_div_factorial_le_exp y hy.le 6) (Real.exp_pos (-y)).le
  have hexp : Real.exp y * Real.exp (-y) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [hexp] at hm
  norm_num at hm
  apply (le_div_iff₀ (pow_pos hy 6)).mpr
  nlinarith only [hm]

/-- On sets away from the pole, the small-time Gaussian is bounded by a fourth power. -/
theorem bellmanGaussianKernel_le_smallTime_four (t : BellmanPositiveTime)
    (ht : t.val ≤ 1) (q : ℝ × ℝ) (a : ℝ) (ha : 0 < a)
    (hq : a ≤ q.1 ^ 2 + q.2 ^ 2) :
    bellmanGaussianKernel t q ≤
      (360 * 8 ^ 6 * Real.sqrt 3 / (Real.pi * a ^ 6)) * t.val ^ 4 := by
  have htp := t.property
  have hE : bellmanGaussianExponent t q ≤ -a / (8 * t.val) := by
    refine (bellmanGaussianExponent_le_smallTime t ht q).trans ?_
    exact div_le_div_of_nonneg_right (neg_le_neg hq) (by positivity)
  have he : Real.exp (bellmanGaussianExponent t q) ≤
      720 / (a / (8 * t.val)) ^ 6 := by
    refine (Real.exp_le_exp.mpr hE).trans ?_
    rw [neg_div]
    exact bellman_exp_neg_le_inv_six _ (by positivity)
  unfold bellmanGaussianKernel
  refine (mul_le_mul_of_nonneg_left he (show 0 ≤ Real.sqrt 3 / (2 * Real.pi * t.val ^ 2) by positivity)).trans_eq ?_
  field_simp [ne_of_gt t.property]
  ring





/-- Time decomposition of the Gaussian derivative bound, for a squared-distance lower bound a. -/
def bellmanDerivativeMajorant (a : ℝ) (t : ℝ) : ℝ :=
  (Ioc (0 : ℝ) 1).indicator
    (fun _ => 360 * 8 ^ 6 * Real.sqrt 3 / (Real.pi * a ^ 6)) t +
  (Ioi (1 : ℝ)).indicator (fun s => Real.sqrt 3 / (2 * Real.pi) * s ^ (-2 : ℝ)) t

/-- The derivative majorant is integrable on the positive half-line. -/
theorem integrable_bellmanDerivativeMajorant (a : ℝ) :
    Integrable (fun t : BellmanPositiveTime => bellmanDerivativeMajorant a t.val)
      bellmanPositiveTimeVolume := by
  have hsmall : IntegrableOn (fun _ : ℝ => 360 * 8 ^ 6 * Real.sqrt 3 / (Real.pi * a ^ 6))
      (Ioc 0 1) := integrableOn_const measure_Ioc_lt_top.ne
  have hlarge : IntegrableOn (fun s : ℝ => Real.sqrt 3 / (2 * Real.pi) *
      s ^ (-2 : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul _
  have hi :=
    (hsmall.integrable_indicator measurableSet_Ioc).add
      (hlarge.integrable_indicator measurableSet_Ioi)
  have hmap : Measure.map (Subtype.val : BellmanPositiveTime → ℝ)
      bellmanPositiveTimeVolume = volume.restrict (Ioi 0) := by
    unfold bellmanPositiveTimeVolume
    convert! map_comap_subtype_coe (s := Ioi 0) measurableSet_Ioi
      (volume.restrict (Ioi (0 : ℝ))) using 1
    rw [Measure.restrict_restrict measurableSet_Ioi, inter_self]
  have h : Integrable (bellmanDerivativeMajorant a)
      (Measure.map (Subtype.val : BellmanPositiveTime → ℝ) bellmanPositiveTimeVolume) := by
    rw [hmap]
    exact hi.restrict
  exact (MeasurableEmbedding.subtype_coe (s := Ioi 0)
    measurableSet_Ioi).integrable_map_iff.mp h

/-- The actual Gaussian time derivative has an integrable separated bound. -/
theorem bellmanGaussianTimeDerivative_le_majorant (a : ℝ) (ha : 0 < a)
    (q : ℝ × ℝ) (hq : a ≤ q.1 ^ 2 + q.2 ^ 2) (t : BellmanPositiveTime) :
    ‖bellmanGaussianTimeCoefficient t.val q * bellmanGaussianKernel t q‖ ≤
      bellmanGaussianTimeWeight q * bellmanDerivativeMajorant a t.val    := by
  have bellmanGaussianTimeCoefficient_large (ht : 1 ≤ t.val) :
      |bellmanGaussianTimeCoefficient t.val q| ≤ bellmanGaussianTimeWeight q := by
    have hp (n : ℕ) : 1 ≤ t.val ^ n := one_le_pow₀ ht
    unfold bellmanGaussianTimeCoefficient
    calc
      |9 * q.1 ^ 2 / t.val ^ 4 - 6 * q.1 * q.2 / t.val ^ 3 +
          q.2 ^ 2 / t.val ^ 2 - 2 / t.val|
          ≤ |9 * q.1 ^ 2 / t.val ^ 4| + |6 * q.1 * q.2 / t.val ^ 3| +
            |q.2 ^ 2 / t.val ^ 2| + |2 / t.val| := by
              have h1 := abs_sub (9 * q.1 ^ 2 / t.val ^ 4)
                (6 * q.1 * q.2 / t.val ^ 3)
              have h2 := abs_add_le
                (9 * q.1 ^ 2 / t.val ^ 4 - 6 * q.1 * q.2 / t.val ^ 3)
                (q.2 ^ 2 / t.val ^ 2)
              have h3 := abs_sub
                (9 * q.1 ^ 2 / t.val ^ 4 - 6 * q.1 * q.2 / t.val ^ 3 +
                  q.2 ^ 2 / t.val ^ 2) (2 / t.val)
              linarith only [h1, h2, h3]
      _ ≤ bellmanGaussianTimeWeight q := by
        simp only [abs_div, abs_mul, abs_of_nonneg (sq_nonneg q.1),
          abs_of_nonneg (sq_nonneg q.2), abs_of_pos t.property,
          abs_of_nonneg (pow_nonneg t.property.le 2),
          abs_of_nonneg (pow_nonneg t.property.le 3),
          abs_of_nonneg (pow_nonneg t.property.le 4)]
        norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        rw [mul_assoc 6, ← abs_mul]
        exact add_le_add (add_le_add (add_le_add
          (div_le_self (by positivity) (hp 4))
          (div_le_self (by positivity) (hp 3)))
          (div_le_self (sq_nonneg _) (hp 2))) (div_le_self (by norm_num) ht)
  have bellmanGaussianTimeCoefficient_small (ht : t.val ≤ 1) :
      |bellmanGaussianTimeCoefficient t.val q| ≤
      bellmanGaussianTimeWeight q / t.val ^ 4 := by
    have ht2 : t.val ^ 2 ≤ 1 := by nlinarith only [t.property, ht]
    have ht3 : t.val ^ 3 ≤ 1 := by
      calc t.val ^ 3 = t.val ^ 2 * t.val := by ring
           _ ≤ 1 * 1 := mul_le_mul ht2 ht t.property.le (by norm_num)
           _ = 1 := one_mul _
    have he : bellmanGaussianTimeCoefficient t.val q * t.val ^ 4 =
        9 * q.1 ^ 2 - 6 * q.1 * q.2 * t.val + q.2 ^ 2 * t.val ^ 2 - 2 * t.val ^ 3 := by
      dsimp [bellmanGaussianTimeCoefficient]
      field_simp [ne_of_gt t.property]
    apply (le_div_iff₀ (pow_pos t.property 4)).mpr
    rw [← abs_of_pos (pow_pos t.property 4), ← abs_mul, he]
    calc
      |9 * q.1 ^ 2 - 6 * q.1 * q.2 * t.val + q.2 ^ 2 * t.val ^ 2 - 2 * t.val ^ 3|
          ≤ |9 * q.1 ^ 2| + |6 * q.1 * q.2 * t.val| +
            |q.2 ^ 2 * t.val ^ 2| + |2 * t.val ^ 3| := by
              have h1 := abs_sub (9 * q.1 ^ 2) (6 * q.1 * q.2 * t.val)
              linarith only [h1, (abs_add_le (9 * q.1 ^ 2 - 6 * q.1 * q.2 * t.val) (q.2 ^ 2 * t.val ^ 2)), (abs_sub (9 * q.1 ^ 2 - 6 * q.1 * q.2 * t.val + q.2 ^ 2 * t.val ^ 2) (2 * t.val ^ 3))]
      _ ≤ bellmanGaussianTimeWeight q := by
        simp only [abs_mul, abs_of_nonneg (sq_nonneg q.1),
          abs_of_nonneg (sq_nonneg q.2), abs_of_pos t.property,
          abs_of_nonneg (pow_nonneg t.property.le 2),
          abs_of_nonneg (pow_nonneg t.property.le 3)]
        norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 9),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        have hx : |q.1| * |q.2| = |q.1 * q.2| := (abs_mul _ _).symm
        dsimp [bellmanGaussianTimeWeight]
        rw [mul_assoc 6, hx]
        nlinarith only [mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 6 * |q.1 * q.2|),
          mul_le_mul_of_nonneg_left ht2 (sq_nonneg q.2), ht3]
  have bellmanGaussianTimeWeight_nonneg :
      0 ≤ bellmanGaussianTimeWeight q := by
    unfold bellmanGaussianTimeWeight
    positivity
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (bellmanGaussianKernel_pos t q)]
  by_cases ht : t.val ≤ 1
  · simp [bellmanDerivativeMajorant, indicator_of_mem
      (show t.val ∈ Ioc 0 1 from ⟨t.property, ht⟩), indicator_of_notMem (show t.val ∉ Ioi 1 from not_lt.mpr ht)]
    have h := mul_le_mul (bellmanGaussianTimeCoefficient_small ht)
      (bellmanGaussianKernel_le_smallTime_four t ht q a ha hq)
      (bellmanGaussianKernel_pos t q).le
      (div_nonneg (bellmanGaussianTimeWeight_nonneg) (by positivity))
    refine h.trans_eq ?_
    field_simp [ne_of_gt t.property]
  · have h1 : 1 < t.val := lt_of_not_ge ht
    simp only [bellmanDerivativeMajorant, indicator_of_notMem
      (show t.val ∉ Ioc (0 : ℝ) 1 from fun h => ht h.2),
      indicator_of_mem (show t.val ∈ Ioi (1 : ℝ) from h1), zero_add]
    refine (mul_le_mul (bellmanGaussianTimeCoefficient_large h1.le) (bellmanGaussianKernel_le t q) (bellmanGaussianKernel_pos t q).le (bellmanGaussianTimeWeight_nonneg)).trans_eq ?_
    rw [Real.rpow_neg t.property.le, Real.rpow_two]
    ring



/-- The scalar time chart vanishes at infinite time. -/
theorem bellmanGaussianTimeChart_tendsto_atTop (q : ℝ × ℝ) :
    Tendsto (fun s => bellmanGaussianTimeChart s q) atTop (𝓝 0) := by
  have hlim : Tendsto (fun s : ℝ => Real.sqrt 3 / (2 * Real.pi) * s ^ (-2 : ℝ))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 2))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
    exact (bellmanGaussianKernel_pos ⟨s, hs⟩ q).le
  · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with s hs
    have hspos := hs
    calc
      bellmanGaussianTimeChart s q = bellmanGaussianKernel ⟨s, hspos⟩ q := rfl
      _ ≤ Real.sqrt 3 / (2 * Real.pi * s ^ 2) := bellmanGaussianKernel_le _ _
      _ = _ := by
        rw [Real.rpow_neg hspos.le, Real.rpow_two]
        ring



/-- The integrated time derivative of the Gaussian is zero away from its pole. -/
theorem integral_bellmanGaussianTimeDerivative_eq_zero (q : BellmanPuncturedPlane) :
    (∫ t : BellmanPositiveTime,
      bellmanGaussianTimeCoefficient t.val q.val * bellmanGaussianKernel t q.val
        ∂bellmanPositiveTimeVolume) = 0   := by
  have integrable_bellmanGaussianTimeDerivative :
      Integrable (fun t : BellmanPositiveTime =>
      bellmanGaussianTimeCoefficient t.val q.val * bellmanGaussianKernel t q.val)
      bellmanPositiveTimeVolume := by
    have hm : Measurable (fun t : BellmanPositiveTime =>
        bellmanGaussianTimeCoefficient t.val q.val * bellmanGaussianKernel t q.val) := by
      unfold bellmanGaussianTimeCoefficient bellmanGaussianKernel bellmanGaussianExponent
      fun_prop
    refine ((integrable_bellmanDerivativeMajorant (q.val.1 ^ 2 + q.val.2 ^ 2)).const_mul
      (bellmanGaussianTimeWeight q.val)).mono' hm.aestronglyMeasurable ?_
    exact ae_of_all _ fun t => bellmanGaussianTimeDerivative_le_majorant _
      (bellmanPunctured_sq_pos q) q.val le_rfl t
  have bellmanGaussianTimeChart_continuousWithinAt_zero :
      ContinuousWithinAt (fun s => bellmanGaussianTimeChart s q.val) (Ici 0) 0 := by
    have bellmanGaussianTimeChart_tendsto_zero :
        Tendsto (fun s => bellmanGaussianTimeChart s q.val) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      let a := q.val.1 ^ 2 + q.val.2 ^ 2
      let C := 360 * 8 ^ 6 * Real.sqrt 3 / (Real.pi * a ^ 6)
      have hlim : Tendsto (fun s : ℝ => C * s ^ 4) (𝓝[>] 0) (𝓝 0) := by
        simpa using (tendsto_const_nhds.mul ((tendsto_id.mono_left inf_le_left).pow 4) :
          Tendsto (fun s : ℝ => C * s ^ 4) (𝓝[>] 0) (𝓝 (C * 0 ^ 4)))
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact (bellmanGaussianKernel_pos ⟨s, hs⟩ q.val).le
      · filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with s hs h1
        exact bellmanGaussianKernel_le_smallTime_four ⟨s, hs⟩ h1.le q.val a (bellmanPunctured_sq_pos q) le_rfl
    apply continuousWithinAt_Ioi_iff_Ici.mp
    simpa [ContinuousWithinAt, bellmanGaussianTimeChart] using
      bellmanGaussianTimeChart_tendsto_zero
  let f' : ℝ → ℝ := fun s =>
    bellmanGaussianTimeCoefficient s q.val * bellmanGaussianTimeChart s q.val
  have he : MeasurableEmbedding (Subtype.val : BellmanPositiveTime → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Ioi
  have hi : IntegrableOn f' (Ioi 0) := by
    rw [IntegrableOn, ← map_bellmanPositiveTimeVolume_coe, he.integrable_map_iff]
    exact integrable_bellmanGaussianTimeDerivative
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (bellmanGaussianTimeChart_continuousWithinAt_zero)
    (fun s hs => hasDerivAt_bellmanGaussianTimeChart ⟨s, hs⟩ q.val) hi
    (bellmanGaussianTimeChart_tendsto_atTop q.val)
  rw [← map_bellmanPositiveTimeVolume_coe, he.integral_map] at h
  simpa [f', bellmanGaussianTimeChart, bellmanGaussianKernel,
    bellmanGaussianExponent] using h


/-- Punctured Lebesgue measure is sigma-finite on its locally compact carrier. -/
instance bellmanPuncturedVolume_sigmaFinite : SigmaFinite bellmanPuncturedVolume := by
  let : LocallyCompactSpace BellmanPuncturedPlane :=
    isOpen_compl_singleton.locallyCompactSpace
  infer_instance

/-- A compact test supported away from the origin remains compact on the punctured plane. -/
theorem bellman_test_compact_subtype {f : ℝ × ℝ → ℝ} (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ {q | q ≠ (0, 0)}) :
    HasCompactSupport (fun q : BellmanPuncturedPlane => f q.val) := by
  have hK : IsCompact ((Subtype.val : BellmanPuncturedPlane → ℝ × ℝ) ⁻¹' tsupport f) := by
    apply Topology.IsInducing.subtypeVal.isCompact_preimage' hc
    intro q hq
    exact ⟨⟨q, hs hq⟩, rfl⟩
  exact hK.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_comp_subset_preimage f continuous_subtype_val)

/-- Compactly supported continuous tests are integrable for the actual fundamental measure. -/
theorem bellman_integrable_fundamental_test {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ {q | q ≠ (0, 0)}) :
    Integrable (fun q : BellmanPuncturedPlane => f q.val) bellmanFundamentalMeasure :=
  (hf.comp continuous_subtype_val).integrable_of_hasCompactSupport
    (bellman_test_compact_subtype hc hs)



/-- The literal density's real value is the Bochner integral of the positive kernel. -/
theorem bellmanFundamentalDensity_toReal (q : BellmanPuncturedPlane) :
    (bellmanFundamentalDensity q).toReal =
      ∫ t, bellmanGaussianKernel t q.val ∂bellmanPositiveTimeVolume := by
  exact (integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ fun t => (bellmanGaussianKernel_pos t q.val).le)
    (integrable_bellmanGaussianKernel_time q).aestronglyMeasurable).symm

/-- Fundamental-measure integration is the time integral of the literal Gaussian pairing. -/
theorem bellmanFundamentalMeasure_integral_test {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ {q | q ≠ (0, 0)}) :
    (∫ q : BellmanPuncturedPlane, f q.val ∂bellmanFundamentalMeasure) =
      ∫ t : BellmanPositiveTime, (∫ q : ℝ × ℝ, bellmanGaussianKernel t q * f q)
        ∂bellmanPositiveTimeVolume  := by
  have bellman_integrable_gaussian_test :
      Integrable (fun w : BellmanPositiveTime × BellmanPuncturedPlane =>
      bellmanGaussianKernel w.1 w.2.val * f w.2.val)
      (bellmanPositiveTimeVolume.prod bellmanPuncturedVolume) := by
    have hcp := bellman_test_compact_subtype hc hs
    obtain ⟨a, ha, hb⟩ := bellmanPunctured_compact_lower_bound _ hcp
    have hfi : Integrable (fun q : BellmanPuncturedPlane => |f q.val|)
        bellmanPuncturedVolume :=
      ((hf.comp continuous_subtype_val).integrable_of_hasCompactSupport hcp).abs
    have hm : Measurable (fun w : BellmanPositiveTime × BellmanPuncturedPlane =>
        bellmanGaussianKernel w.1 w.2.val * f w.2.val) := by
      apply Continuous.measurable
      exact (continuous_bellmanGaussianKernel.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).mul
        (hf.comp (continuous_subtype_val.comp continuous_snd))
    refine ((integrable_bellmanTimeMajorant a).mul_prod hfi).mono'
      hm.aestronglyMeasurable (ae_of_all _ fun w => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (bellmanGaussianKernel_pos w.1 w.2.val)]
    by_cases hq : w.2 ∈ tsupport (fun q : BellmanPuncturedPlane => f q.val)
    · exact mul_le_mul_of_nonneg_right
        (bellmanGaussianKernel_le_timeMajorant a ha w.2.val (hb _ hq) w.1) (abs_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hq]
  have he : MeasurableEmbedding (Subtype.val : BellmanPuncturedPlane → ℝ × ℝ) :=
    MeasurableEmbedding.subtype_coe isOpen_compl_singleton.measurableSet
  rw [bellmanFundamentalMeasure, integral_withDensity_eq_integral_toReal_smul
    measurable_bellmanFundamentalDensity
    (ae_of_all _ fun q => (bellmanFundamentalDensity_ne_top q).lt_top)]
  simp [bellmanFundamentalDensity_toReal, ← integral_mul_const]
  rw [integral_integral_swap
    (f := fun q : BellmanPuncturedPlane => fun t : BellmanPositiveTime =>
      bellmanGaussianKernel t q.val * f q.val)
    (bellman_integrable_gaussian_test).swap]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  dsimp only
  rw [← map_bellmanPuncturedVolume_coe, he.integral_map]

/-- The Gaussian time derivative has zero total spacetime pairing with a punctured test. -/
theorem bellmanGaussianTimeDerivative_integral_test_eq_zero {f : ℝ × ℝ → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ {q | q ≠ (0, 0)}) :
    (∫ t : BellmanPositiveTime, (∫ q : ℝ × ℝ,
      (bellmanGaussianTimeCoefficient t.val q * bellmanGaussianKernel t q) * f q)
        ∂bellmanPositiveTimeVolume) = 0  := by
  have bellman_integrable_gaussian_timeDerivative_test :
      Integrable (fun w : BellmanPositiveTime × BellmanPuncturedPlane =>
      (bellmanGaussianTimeCoefficient w.1.val w.2.val *
        bellmanGaussianKernel w.1 w.2.val) * f w.2.val)
      (bellmanPositiveTimeVolume.prod bellmanPuncturedVolume) := by
    have hcp := bellman_test_compact_subtype hc hs
    obtain ⟨a, ha, hb⟩ := bellmanPunctured_compact_lower_bound _ hcp
    have hweight : Continuous bellmanGaussianTimeWeight := by
      unfold bellmanGaussianTimeWeight
      fun_prop
    have hfi : Integrable (fun q : BellmanPuncturedPlane =>
        bellmanGaussianTimeWeight q.val * |f q.val|) bellmanPuncturedVolume :=
      ((hweight.comp continuous_subtype_val).mul (hf.comp continuous_subtype_val).abs)
        |>.integrable_of_hasCompactSupport hcp.abs.mul_left
    have hm : Measurable (fun w : BellmanPositiveTime × BellmanPuncturedPlane =>
        (bellmanGaussianTimeCoefficient w.1.val w.2.val *
          bellmanGaussianKernel w.1 w.2.val) * f w.2.val) := by
      have hg : Measurable (fun w : BellmanPositiveTime × BellmanPuncturedPlane =>
          bellmanGaussianKernel w.1 w.2.val) := (continuous_bellmanGaussianKernel.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).measurable
      apply Measurable.mul (Measurable.mul ?_ hg)
        (hf.measurable.comp (measurable_subtype_coe.comp measurable_snd))
      unfold bellmanGaussianTimeCoefficient
      fun_prop
    refine ((integrable_bellmanDerivativeMajorant a).mul_prod hfi).mono'
      hm.aestronglyMeasurable (ae_of_all _ fun w => ?_)
    rw [norm_mul, Real.norm_eq_abs (f w.2.val)]
    by_cases hq : w.2 ∈ tsupport (fun q : BellmanPuncturedPlane => f q.val)
    · have h := mul_le_mul_of_nonneg_right
        (bellmanGaussianTimeDerivative_le_majorant a ha w.2.val (hb _ hq) w.1)
        (abs_nonneg (f w.2.val))
      simpa only [mul_assoc, mul_comm, mul_left_comm] using h
    · simp [image_eq_zero_of_notMem_tsupport hq]
  have he : MeasurableEmbedding (Subtype.val : BellmanPuncturedPlane → ℝ × ℝ) :=
    MeasurableEmbedding.subtype_coe isOpen_compl_singleton.measurableSet
  have heq (t : BellmanPositiveTime) :
      (∫ q : ℝ × ℝ, (bellmanGaussianTimeCoefficient t.val q *
        bellmanGaussianKernel t q) * f q) =
      ∫ q : BellmanPuncturedPlane, (bellmanGaussianTimeCoefficient t.val q.val *
        bellmanGaussianKernel t q.val) * f q.val ∂bellmanPuncturedVolume := by
    rw [← map_bellmanPuncturedVolume_coe, he.integral_map]
  simp_rw [heq]
  rw [integral_integral_swap (bellman_integrable_gaussian_timeDerivative_test)]
  simp [integral_mul_const, integral_bellmanGaussianTimeDerivative_eq_zero, integral_zero]

end HypoellipticAleksandrov.KineticAleksandrov

