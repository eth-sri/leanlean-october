module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklov
import Batteries.Tactic.Alias
import Batteries.Tactic.OpenPrivate
import all HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklov
import all HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTranslation

open private HypoellipticAleksandrov.Parabolic.Dirichlet.sqNorm_smul_window_integral_le from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklov
open private HypoellipticAleksandrov.Parabolic.Dirichlet.tendsto_sqNorm_integral_translate_add_on_of_memLp_two from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTranslation
open private HypoellipticAleksandrov.Parabolic.Dirichlet.sqNorm_forward_window_average_le from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklov
open private HypoellipticAleksandrov.Parabolic.Dirichlet.forward_window_product_memLp from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklov
open private HypoellipticAleksandrov.Parabolic.Dirichlet.tendsto_inv_mul_setIntegral_Ioc_zero from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklov
open private HypoellipticAleksandrov.Parabolic.Dirichlet.ae_memLp_forward_window_slice from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklov
open private HypoellipticAleksandrov.Parabolic.Dirichlet.forward_window_sqNorm_integral_swap from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeSteklov
open private HypoellipticAleksandrov.Parabolic.Dirichlet.sqNorm_integral_eq_norm_sq_toLp from HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTranslation


/-!
# Endpoint-safe reverse-time Steklov convergence

This module upgrades the strict-interior Steklov convergence theorem to the
whole closed time interval.  The proof uses the zero extension only inside
ordinary Lebesgue integrals, so no endpoint values are interpreted as traces.
-/

 public section

open Filter MeasureTheory Set Topology
open scoped ENNReal



namespace HypoellipticAleksandrov.Parabolic.Dirichlet

variable {E : Type*}






















private theorem endpoint_backward_window_product_memLp
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) (hF : MemLp F (2 ) ) (h : ℝ) (K : Set ℝ) :
    MemLp (fun z : ℝ × ℝ => F (z.2 - z.1) - F z.2) (2 )
      ((volume.restrict (Ioc 0 h)).prod (volume.restrict K)) := by
  let sharedTerm_a985c6cf71 := ((fun z : ℝ × ℝ => F (z.2 - z.1)))
  let μs : Measure ℝ := volume.restrict (Ioc 0 h)
  let μt : Measure ℝ := volume.restrict K
  letI : IsFiniteMeasure μs := (id inferInstance)
  let hzero : MemLp (fun z : ℝ × ℝ => F z.2) (2 ) (μs.prod volume) :=
    hF.comp_snd μs

  let hminus : MemLp sharedTerm_a985c6cf71 (2 )
      (μs.prod volume) := by
    simpa only [Function.comp_def] using hzero.comp_measurePreserving (measurePreserving_prod_sub μs volume)


  exact (show MemLp sharedTerm_a985c6cf71 (2 )
      (μs.prod μt) by
      simpa only [μt, ← Measure.prod_restrict, Measure.restrict_univ] using
        hminus.restrict (univ ×ˢ K)).sub (by
      simpa only [μt, ← Measure.prod_restrict, Measure.restrict_univ] using
        hzero.restrict (univ ×ˢ K))

private theorem endpoint_backward_window_sqNorm_integral_swap
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) (hF : MemLp F (2 ) ) (h : ℝ) (K : Set ℝ)
    [IsFiniteMeasure (volume.restrict K)] :
    (∫ s in Ioc 0 h, ∫ t in K, ‖F (t - s) - F t‖ ^ 2) =
      ∫ t in K, ∫ s in Ioc 0 h, ‖F (t - s) - F t‖ ^ 2 := by


  simpa only [MeasureTheory.integral] using integral_integral_swap ((endpoint_backward_window_product_memLp F hF h K).integrable_norm_pow (by norm_num))

private theorem endpoint_ae_memLp_backward_window_slice
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) (hF : MemLp F (2 ) ) (h : ℝ) (K : Set ℝ)
    [IsFiniteMeasure (volume.restrict K)] :
    ∀ᵐ t ∂volume.restrict K,
      MemLp (fun s => F (t - s) - F t) (2 )
        (volume.restrict (Ioc 0 h)) := by
  let hPhi  :=
    endpoint_backward_window_product_memLp F hF h K


  filter_upwards [(hPhi.integrable (by norm_num)).prod_left_ae, (hPhi.integrable_norm_pow (by norm_num)).prod_left_ae] with t ht htSq
  exact (memLp_two_iff_integrable_sq_norm ht.aestronglyMeasurable).mpr htSq

private theorem endpoint_sqNorm_backward_window_average_le
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) (hF : MemLp F (2 ) ) (h : ℝ) (hh : 0 < h) (K : Set ℝ)
    [IsFiniteMeasure (volume.restrict K)] :
    (∫ t in K, ‖h⁻¹ • ∫ s in Ioc 0 h, (F (t - s) - F t)‖ ^ 2) ≤
      h⁻¹ * ∫ s in Ioc 0 h, ∫ t in K, ‖F (t - s) - F t‖ ^ 2 := by
  let μs : Measure ℝ := volume.restrict (Ioc 0 h)
  let μt : Measure ℝ := volume.restrict K
  letI : IsFiniteMeasure μs := (id inferInstance)
  letI : IsFiniteMeasure μt := inferInstance





  calc
    (∫ t in K, ‖h⁻¹ • ∫ s in Ioc 0 h, (F (t - s) - F t)‖ ^ 2) =
        ∫ t, ‖h⁻¹ • ∫ s, F (t - s) - F t ∂μs‖ ^ 2 ∂μt := rfl
    _ ≤ ∫ t, h⁻¹ * ∫ s, ‖F (t - s) - F t‖ ^ 2 ∂μs ∂μt := (by
        apply integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) ((((endpoint_backward_window_product_memLp F hF h K).integrable_norm_pow (by norm_num)).integral_prod_right).const_mul _)
        filter_upwards [(endpoint_ae_memLp_backward_window_slice F hF h K)] with t ht
        exact _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.sqNorm_smul_window_integral_le h hh _ ht)
    _ = h⁻¹ * ∫ t, ∫ s, ‖F (t - s) - F t‖ ^ 2 ∂μs ∂μt := by
      rw [integral_const_mul]
    _ = h⁻¹ * ∫ s in Ioc 0 h, ∫ t in K, ‖F (t - s) - F t‖ ^ 2 := by
      rw [← endpoint_backward_window_sqNorm_integral_swap F hF h K]




variable {E : Type*}

private theorem endpoint_forward_sub_eq_window
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (hh : 0 < h)
    (f : MeasureTheory.Lp E (2 ) (reverseTimeVolume T))
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    reverseTimeForwardSteklov T h f t - f t = h⁻¹ •
      ∫ s in Ioc 0 h, ((Ioo 0 T).indicator (f : ℝ → E) (s + t) -
        (Ioo 0 T).indicator (f : ℝ → E) t) := by
  let S  := Ioo 0 T
  let F  := S.indicator f
  let W  := Ioc t (t + h)
  have hwindow : (∫ x in W, f x ∂reverseTimeVolume T) = ∫ x in W, F x := by
    unfold reverseTimeVolume reverseTimeOpenInterval
    change (∫ x, f x ∂(volume.restrict S).restrict W) = ∫ x in W, F x
    rw [Measure.restrict_restrict measurableSet_Ioc]
    rw [← integral_indicator measurableSet_Ioc]
    have hindicator : W.indicator F = (W ∩ S).indicator f := by
      funext x
      simp only [F, Set.indicator_indicator]
    rw [hindicator]
    exact (integral_indicator (measurableSet_Ioc.inter measurableSet_Ioo)).symm
  have hshift : (∫ s in Ioc 0 h, F (s + t)) = ∫ x in W, F x := by
    calc
      (∫ s in Ioc 0 h, F (s + t)) = ∫ s in (0 )..h, F (s + t) :=
        (intervalIntegral.integral_of_le hh.le).symm
      _ = ∫ x in (0 : ℝ) + t..h + t, F x :=
        intervalIntegral.integral_comp_add_right F t
      _ = ∫ x in t..t + h, F x := by simp only [zero_add, add_comm h t]
      _ = ∫ x in W, F x := intervalIntegral.integral_of_le (by linarith)
  have hconst : h⁻¹ • ∫ _s in Ioc 0 h, F t = f t := by
    rw [integral_const, MeasureTheory.measureReal_restrict_apply_univ,
      Real.volume_real_Ioc_of_le hh.le, sub_zero]
    rw [← mul_smul]
    field_simp [ne_of_gt hh]
    have hFt : F t = f t := by
      change S.indicator (f : ℝ → E) t = f t
      exact Set.indicator_of_mem ht (f : ℝ → E)
    rw [hFt, one_smul]
  have hF : MemLp F (2 )  := by
    simpa only [F, S, reverseTimeVolume, reverseTimeOpenInterval] using
      (memLp_indicator_iff_restrict measurableSet_Ioo).mpr (Lp.memLp f)
  have hshiftInt : Integrable (fun s => F (s + t)) (volume.restrict (Ioc 0 h)) :=
    ((hF.comp_measurePreserving (measurePreserving_add_right volume t)).restrict _).integrable
      (by norm_num)
  rw [reverseTimeForwardSteklov, hwindow, ← hshift,
    integral_sub hshiftInt (integrable_const _), ← hconst, ← smul_sub]

private theorem endpoint_backward_sub_eq_window
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (hh : 0 < h)
    (f : MeasureTheory.Lp E (2 ) (reverseTimeVolume T))
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    reverseTimeBackwardSteklov T h f t - f t = h⁻¹ •
      ∫ s in Ioc 0 h, ((Ioo 0 T).indicator (f : ℝ → E) (t - s) -
        (Ioo 0 T).indicator (f : ℝ → E) t) := by
  let S  := Ioo 0 T
  let F  := S.indicator f
  let W  := Ioc (t - h) t
  have hwindow : (∫ x in W, f x ∂reverseTimeVolume T) = ∫ x in W, F x := by
    unfold reverseTimeVolume reverseTimeOpenInterval
    change (∫ x, f x ∂(volume.restrict S).restrict W) = ∫ x in W, F x
    rw [Measure.restrict_restrict measurableSet_Ioc]
    rw [← integral_indicator measurableSet_Ioc]
    have hindicator : W.indicator F = (W ∩ S).indicator f := by
      funext x
      simp only [F, Set.indicator_indicator]
    rw [hindicator]
    exact (integral_indicator (measurableSet_Ioc.inter measurableSet_Ioo)).symm
  have hshift : (∫ s in Ioc 0 h, F (t - s)) = ∫ x in W, F x := by
    calc
      (∫ s in Ioc 0 h, F (t - s)) = ∫ s in (0 )..h, F (t - s) :=
        (intervalIntegral.integral_of_le hh.le).symm
      _ = ∫ x in t - h..t - 0, F x := intervalIntegral.integral_comp_sub_left F t
      _ = ∫ x in t - h..t, F x := by simp
      _ = ∫ x in W, F x := intervalIntegral.integral_of_le (by linarith)
  have hconst : h⁻¹ • ∫ _s in Ioc 0 h, F t = f t := by
    rw [integral_const, MeasureTheory.measureReal_restrict_apply_univ,
      Real.volume_real_Ioc_of_le hh.le, sub_zero]
    rw [← mul_smul]
    field_simp [ne_of_gt hh]
    have hFt : F t = f t := by
      change S.indicator (f : ℝ → E) t = f t
      exact Set.indicator_of_mem ht (f : ℝ → E)
    rw [hFt, one_smul]
  have hF : MemLp F (2 )  := by
    simpa only [F, S, reverseTimeVolume, reverseTimeOpenInterval] using
      (memLp_indicator_iff_restrict measurableSet_Ioo).mpr (Lp.memLp f)
  have hshiftInt : Integrable (fun s => F (t - s)) (volume.restrict (Ioc 0 h)) :=
    ((hF.comp_measurePreserving (volume.measurePreserving_sub_left t)).restrict _).integrable
      (by norm_num)
  rw [reverseTimeBackwardSteklov, hwindow, ← hshift,
    integral_sub hshiftInt (integrable_const _), ← hconst, ← smul_sub]

private theorem endpoint_ae_mem_Ioo_on_Icc (T : ℝ) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T), t ∈ Ioo 0 T := by
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards [Ioo_ae_eq_Icc (μ := volume)] with t ht
  exact ht.mpr

variable {E : Type*}

/-- Forward Steklov averages converge strongly in Bochner `L²` on the full
closed reverse-time interval; endpoint values are measure-null. -/
theorem tendsto_forwardSteklov_sqNorm_integral_on_Icc_zero_T
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (hT : 0 < T)
    (f : MeasureTheory.Lp E (2 ) (reverseTimeVolume T)) :
    Filter.Tendsto
      (fun h : ℝ => ∫ t in Set.Icc 0 T,
        ‖reverseTimeForwardSteklov T h f t - f t‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  let S  := Ioo 0 T
  let F  := S.indicator f
  let K  := Icc 0 T

  have hF : MemLp F (2 )  := by
    simpa only [F, S, reverseTimeVolume, reverseTimeOpenInterval] using
      (memLp_indicator_iff_restrict measurableSet_Ioo).mpr (Lp.memLp f)
  let q  := fun s => ∫ t in K, ‖F (s + t) - F t‖ ^ 2


  have haverage := _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.tendsto_inv_mul_setIntegral_Ioc_zero q (by
      simpa only [q, add_comm] using
        (_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.tendsto_sqNorm_integral_translate_add_on_of_memLp_two F hF K).mono_left
          nhdsWithin_le_nhds) (fun s => integral_nonneg fun _ => sq_nonneg _)
  apply squeeze_zero'
  · filter_upwards with h
    exact integral_nonneg fun _ => sq_nonneg _
  ·
    filter_upwards [self_mem_nhdsWithin] with h hh

    calc
      (∫ t in K, ‖reverseTimeForwardSteklov T h f t - f t‖ ^ 2) =
          ∫ t in K, ‖h⁻¹ • ∫ s in Ioc 0 h, (F (s + t) - F t)‖ ^ 2 := (by
              apply integral_congr_ae
              filter_upwards [endpoint_ae_mem_Ioo_on_Icc T] with t ht
              rw [endpoint_forward_sub_eq_window T h hh f t ht])
      _ ≤ h⁻¹ * ∫ s in Ioc 0 h, ∫ t in K, ‖F (s + t) - F t‖ ^ 2 :=
        _root_.HypoellipticAleksandrov.Parabolic.Dirichlet.sqNorm_forward_window_average_le F hF h hh K
      _ = h⁻¹ * ∫ s in Ioc 0 h, q s := rfl
  · exact haverage

/-- Backward Steklov averages converge strongly in Bochner `L²` on the full
closed reverse-time interval; endpoint values are measure-null. -/
theorem tendsto_backwardSteklov_sqNorm_integral_on_Icc_zero_T
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (hT : 0 < T)
    (f : MeasureTheory.Lp E (2 ) (reverseTimeVolume T)) :
    Filter.Tendsto
      (fun h : ℝ => ∫ t in Set.Icc 0 T,
        ‖reverseTimeBackwardSteklov T h f t - f t‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  let S  := Ioo 0 T
  let F  := S.indicator f
  let K  := Icc 0 T

  have hF : MemLp F (2 )  := by
    simpa only [F, S, reverseTimeVolume, reverseTimeOpenInterval] using
      (memLp_indicator_iff_restrict measurableSet_Ioo).mpr (Lp.memLp f)
  let q  := fun s => ∫ t in K, ‖F (t - s) - F t‖ ^ 2


  have hq : Tendsto q (𝓝[>] 0) (𝓝 0) := by

    exact (show Tendsto (fun h : ℝ => ∫ t in K, ‖F (t - h) - F t‖ ^ 2)
        (𝓝 0) (𝓝 0) by
        exact (_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.tendsto_sqNorm_integral_translate_add_on_of_memLp_two F hF K).comp (by
            simpa using tendsto_neg (0 : ℝ))).mono_left nhdsWithin_le_nhds


  apply squeeze_zero'
  · filter_upwards with h
    exact integral_nonneg fun _ => sq_nonneg _
  ·
    filter_upwards [self_mem_nhdsWithin] with h hh

    calc
      (∫ t in K, ‖reverseTimeBackwardSteklov T h f t - f t‖ ^ 2) =
          ∫ t in K, ‖h⁻¹ • ∫ s in Ioc 0 h, (F (t - s) - F t)‖ ^ 2 := (by
              apply integral_congr_ae
              filter_upwards [endpoint_ae_mem_Ioo_on_Icc T] with t ht
              rw [endpoint_backward_sub_eq_window T h hh f t ht])
      _ ≤ h⁻¹ * ∫ s in Ioc 0 h, ∫ t in K, ‖F (t - s) - F t‖ ^ 2 :=
        endpoint_sqNorm_backward_window_average_le F hF h hh K
      _ = h⁻¹ * ∫ s in Ioc 0 h, q s := rfl
  · exact (_root_.HypoellipticAleksandrov.Parabolic.Dirichlet.tendsto_inv_mul_setIntegral_Ioc_zero q hq (fun s => integral_nonneg fun _ => sq_nonneg _))

end HypoellipticAleksandrov.Parabolic.Dirichlet
