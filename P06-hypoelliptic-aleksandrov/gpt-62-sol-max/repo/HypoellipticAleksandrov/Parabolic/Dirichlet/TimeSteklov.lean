module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTranslation
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

/-!
# One-sided reverse-time Bochner averages

This module provides literal reverse-time Bochner Steklov windows and their
basic regularity.  The local strong approximation assertions are stated on
strictly interior compact intervals, so they remain assertions about `Lp`
classes rather than selected pointwise representatives.
-/

@[expose] public section

open Filter MeasureTheory Set Topology
open scoped ENNReal

noncomputable section

namespace HypoellipticAleksandrov.Parabolic.Dirichlet

/-- Forward literal reverse-time Bochner Steklov window average. -/
noncomputable def reverseTimeForwardSteklov
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T))
    (t : ℝ) : E :=
  h⁻¹ • ∫ s in Set.Ioc t (t + h), f s ∂reverseTimeVolume T

/-- Backward literal reverse-time Bochner Steklov window average. -/
noncomputable def reverseTimeBackwardSteklov
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T))
    (t : ℝ) : E :=
  h⁻¹ • ∫ s in Set.Ioc (t - h) t, f s ∂reverseTimeVolume T

private theorem reverseTimeVolume_isFiniteMeasure (T : ℝ) :
    IsFiniteMeasure (reverseTimeVolume T) := by
  unfold reverseTimeVolume reverseTimeOpenInterval
  infer_instance

private theorem reverseTimeVolume_noAtoms (T : ℝ) :
    NoAtoms (reverseTimeVolume T) := by
  change NullSingletonClass (volume.restrict (Ioo (0 : ℝ) T))
  infer_instance

private theorem forwardSteklov_eq_primitive_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (hh : 0 < h)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T)) (t : ℝ) :
    reverseTimeForwardSteklov T h f t = h⁻¹ •
      ((∫ s in (0 : ℝ)..(t + h), f s ∂reverseTimeVolume T) -
        ∫ s in (0 : ℝ)..t, f s ∂reverseTimeVolume T) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := reverseTimeVolume_isFiniteMeasure T
  letI : NullSingletonClass (reverseTimeVolume T) := reverseTimeVolume_noAtoms T
  have hf : Integrable (f : ℝ → E) (reverseTimeVolume T) :=
    (Lp.memLp f).integrable (by norm_num)
  have hadd : (∫ s in (0 : ℝ)..t, f s ∂reverseTimeVolume T) +
      ∫ s in t..(t + h), f s ∂reverseTimeVolume T =
      ∫ s in (0 : ℝ)..(t + h), f s ∂reverseTimeVolume T :=
    intervalIntegral.integral_add_adjacent_intervals hf.intervalIntegrable hf.intervalIntegrable
  have hsub : ∫ s in t..(t + h), f s ∂reverseTimeVolume T =
      (∫ s in (0 : ℝ)..(t + h), f s ∂reverseTimeVolume T) -
        ∫ s in (0 : ℝ)..t, f s ∂reverseTimeVolume T :=
    (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using hadd)
  rw [reverseTimeForwardSteklov, ← intervalIntegral.integral_of_le (by linarith), hsub]

private theorem tendsto_inv_mul_setIntegral_Ioc_zero
    (q : ℝ → ℝ) (hq : Tendsto q (𝓝[>] 0) (𝓝 0))
    (hq0 : ∀ s, 0 ≤ q s) :
    Tendsto (fun h : ℝ => h⁻¹ * ∫ s in Ioc 0 h, q s) (𝓝[>] 0) (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro c hc
    filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin] with h hh
    exact hc.trans_le (mul_nonneg (inv_nonneg.mpr hh.le)
      (integral_nonneg fun s => hq0 s))
  · intro ε hε
    have hqhalf : ∀ᶠ s : ℝ in 𝓝[>] 0, q s < ε / 2 :=
      hq.eventually (eventually_lt_nhds (half_pos hε))
    rcases mem_nhdsGT_iff_exists_Ioc_subset.mp hqhalf with ⟨δ, hδ, hδq⟩
    filter_upwards [Ioc_mem_nhdsGT hδ] with h hh
    have hI : (∫ s in Ioc 0 h, q s) ≤ ∫ _s in Ioc 0 h, ε / 2 := by
      apply integral_mono_of_nonneg
      · exact Eventually.of_forall fun s => hq0 s
      · exact integrable_const _
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact (hδq ⟨hs.1, hs.2.trans hh.2⟩).le
    have hconst : (∫ _s in Ioc 0 h, ε / 2) = h * (ε / 2) := by
      rw [integral_const, MeasureTheory.measureReal_restrict_apply_univ,
        Real.volume_real_Ioc_of_le hh.1.le, sub_zero, smul_eq_mul]
    calc
      h⁻¹ * ∫ s in Ioc 0 h, q s ≤ h⁻¹ * (h * (ε / 2)) :=
        mul_le_mul_of_nonneg_left (hI.trans_eq hconst) (inv_nonneg.mpr hh.1.le)
      _ = ε / 2 := by field_simp [ne_of_gt hh.1]
      _ < ε := half_lt_self hε

section
variable {E : Type*}

private theorem backwardSteklov_eq_primitive_sub [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (hh : 0 < h)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T)) (t : ℝ) :
    reverseTimeBackwardSteklov T h f t = h⁻¹ •
      ((∫ s in (0 : ℝ)..t, f s ∂reverseTimeVolume T) -
        ∫ s in (0 : ℝ)..(t - h), f s ∂reverseTimeVolume T) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := reverseTimeVolume_isFiniteMeasure T
  letI : NullSingletonClass (reverseTimeVolume T) := reverseTimeVolume_noAtoms T
  have hf : Integrable (f : ℝ → E) (reverseTimeVolume T) :=
    (Lp.memLp f).integrable (by norm_num)
  have hadd : (∫ s in (0 : ℝ)..(t - h), f s ∂reverseTimeVolume T) +
      ∫ s in (t - h)..t, f s ∂reverseTimeVolume T =
      ∫ s in (0 : ℝ)..t, f s ∂reverseTimeVolume T :=
    intervalIntegral.integral_add_adjacent_intervals hf.intervalIntegrable hf.intervalIntegrable
  have hsub : ∫ s in (t - h)..t, f s ∂reverseTimeVolume T =
      (∫ s in (0 : ℝ)..t, f s ∂reverseTimeVolume T) -
        ∫ s in (0 : ℝ)..(t - h), f s ∂reverseTimeVolume T :=
    (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using hadd)
  rw [reverseTimeBackwardSteklov, ← intervalIntegral.integral_of_le (by linarith), hsub]

/-- A positive-length forward average is an ordinary continuous `E`-curve. -/
theorem continuous_reverseTimeForwardSteklov [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (hh : 0 < h)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T)) :
    Continuous (reverseTimeForwardSteklov T h f) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := reverseTimeVolume_isFiniteMeasure T
  letI : NullSingletonClass (reverseTimeVolume T) := reverseTimeVolume_noAtoms T
  have hf : Integrable (f : ℝ → E) (reverseTimeVolume T) :=
    (Lp.memLp f).integrable (by norm_num)
  let P : ℝ → E := fun x => ∫ s in (0 : ℝ)..x, f s ∂reverseTimeVolume T
  have hP : Continuous P := hf.continuous_primitive 0
  have hformula : reverseTimeForwardSteklov T h f =
      fun t => h⁻¹ • (P (t + h) - P t) := by
    funext t
    exact forwardSteklov_eq_primitive_sub T h hh f t
  rw [hformula]
  exact continuous_const.smul ((hP.comp (continuous_id.add continuous_const)).sub hP)

/-- A positive-length backward average is an ordinary continuous `E`-curve. -/
theorem continuous_reverseTimeBackwardSteklov [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (hh : 0 < h)
    (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T)) :
    Continuous (reverseTimeBackwardSteklov T h f) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := reverseTimeVolume_isFiniteMeasure T
  letI : NullSingletonClass (reverseTimeVolume T) := reverseTimeVolume_noAtoms T
  have hf : Integrable (f : ℝ → E) (reverseTimeVolume T) :=
    (Lp.memLp f).integrable (by norm_num)
  let P : ℝ → E := fun x => ∫ s in (0 : ℝ)..x, f s ∂reverseTimeVolume T
  have hP : Continuous P := hf.continuous_primitive 0
  have hformula : reverseTimeBackwardSteklov T h f =
      fun t => h⁻¹ • (P t - P (t - h)) := by
    funext t
    exact backwardSteklov_eq_primitive_sub T h hh f t
  rw [hformula]
  exact continuous_const.smul (hP.sub (hP.comp (continuous_id.sub continuous_const)))

end

section Windows

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Jensen's inequality for the normalized integral over a translation window. -/
private theorem sqNorm_windowMean_le (h : ℝ) (hh : 0 < h) (φ : ℝ → E)
    (hφ : IntegrableOn φ (Ioc 0 h)) (hφsq : IntegrableOn (fun s => ‖φ s‖ ^ 2) (Ioc 0 h)) :
    ‖h⁻¹ • ∫ s in Ioc 0 h, φ s‖ ^ 2 ≤ h⁻¹ * ∫ s in Ioc 0 h, ‖φ s‖ ^ 2 := by
  have hvol : (volume.restrict (Ioc 0 h)).real univ = h := by
    rw [measureReal_restrict_apply_univ, Real.volume_real_Ioc_of_le hh.le, sub_zero]
  have hJ := (convexOn_pow (𝕜 := ℝ) 2).map_set_average_le
    (continuous_pow 2).continuousOn isClosed_Ici
    (μ := volume) (t := Ioc 0 h) (f := fun s => ‖φ s‖)
    (by simp [Real.volume_Ioc, hh]) (by simp)
    (Eventually.of_forall fun _ => norm_nonneg _) hφ.norm hφsq
  rw [average_eq, average_eq, hvol, smul_eq_mul, smul_eq_mul] at hJ
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hh.le)]
  exact (pow_le_pow_left₀ (by positivity)
    (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm φ) (inv_nonneg.mpr hh.le)) 2).trans hJ

section
variable (F : ℝ → E) (hF : MemLp F 2 volume) (K : Set ℝ)
include hF

/-- The Jensen bound, integrated in time using the measure-preserving shear. -/
private theorem sqNorm_translationWindow_le [IsFiniteMeasure (volume.restrict K)] (δ : ℝ → ℝ)
    (h : ℝ) (hh : 0 < h)
    (hδ : MeasurePreserving (fun z : ℝ × ℝ => (z.1, δ z.1 + z.2))
      ((volume.restrict (Ioc 0 h)).prod volume) ((volume.restrict (Ioc 0 h)).prod volume)) :
    (∫ t in K, ‖h⁻¹ • ∫ s in Ioc 0 h, (F (δ s + t) - F t)‖ ^ 2) ≤
      h⁻¹ * ∫ s in Ioc 0 h, ∫ t in K, ‖F (δ s + t) - F t‖ ^ 2 := by
  let μ := volume.restrict (Ioc 0 h)
  let ν := volume.restrict K
  letI : IsFiniteMeasure μ := inferInstanceAs (IsFiniteMeasure (volume.restrict (Ioc 0 h)))
  letI : IsFiniteMeasure ν := inferInstanceAs (IsFiniteMeasure (volume.restrict K))
  have hbase := hF.comp_snd μ
  have hmem : MemLp (fun z : ℝ × ℝ => F (δ z.1 + z.2) - F z.2) 2 (μ.prod ν) := by
    simpa only [μ, ν, ← Measure.prod_restrict, Measure.restrict_univ, Function.comp_def, Pi.sub_def] using
      ((hbase.comp_measurePreserving hδ).sub hbase).restrict (univ ×ˢ K)
  have hi := hmem.integrable (by norm_num)
  have hi2 := hmem.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  rw [integral_integral_swap hi2, ← integral_const_mul]
  apply integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
    (hi2.integral_prod_right.const_mul _)
  filter_upwards [hi.prod_left_ae, hi2.prod_left_ae] with t ht ht2
  exact sqNorm_windowMean_le h hh _ ht ht2

/-- Averaging translations tending to the identity converges in `L²`. -/
private theorem tendsto_sqNorm_translationWindow [IsFiniteMeasure (volume.restrict K)] (δ : ℝ → ℝ)
    (hδ : Tendsto δ (𝓝 0) (𝓝 0))
    (hpres : ∀ h : ℝ, MeasurePreserving (fun z : ℝ × ℝ => (z.1, δ z.1 + z.2))
      ((volume.restrict (Ioc 0 h)).prod volume) ((volume.restrict (Ioc 0 h)).prod volume)) :
    Tendsto (fun h : ℝ => ∫ t in K, ‖h⁻¹ • ∫ s in Ioc 0 h, (F (δ s + t) - F t)‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  have hq := ((tendsto_sqNorm_integral_translate_add_on_of_memLp_two F hF K).comp hδ).mono_left
    (nhdsWithin_le_nhds (s := Ioi 0))
  simp only [Function.comp_def, add_comm] at hq
  apply squeeze_zero' (g := fun h : ℝ => h⁻¹ * ∫ s in Ioc 0 h, ∫ t in K, ‖F (δ s + t) - F t‖ ^ 2)
  · exact Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _
  · filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with h hh
    exact sqNorm_translationWindow_le F hF K δ h hh (hpres h)
  · exact tendsto_inv_mul_setIntegral_Ioc_zero _ (by simpa only [add_comm] using hq)
      (fun _ => integral_nonneg fun _ => sq_nonneg _)

end

private theorem memLp_reverseTime_zeroExtension (T : ℝ)
    (f : Lp E 2 (reverseTimeVolume T)) : MemLp ((Ioo 0 T).indicator f) 2 volume :=
  (memLp_indicator_iff_restrict measurableSet_Ioo).2 (Lp.memLp f)

/-- The error in the window integral after extending by zero outside reverse time. -/
private theorem steklov_sub_eq_window (T h : ℝ) (hh : 0 < h)
    (f : Lp E 2 (reverseTimeVolume T)) (t : ℝ) (ht : t ∈ Ioo 0 T)
    {W : Set ℝ} (hW : MeasurableSet W) (φ : ℝ → ℝ)
    (hp : MeasurePreserving φ volume volume)
    (hshift : (∫ s in Ioc 0 h, (Ioo 0 T).indicator f (φ s)) =
      ∫ s in W, (Ioo 0 T).indicator f s) :
    h⁻¹ • (∫ s in W, f s ∂reverseTimeVolume T) - f t =
      h⁻¹ • ∫ s in Ioc 0 h, ((Ioo 0 T).indicator f (φ s) - (Ioo 0 T).indicator f t) := by
  rw [show (∫ s in W, f s ∂reverseTimeVolume T) = ∫ s in W, (Ioo 0 T).indicator f s by
    unfold reverseTimeVolume reverseTimeOpenInterval
    rw [Measure.restrict_restrict hW,
      ← integral_indicator (μ := volume) (hW.inter measurableSet_Ioo),
      ← integral_indicator (μ := volume) hW, Set.indicator_indicator]]
  have hφ : IntegrableOn (fun s => (Ioo 0 T).indicator f (φ s)) (Ioc 0 h) :=
    (((memLp_reverseTime_zeroExtension T f).comp_measurePreserving hp).restrict _).integrable (by norm_num)
  rw [← hshift, integral_sub hφ (integrable_const _), smul_sub, integral_const,
    measureReal_restrict_apply_univ, Real.volume_real_Ioc_of_le hh.le, sub_zero,
    ← mul_smul, inv_mul_cancel₀ hh.ne', one_smul, Set.indicator_of_mem ht]

section
variable (T : ℝ) (f : Lp E 2 (reverseTimeVolume T)) (K : Set ℝ)

/-- Forward Steklov convergence on any finite-measure subdomain of the time interval. -/
theorem tendsto_forwardSteklov_sqNorm_integral_on [IsFiniteMeasure (volume.restrict K)]
    (hK : ∀ᵐ t ∂volume.restrict K, t ∈ Ioo 0 T) :
    Tendsto (fun h : ℝ => ∫ t in K, ‖reverseTimeForwardSteklov T h f t - f t‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  refine (tendsto_sqNorm_translationWindow ((Ioo 0 T).indicator (f : ℝ → E)) (memLp_reverseTime_zeroExtension T f) K id
    tendsto_id (fun _ => measurePreserving_prod_add _ _)).congr' ?_
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with h hh
  apply integral_congr_ae
  filter_upwards [hK] with t ht
  rw [reverseTimeForwardSteklov, steklov_sub_eq_window T h hh f t ht measurableSet_Ioc
    (fun s => s + t) (measurePreserving_add_right volume t)]
  · rfl
  · rw [← intervalIntegral.integral_of_le hh.le, intervalIntegral.integral_comp_add_right,
      zero_add, add_comm h t, intervalIntegral.integral_of_le (le_add_of_nonneg_right hh.le)]

/-- Backward Steklov convergence on any finite-measure subdomain of the time interval. -/
theorem tendsto_backwardSteklov_sqNorm_integral_on [IsFiniteMeasure (volume.restrict K)]
    (hK : ∀ᵐ t ∂volume.restrict K, t ∈ Ioo 0 T) :
    Tendsto (fun h : ℝ => ∫ t in K, ‖reverseTimeBackwardSteklov T h f t - f t‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  let F := (Ioo 0 T).indicator (f : ℝ → E)
  have hp (h : ℝ) := measurePreserving_prod_sub (volume.restrict (Ioc 0 h)) (volume : Measure ℝ)
  refine (tendsto_sqNorm_translationWindow F (memLp_reverseTime_zeroExtension T f) K Neg.neg
    (by simpa using tendsto_neg (0 : ℝ)) (fun h => by simpa only [sub_eq_neg_add] using hp h)).congr' ?_
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Ioi 0)] with h hh
  apply integral_congr_ae
  filter_upwards [hK] with t ht
  rw [reverseTimeBackwardSteklov, steklov_sub_eq_window T h hh f t ht measurableSet_Ioc
    (fun s => t - s) (volume.measurePreserving_sub_left t)]
  · simp only [sub_eq_neg_add, F]
  · rw [← intervalIntegral.integral_of_le hh.le, intervalIntegral.integral_comp_sub_left,
      sub_zero, intervalIntegral.integral_of_le (sub_le_self t hh.le)]

end

end Windows

/-- Forward one-sided Steklov averages converge strongly in local Bochner `L²`. -/
theorem tendsto_forwardSteklov_sqNorm_integral_on_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (f : MeasureTheory.Lp E (2 : ℝ≥0∞) (reverseTimeVolume T))
    {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b) (hb : b < T) :
    Filter.Tendsto
      (fun h : ℝ => ∫ t in Set.Icc a b,
        ‖reverseTimeForwardSteklov T h f t - f t‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_forwardSteklov_sqNorm_integral_on T f
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩

end HypoellipticAleksandrov.Parabolic.Dirichlet
