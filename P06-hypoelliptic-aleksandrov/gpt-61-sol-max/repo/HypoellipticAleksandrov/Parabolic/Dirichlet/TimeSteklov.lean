module

public import HypoellipticAleksandrov.Parabolic.Dirichlet.TimeTranslation
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Prod

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
def reverseTimeForwardSteklov
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (f : MeasureTheory.Lp E (2 ) (reverseTimeVolume T))
    (t : ℝ) : E :=
  h⁻¹ • ∫ s in Set.Ioc t (t + h), f s ∂reverseTimeVolume T

/-- Backward literal reverse-time Bochner Steklov window average. -/
def reverseTimeBackwardSteklov
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (f : MeasureTheory.Lp E (2 ) (reverseTimeVolume T))
    (t : ℝ) : E :=
  h⁻¹ • ∫ s in Set.Ioc (t - h) t, f s ∂reverseTimeVolume T

variable (T : ℝ)

private theorem reverseTimeVolume_isFiniteMeasure  :
    IsFiniteMeasure (reverseTimeVolume T) := by
  unfold reverseTimeVolume reverseTimeOpenInterval
  infer_instance

private theorem reverseTimeVolume_noAtoms  :
    NoAtoms (reverseTimeVolume T) := by
  change NullSingletonClass (volume.restrict (Ioo (0 : ℝ) T))
  infer_instance

variable {E : Type*}

private theorem forward_window_product_memLp
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) (hF : MemLp F (2 ) ) (h : ℝ) (K : Set ℝ) :
    MemLp (fun z : ℝ × ℝ => F (z.1 + z.2) - F z.2) (2 )
      ((volume.restrict (Ioc 0 h)).prod (volume.restrict K)) := by
  let sharedTerm_4b608c2081 := ((fun z : ℝ × ℝ => F (z.1 + z.2)))
  let μs  := volume.restrict (Ioc 0 h)
  let μt  := volume.restrict K
  letI : IsFiniteMeasure μs := (id inferInstance)
  let hzero  :=
    hF.comp_snd μs

  let hplus : MemLp sharedTerm_4b608c2081 (2 )
      (μs.prod volume) := by
    simpa only [Function.comp_def] using hzero.comp_measurePreserving (measurePreserving_prod_add μs volume)


  exact (show MemLp sharedTerm_4b608c2081 (2 ) (μs.prod μt) by
      simpa only [μt, ← Measure.prod_restrict, Measure.restrict_univ] using
        hplus.restrict (univ ×ˢ K)).sub (by
      simpa only [μt, ← Measure.prod_restrict, Measure.restrict_univ] using
        hzero.restrict (univ ×ˢ K))

private theorem forward_window_sqNorm_integral_swap
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) (hF : MemLp F (2 ) ) (h : ℝ) (K : Set ℝ)
    [IsFiniteMeasure (volume.restrict K)] :
    (∫ s in Ioc 0 h, ∫ t in K, ‖F (s + t) - F t‖ ^ 2) =
      ∫ t in K, ∫ s in Ioc 0 h, ‖F (s + t) - F t‖ ^ 2 := by


  simpa only [MeasureTheory.integral] using
    integral_integral_swap ((forward_window_product_memLp F hF h K).integrable_norm_pow (by norm_num))

private theorem ae_memLp_forward_window_slice
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) (hF : MemLp F (2 ) ) (h : ℝ) (K : Set ℝ)
    [IsFiniteMeasure (volume.restrict K)] :
    ∀ᵐ t ∂volume.restrict K,
      MemLp (fun s => F (s + t) - F t) (2 )
        (volume.restrict (Ioc 0 h)) := by
  let hPhi  :=
    forward_window_product_memLp F hF h K


  filter_upwards [(hPhi.integrable (by norm_num)).prod_left_ae, (hPhi.integrable_norm_pow (by norm_num)).prod_left_ae] with t ht htSq
  exact (memLp_two_iff_integrable_sq_norm ht.aestronglyMeasurable).mpr htSq

private theorem sqNorm_smul_window_integral_le
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (h : ℝ) (hh : 0 < h) (φ : ℝ → E)
    (hφ : MemLp φ (2 ) (volume.restrict (Ioc 0 h))) :
    ‖h⁻¹ • ∫ s, φ s ∂volume.restrict (Ioc 0 h)‖ ^ 2 ≤
      h⁻¹ * ∫ s, ‖φ s‖ ^ 2 ∂volume.restrict (Ioc 0 h) := by
  let μ  := volume.restrict (Ioc 0 h)
  letI : IsFiniteMeasure μ := (id inferInstance)
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (μ := μ) (f := fun s => ‖φ s‖) (g := fun _ => (1 ))
    (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun _ => zero_le_one)
    (by simpa only [ENNReal.ofReal_ofNat] using hφ.norm)
    (by simpa only [ENNReal.ofReal_ofNat] using
      (memLp_const (1 : ℝ) : MemLp _ (2 ) μ))
  have hvol : μ.real univ = h := by
    dsimp only [μ]
    rw [MeasureTheory.measureReal_restrict_apply_univ,
      Real.volume_real_Ioc_of_le hh.le, sub_zero]


  have hholder' : ∫ s, ‖φ s‖ ∂μ ≤
      (∫ s, ‖φ s‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
        (∫ _s, (1 : ℝ) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    simpa only [mul_one] using hholder



  calc
    ‖h⁻¹ • ∫ s, φ s ∂μ‖ ^ 2 = (h⁻¹ * ‖∫ s, φ s ∂μ‖) ^ 2 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hh.le)]
    _ ≤ (h⁻¹ * ∫ s, ‖φ s‖ ∂μ) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg (inv_nonneg.mpr hh.le) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm φ)
          (inv_nonneg.mpr hh.le)) 2
    _ ≤ (h⁻¹ * (√(∫ s, ‖φ s‖ ^ 2 ∂μ) * √h)) ^ 2 := (pow_le_pow_left₀ (mul_nonneg (inv_nonneg.mpr hh.le) (integral_nonneg fun _ => norm_nonneg _))
          (mul_le_mul_of_nonneg_left (by
              rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
              simpa only [Real.rpow_two, one_pow, integral_const, hvol, smul_eq_mul, mul_one] using hholder') (inv_nonneg.mpr hh.le)) 2)
    _ = h⁻¹ * ∫ s, ‖φ s‖ ^ 2 ∂μ := (by
        rw [mul_pow, mul_pow, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _), Real.sq_sqrt hh.le]
        field_simp [ne_of_gt hh])

private theorem sqNorm_forward_window_average_le
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℝ → E) (hF : MemLp F (2 ) ) (h : ℝ) (hh : 0 < h) (K : Set ℝ)
    [IsFiniteMeasure (volume.restrict K)] :
    (∫ t in K, ‖h⁻¹ • ∫ s in Ioc 0 h, (F (s + t) - F t)‖ ^ 2) ≤
      h⁻¹ * ∫ s in Ioc 0 h, ∫ t in K, ‖F (s + t) - F t‖ ^ 2 := (Trans.trans
  (Trans.trans
    (Trans.trans rfl
      (integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg ‖h⁻¹ • ∫ (s : ℝ) in Ioc 0 h, F (s + x) - F x‖)
        (Integrable.const_mul
          (Integrable.integral_prod_right
            (MemLp.integrable_norm_pow (forward_window_product_memLp F hF h K)
              (Mathlib.Meta.NormNum.isNat_eq_false (Mathlib.Meta.NormNum.IsNat.raw_refl 2)
                (Mathlib.Meta.NormNum.isNat_ofNat ℕ (Eq.refl 0)) (Eq.refl false))))
          h⁻¹)
        (mp_mem (ae_memLp_forward_window_slice F hF h K)
          (univ_mem' (id fun t ht => sqNorm_smul_window_integral_le h hh (fun s => F (s + t) - F t) ht)))))
    (Eq.mpr
      (id
        (congrArg (fun _a => _a = h⁻¹ * ∫ (t : ℝ) in K, ∫ (s : ℝ) in Ioc 0 h, ‖F (s + t) - F t‖ ^ 2)
          (integral_const_mul h⁻¹ fun t => ∫ (s : ℝ) in Ioc 0 h, ‖F (s + t) - F t‖ ^ 2)))
      (Eq.refl (h⁻¹ * ∫ (a : ℝ) in K, ∫ (s : ℝ) in Ioc 0 h, ‖F (s + a) - F a‖ ^ 2))))
  (Eq.mpr
    (id
      (congrArg (fun _a => h⁻¹ * _a = h⁻¹ * ∫ (s : ℝ) in Ioc 0 h, ∫ (t : ℝ) in K, ‖F (s + t) - F t‖ ^ 2)
        (Eq.symm (forward_window_sqNorm_integral_swap F hF h K))))
    (Eq.refl (h⁻¹ * ∫ (s : ℝ) in Ioc 0 h, ∫ (t : ℝ) in K, ‖F (s + t) - F t‖ ^ 2))))

private theorem forwardSteklov_eq_primitive_sub
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (hh : 0 < h)
    (f : MeasureTheory.Lp E (2 ) (reverseTimeVolume T)) (t : ℝ) :
    reverseTimeForwardSteklov T h f t = h⁻¹ •
      ((∫ s in (0 )..(t + h), f s ∂reverseTimeVolume T) -
        ∫ s in (0 )..t, f s ∂reverseTimeVolume T) := by
  let sharedTerm_ab0f5b55a8 := (∫ s in (0 )..(t + h), f s ∂reverseTimeVolume T)
  let sharedTerm_c59276bea9 := (∫ s in (0 )..t, f s ∂reverseTimeVolume T)
  letI : IsFiniteMeasure (reverseTimeVolume T) := reverseTimeVolume_isFiniteMeasure T
  letI : NullSingletonClass (reverseTimeVolume T) := reverseTimeVolume_noAtoms T
  have hf  :=
    (Lp.memLp f).integrable (by norm_num)

  have hsub : ∫ s in t..(t + h), f s ∂reverseTimeVolume T =
      (sharedTerm_ab0f5b55a8) -
        sharedTerm_c59276bea9 :=
    (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using (show (sharedTerm_c59276bea9) +
      ∫ s in t..(t + h), f s ∂reverseTimeVolume T =
      sharedTerm_ab0f5b55a8 from intervalIntegral.integral_add_adjacent_intervals hf.intervalIntegrable hf.intervalIntegrable))
  rw [reverseTimeForwardSteklov, ← intervalIntegral.integral_of_le (by linarith), hsub]

private theorem tendsto_inv_mul_setIntegral_Ioc_zero
    (q : ℝ → ℝ) (hq : Tendsto q (𝓝[>] 0) (𝓝 0))
    (hq0 : ∀ s, 0 ≤ q s) :
    Tendsto (fun h  => h⁻¹ * ∫ s in Ioc 0 h, q s) (𝓝[>] 0) (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro c hc
    filter_upwards [show ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h from self_mem_nhdsWithin] with h hh
    exact hc.trans_le (mul_nonneg (inv_nonneg.mpr hh.le)
      (integral_nonneg hq0))
  · intro ε hε

    rcases mem_nhdsGT_iff_exists_Ioc_subset.mp (hq.eventually (eventually_lt_nhds (half_pos hε))) with ⟨δ, hδ, hδq⟩
    filter_upwards [Ioc_mem_nhdsGT hδ] with h hh


    calc
      h⁻¹ * ∫ s in Ioc 0 h, q s ≤ h⁻¹ * (h * (ε / 2)) :=
        mul_le_mul_of_nonneg_left ((show (∫ s in Ioc 0 h, q s) ≤ ∫ _s in Ioc 0 h, ε / 2 by
            apply integral_mono_of_nonneg
            · exact Eventually.of_forall hq0
            · exact integrable_const _
            · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
              exact (hδq ⟨hs.1, hs.2.trans hh.2⟩).le).trans_eq (by
            rw [integral_const, MeasureTheory.measureReal_restrict_apply_univ,
              Real.volume_real_Ioc_of_le hh.1.le, sub_zero, smul_eq_mul])) (inv_nonneg.mpr hh.1.le)
      _ = ε / 2 := by field_simp [ne_of_gt hh.1]
      _ < ε := half_lt_self hε

variable {E : Type*}

private theorem forwardSteklov_sub_eq_forward_window
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h a b : ℝ) (hh : 0 < h) (hhT : h < T - b) (ha : 0 < a) (hb : b < T)
    (f : MeasureTheory.Lp E (2 ) (reverseTimeVolume T))
    (t : ℝ) (ht : t ∈ Icc a b) :
    reverseTimeForwardSteklov T h f t - f t = h⁻¹ •
      ∫ s in Ioc 0 h, ((Ioo 0 T).indicator (f : ℝ → E) (s + t) -
        (Ioo 0 T).indicator (f : ℝ → E) t) := by
  let S  := Ioo 0 T
  let F  := S.indicator f
  let W  := Ioc t (t + h)
  have hwin : W ⊆ S := by
    intro x hx
    constructor
    · exact lt_of_lt_of_le ha (ht.1.trans hx.1.le)
    · calc
        x ≤ t + h := hx.2
        _ ≤ b + h := by simpa only [add_comm] using add_le_add_right ht.2 h
        _ < T := by linarith
  have hwindow : (∫ x in W, f x ∂reverseTimeVolume T) = ∫ x in W, F x := by
    unfold reverseTimeVolume reverseTimeOpenInterval
    change (∫ x, f x ∂(volume.restrict S).restrict W) = ∫ x in W, F x
    rw [Measure.restrict_restrict_of_subset hwin]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    simp only [F, Set.indicator_of_mem (hwin hx)]
  have hshift : (∫ s in Ioc 0 h, F (s + t)) = ∫ x in W, F x := by
    calc
      (∫ s in Ioc 0 h, F (s + t)) = ∫ s in (0 )..h, F (s + t) :=
        (intervalIntegral.integral_of_le hh.le).symm
      _ = ∫ x in (0 : ℝ) + t..h + t, F x :=
        intervalIntegral.integral_comp_add_right F t
      _ = ∫ x in t..t + h, F x := by simp only [zero_add, add_comm h t]
      _ = ∫ x in W, F x := intervalIntegral.integral_of_le (by linarith)
  have htS : t ∈ S := ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
  have hconst : h⁻¹ • ∫ _s in Ioc 0 h, F t = f t := by
    rw [integral_const, MeasureTheory.measureReal_restrict_apply_univ,
      Real.volume_real_Ioc_of_le hh.le, sub_zero]
    simp only [F, Set.indicator_of_mem htS]
    rw [← mul_smul]
    field_simp [ne_of_gt hh]
    exact one_smul _ _
  have hF : MemLp F (2 )  := by
    simpa only [F, S, reverseTimeVolume, reverseTimeOpenInterval] using
      (memLp_indicator_iff_restrict measurableSet_Ioo).mpr (Lp.memLp f)
  have hshiftInt : Integrable (fun s => F (s + t)) (volume.restrict (Ioc 0 h)) :=
    ((hF.comp_measurePreserving (measurePreserving_add_right volume t)).restrict _).integrable
      (by norm_num)
  rw [reverseTimeForwardSteklov, hwindow, ← hshift,
    integral_sub hshiftInt (integrable_const _), ← hconst, ← smul_sub]

private theorem backwardSteklov_eq_primitive_sub
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (hh : 0 < h)
    (f : MeasureTheory.Lp E (2 ) (reverseTimeVolume T)) (t : ℝ) :
    reverseTimeBackwardSteklov T h f t = h⁻¹ •
      ((∫ s in (0 )..t, f s ∂reverseTimeVolume T) -
        ∫ s in (0 )..(t - h), f s ∂reverseTimeVolume T) := by
  let sharedTerm_79a37952aa := (∫ s in (0 )..(t - h), f s ∂reverseTimeVolume T)
  let sharedTerm_740fe56e71 := (∫ s in (0 )..t, f s ∂reverseTimeVolume T)
  letI : IsFiniteMeasure (reverseTimeVolume T) := reverseTimeVolume_isFiniteMeasure T
  letI : NullSingletonClass (reverseTimeVolume T) := reverseTimeVolume_noAtoms T
  have hf  :=
    (Lp.memLp f).integrable (by norm_num)

  have hsub : ∫ s in (t - h)..t, f s ∂reverseTimeVolume T =
      (sharedTerm_740fe56e71) -
        sharedTerm_79a37952aa :=
    (eq_sub_iff_add_eq).mpr (by simpa [add_comm] using (show (sharedTerm_79a37952aa) +
      ∫ s in (t - h)..t, f s ∂reverseTimeVolume T =
      sharedTerm_740fe56e71 from intervalIntegral.integral_add_adjacent_intervals hf.intervalIntegrable hf.intervalIntegrable))
  rw [reverseTimeBackwardSteklov, ← intervalIntegral.integral_of_le (by linarith), hsub]

/-- A positive-length forward average is an ordinary continuous `E`-curve. -/
theorem continuous_reverseTimeForwardSteklov
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (hh : 0 < h)
    (f : MeasureTheory.Lp E (2 ) (reverseTimeVolume T)) :
    Continuous (reverseTimeForwardSteklov T h f) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := reverseTimeVolume_isFiniteMeasure T
  letI : NullSingletonClass (reverseTimeVolume T) := reverseTimeVolume_noAtoms T

  let P  := fun x => ∫ s in (0 )..x, f s ∂reverseTimeVolume T
  have hP  := ((Lp.memLp f).integrable (by norm_num)).continuous_primitive 0
  have hformula : reverseTimeForwardSteklov T h f =
      fun t => h⁻¹ • (P (t + h) - P t) := by
    funext t
    exact forwardSteklov_eq_primitive_sub T h hh f t
  rw [hformula]
  exact continuous_const.smul ((hP.comp (continuous_id.add continuous_const)).sub hP)

/-- A positive-length backward average is an ordinary continuous `E`-curve. -/
theorem continuous_reverseTimeBackwardSteklov
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T h : ℝ) (hh : 0 < h)
    (f : MeasureTheory.Lp E (2 ) (reverseTimeVolume T)) :
    Continuous (reverseTimeBackwardSteklov T h f) := by
  letI : IsFiniteMeasure (reverseTimeVolume T) := reverseTimeVolume_isFiniteMeasure T
  letI : NullSingletonClass (reverseTimeVolume T) := reverseTimeVolume_noAtoms T

  let P  := fun x => ∫ s in (0 )..x, f s ∂reverseTimeVolume T
  have hP  := ((Lp.memLp f).integrable (by norm_num)).continuous_primitive 0
  have hformula : reverseTimeBackwardSteklov T h f =
      fun t => h⁻¹ • (P t - P (t - h)) := by
    funext t
    exact backwardSteklov_eq_primitive_sub T h hh f t
  rw [hformula]
  exact continuous_const.smul (hP.sub (hP.comp (continuous_id.sub continuous_const)))

/-- Forward one-sided Steklov averages converge strongly in local Bochner `L²`. -/
theorem tendsto_forwardSteklov_sqNorm_integral_on_Icc
     [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (f : MeasureTheory.Lp E (2 ) (reverseTimeVolume T))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < T) :
    Filter.Tendsto
      (fun h : ℝ => ∫ t in Set.Icc a b,
        ‖reverseTimeForwardSteklov T h f t - f t‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  let S  := Ioo 0 T
  let F  := S.indicator f
  let K  := Icc a b

  let q  := fun s => ∫ t in K, ‖f (t + s) - f t‖ ^ 2



  apply squeeze_zero'
  · filter_upwards with h
    exact integral_nonneg fun _ => sq_nonneg _
  ·

    filter_upwards [self_mem_nhdsWithin, ((eventually_lt_nhds (sub_pos.mpr hb)).filter_mono nhdsWithin_le_nhds)] with h hh hhT


    calc
      (∫ t in K, ‖reverseTimeForwardSteklov T h f t - f t‖ ^ 2) =
          ∫ t in K, ‖h⁻¹ • ∫ s in Ioc 0 h, (F (s + t) - F t)‖ ^ 2 := (by
              apply integral_congr_ae
              filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
              rw [forwardSteklov_sub_eq_forward_window T h a b hh hhT ha hb f t ht])
      _ ≤ h⁻¹ * ∫ s in Ioc 0 h, ∫ t in K, ‖F (s + t) - F t‖ ^ 2 :=
        sqNorm_forward_window_average_le F (by
            simpa only [F, S, reverseTimeVolume, reverseTimeOpenInterval] using
              (memLp_indicator_iff_restrict measurableSet_Ioo).mpr (Lp.memLp f)) h hh K
      _ = h⁻¹ * ∫ s in Ioc 0 h, q s := (by
          congr 1
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
          apply setIntegral_congr_fun measurableSet_Icc
          intro t ht
          have htS : t ∈ S := ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
          have htsS : t + s ∈ S := by
            constructor
            · exact add_pos (lt_of_lt_of_le ha ht.1) hs.1
            · calc
                t + s ≤ b + h := add_le_add ht.2 hs.2
                _ < T := by linarith

          simp only [F, Set.indicator_of_mem (by simpa only [add_comm] using htsS), Set.indicator_of_mem htS, add_comm])
  · exact (tendsto_inv_mul_setIntegral_Ioc_zero q (tendsto_sqNorm_integral_forward_translate_on_Icc T f ha hab hb) (fun s => integral_nonneg fun _ => sq_nonneg _))

end HypoellipticAleksandrov.Parabolic.Dirichlet
