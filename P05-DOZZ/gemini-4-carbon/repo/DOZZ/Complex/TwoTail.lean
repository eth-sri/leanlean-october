/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Complex.Charge
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Probability.Moments.ComplexMGF

/-!
# Two-tail meromorphic continuation and residues
-/

@[expose] public section

noncomputable section
open MeasureTheory Filter Topology Set Complex Asymptotics ProbabilityTheory
open scoped Real

namespace DOZZ.Proofs

private def lowerTailKernel (T : ℝ → ℝ) : ℝ → ℂ :=
  (Ioc 0 1).indicator fun t => (T t : ℂ)

private def upperTailErrorKernel (T : ℝ → ℝ) (c₁ c₂ β₁ β₂ : ℝ) : ℝ → ℂ :=
  (Ioi 1).indicator fun t => ((T t - c₁ * t ^ (-β₁) - c₂ * t ^ (-β₂) : ℝ) : ℂ)

private def upperTailPowerKernel (c β : ℝ) : ℝ → ℂ :=
  (Ioi 1).indicator fun t => ((c * t ^ (-β) : ℝ) : ℂ)

private def inverseTailRemainder (T : ℝ → ℝ) (c₁ c₂ β₁ β₂ : ℝ) (s : ℂ) : ℂ :=
  1 - s * mellin (lowerTailKernel (fun t => 1 - T t)) s +
    s * mellin (upperTailErrorKernel T c₁ c₂ β₁ β₂) s






/-- Proof of `DOZZ.complexMoment_two_tail_residues_of_inverse_moments`: the lower-tail extension,
with every inverse moment kept as a separate input. -/
theorem complexMoment_two_tail_residues_of_inverse_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : AEMeasurable Y P) (hpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hinv : ∀ q : ℝ, 0 < q → Integrable (fun ω => Y ω ^ (-q)) P)
    (c₁ c₂ c₃ β₁ β₂ β₃ : ℝ)
    (_hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ < β₂) (hβ₂₃ : β₂ < β₃)
    (htail : ∀ t : ℝ, 1 ≤ t →
      |realUpperTail P Y hY t - c₁ * t ^ (-β₁) - c₂ * t ^ (-β₂)| ≤ c₃ * t ^ (-β₃)) :
    (∀ s : ℂ, s.re < β₁ → Integrable (fun ω => (Y ω : ℂ) ^ s) P) ∧
    DifferentiableOn ℂ (fun s : ℂ => ∫ ω, (Y ω : ℂ) ^ s ∂P)
      {s : ℂ | s.re < β₁} ∧
    ∃ r : ℂ → ℂ, DifferentiableOn ℂ r {s | s.re < β₃} ∧
      MeromorphicOn (fun s => twoTailRational c₁ c₂ β₁ β₂ s + r s) {s | s.re < β₃} ∧
      (∀ s : ℂ, s.re < β₁ →
        (∫ ω, (Y ω : ℂ) ^ s ∂P) = twoTailRational c₁ c₂ β₁ β₂ s + r s) ∧
      r 0 = 1 ∧
      Tendsto (fun s => (s - (β₁ : ℂ)) *
        (twoTailRational c₁ c₂ β₁ β₂ s + r s)) (𝓝[≠] (β₁ : ℂ)) (𝓝 (-(β₁ * c₁ : ℝ) : ℂ)) ∧
      Tendsto (fun s => (s - (β₂ : ℂ)) *
        (twoTailRational c₁ c₂ β₁ β₂ s + r s)) (𝓝[≠] (β₂ : ℂ)) (𝓝 (-(β₂ * c₂ : ℝ) : ℂ)) := by
  have complexMoment_real_eq_mellin_tail (hpos : ∀ᵐ ω ∂P, 0 ≤ Y ω) (p : ℝ) (hp : 0 < p) (hm : MellinConvergent (fun t => (realUpperTail P Y hY t : ℂ)) (p : ℂ)) : Integrable (fun ω => Y ω ^ p) P ∧
        (∫ ω, (Y ω : ℂ) ^ (p : ℂ) ∂P) = (p : ℂ) * mellin (fun t => (realUpperTail P Y hY t : ℂ)) (p : ℂ) := by
    have hT := measurable_realUpperTail P Y hY
    have ht : IntegrableOn (fun t => realUpperTail P Y hY t * t ^ (p - 1)) (Ioi 0) :=
      ((mellin_convergent_iff_norm (T := Ioi 0) Subset.rfl measurableSet_Ioi
        (Complex.continuous_ofReal.measurable.comp hT).aestronglyMeasurable.restrict).1 hm).congr
        (Eventually.of_forall fun t => by
          change t ^ (p - 1) * ‖(realUpperTail P Y hY t : ℂ)‖ = _
          rw [norm_real, Real.norm_of_nonneg (realUpperTail_bounds P Y hY t).1, mul_comm])
    have hreal := integral_rpow_eq_tail_of_integrable P Y hY hpos p hp ht
    refine ⟨hreal.1, ?_⟩
    rw [integral_congr_ae (hpos.mono fun ω hω => (ofReal_cpow hω p).symm),
      integral_complex_ofReal, hreal.2, ofReal_mul, mellin, ← integral_complex_ofReal]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    change ((realUpperTail P Y hY t * t ^ (p - 1) : ℝ) : ℂ) =
      (t : ℂ) ^ ((p : ℂ) - 1) * (realUpperTail P Y hY t : ℂ)
    rw [ofReal_mul, ofReal_cpow ht.le, ofReal_sub, ofReal_one, mul_comm]
  have hasMellin_upperTailPowerKernel (c β : ℝ) (s : ℂ) (hs : s.re < β) : HasMellin (upperTailPowerKernel c β) s ((c : ℂ) / ((β : ℂ) - s)) := by
    let a := s - 1 - (β : ℂ)
    have ha : a.re < -1 := by dsimp [a]; linarith
    have heq : (fun t : ℝ => (t : ℂ) ^ (s - 1) • upperTailPowerKernel c β t) =
        (Ioi (1 : ℝ)).indicator fun t => (c : ℂ) * (t : ℂ) ^ a := by
      ext t
      by_cases ht : t ∈ Ioi (1 : ℝ)
      · have ht0 : 0 < t := zero_lt_one.trans ht
        rw [upperTailPowerKernel, indicator_of_mem ht, indicator_of_mem ht, ofReal_mul,
          ofReal_cpow ht0.le, ofReal_neg, smul_eq_mul, mul_left_comm,
          ← cpow_add _ _ (ofReal_ne_zero.2 ht0.ne')]; rfl
      · simp [upperTailPowerKernel, indicator_of_notMem ht]
    have hint : IntegrableOn (fun t : ℝ => (c : ℂ) * (t : ℂ) ^ a) (Ioi 1) :=
      (integrableOn_Ioi_cpow_of_lt ha zero_lt_one).const_mul _
    refine ⟨by rw [MellinConvergent, heq]; exact (hint.integrable_indicator measurableSet_Ioi).integrableOn, ?_⟩
    have hsub : Ioi (1 : ℝ) ⊆ Ioi 0 := fun _ ht => zero_lt_one.trans ht
    rw [mellin, heq, integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict_of_subset hsub, integral_const_mul,
      integral_Ioi_cpow_of_lt ha zero_lt_one, ofReal_one, one_cpow,
      show a + 1 = -((β : ℂ) - s) by dsimp [a]; ring, div_neg, neg_div, neg_neg]
    ring
  have locInt_of_bound {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ t, ‖g t‖ ≤ C) := 
    (locallyIntegrableOn_const (c := C) (s := Ioi 0)).mono hg
      (Eventually.of_forall fun t => (hb t).trans_eq (Real.norm_of_nonneg hC).symm)
  have mellin_upperTailErrorKernel (T : ℝ → ℝ) (hT : Measurable T) (c₁ c₂ c₃ β₁ β₂ β₃ : ℝ) (hc₃ : 0 ≤ c₃) (hβ₃ : 0 ≤ β₃) (htail : ∀ t : ℝ, 1 ≤ t → |T t - c₁ * t ^ (-β₁) - c₂ * t ^ (-β₂)| ≤ c₃ * t ^ (-β₃)) : (∀ s : ℂ, s.re < β₃ → MellinConvergent (upperTailErrorKernel T c₁ c₂ β₁ β₂) s) ∧
        DifferentiableOn ℂ (mellin (upperTailErrorKernel T c₁ c₂ β₁ β₂)) {s | s.re < β₃} := by
    let g := upperTailErrorKernel T c₁ c₂ β₁ β₂
    have hg : AEStronglyMeasurable g volume :=
      ((Complex.continuous_ofReal.measurable.comp
        ((hT.sub ((measurable_id.pow_const (-β₁)).const_mul c₁)).sub
          ((measurable_id.pow_const (-β₂)).const_mul c₂))).indicator measurableSet_Ioi).aestronglyMeasurable
    have hpow (t : ℝ) (ht : 1 ≤ t) : ‖g t‖ ≤ c₃ * t ^ (-β₃) := by
      dsimp only [g]
      by_cases h : t ∈ Ioi (1 : ℝ)
      · rw [upperTailErrorKernel, indicator_of_mem h, norm_real, Real.norm_eq_abs]; exact htail t ht
      · rw [upperTailErrorKernel, indicator_of_notMem h, norm_zero]
        exact mul_nonneg hc₃ (Real.rpow_nonneg (by linarith) _)
    have hbnd (t : ℝ) : ‖g t‖ ≤ c₃ := by
      by_cases ht : 1 < t
      · exact (hpow t ht.le).trans ((mul_le_of_le_one_right hc₃
          (Real.rpow_le_one_of_one_le_of_nonpos ht.le (neg_nonpos.2 hβ₃))))
      · dsimp only [g]; rw [upperTailErrorKernel, indicator_of_notMem (show t ∉ Ioi 1 from ht), norm_zero]; exact hc₃
    have hloc := locInt_of_bound hg hc₃ hbnd
    have htop : g =O[atTop] fun t : ℝ => t ^ (-β₃) := IsBigO.of_bound c₃ (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      exact (hpow t ht).trans_eq (by rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]))
    have hzero (b : ℝ) : g =O[𝓝[>] 0] fun t : ℝ => t ^ (-b) := IsBigO.of_bound 0 (by
      filter_upwards [(eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds] with t ht
      dsimp only [g]
      rw [upperTailErrorKernel, indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from not_lt.2 ht.le),
        norm_zero, zero_mul])
    exact ⟨fun s hs => mellinConvergent_of_isBigO_rpow hloc htop hs (hzero (s.re - 1)) (by linarith),
      fun s hs => (mellin_differentiableAt_of_isBigO_rpow hloc htop hs (hzero (s.re - 1))
        (by linarith)).differentiableWithinAt⟩
  have mellin_lowerTailKernel (T : ℝ → ℝ) (hT : Measurable T) (hb : ∀ t, 0 ≤ T t ∧ T t ≤ 1) (s : ℂ) (hs : 0 < s.re) : MellinConvergent (lowerTailKernel T) s := by
    have hg : AEStronglyMeasurable (lowerTailKernel T) volume :=
      ((Complex.continuous_ofReal.measurable.comp hT).indicator measurableSet_Ioc).aestronglyMeasurable
    have h1 : ∀ t, ‖lowerTailKernel T t‖ ≤ 1 := fun t => by
      by_cases ht : t ∈ Ioc (0 : ℝ) 1
      · rw [lowerTailKernel, indicator_of_mem ht, norm_real, Real.norm_of_nonneg (hb t).1]; exact (hb t).2
      · simp [lowerTailKernel, indicator_of_notMem ht]
    refine mellinConvergent_of_isBigO_rpow (locInt_of_bound hg zero_le_one h1)
      (IsBigO.of_bound 0 ?_) (a := s.re + 1) (by linarith)
      (IsBigO.of_bound 1 (Eventually.of_forall fun t => by simpa using h1 t)) (b := 0) hs
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    simp [lowerTailKernel, indicator_of_notMem (fun h : t ∈ Ioc 0 1 => ht.not_ge h.2)]
  let T := realUpperTail P Y hY
  have hT := measurable_realUpperTail P Y hY
  have hb := realUpperTail_bounds P Y hY
  have htop_le (t : ℝ) (ht : 1 ≤ t) : T t ≤ (c₁ + c₂ + c₃) * t ^ (-β₁) := by
    have h1 := (le_abs_self (T t - c₁ * t ^ (-β₁) - c₂ * t ^ (-β₂))).trans (htail t ht)
    have h2 := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht (neg_le_neg hβ₁₂.le)) hc₂.le
    have h3 := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht (neg_le_neg (hβ₁₂.trans hβ₂₃).le)) hc₃.le
    nlinarith
  have hm_full (p : ℝ) (hp0 : 0 < p) (hpβ : p < β₁) : MellinConvergent (fun t => (T t : ℂ)) (p : ℂ) := by
    have hT1 (t : ℝ) : ‖(T t : ℂ)‖ ≤ 1 := by rw [norm_real, Real.norm_of_nonneg (hb t).1]; exact (hb t).2
    refine mellinConvergent_of_isBigO_rpow
      (locInt_of_bound (Complex.continuous_ofReal.measurable.comp hT).aestronglyMeasurable zero_le_one hT1)
      (IsBigO.of_bound (c₁ + c₂ + c₃) ?_) (a := β₁) (by simpa using hpβ)
      (IsBigO.of_bound 1 (Eventually.of_forall fun t => by simpa using hT1 t)) (b := 0) (by simpa using hp0)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    rw [norm_real, Real.norm_of_nonneg (hb t).1, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    exact htop_le t ht
  have hmom (p : ℝ) (hp : p ∈ Iio β₁) : Integrable (fun ω => Y ω ^ p) P := by
    rcases lt_trichotomy p 0 with hlt | rfl | hgt
    · simpa only [neg_neg] using hinv (-p) (neg_pos.2 hlt)
    · simpa only [Real.rpow_zero] using integrable_const (1 : ℝ)
    · exact (complexMoment_real_eq_mellin_tail (hpos.mono fun _ h => h.le) p hgt (hm_full p hgt hp)).1
  have hsub_exp : Iio β₁ ⊆ interior (integrableExpSet (fun ω => Real.log (Y ω)) P) :=
    isOpen_Iio.subset_interior_iff.2 fun p hp => (hmom p hp).congr (by
      filter_upwards [hpos] with ω hω; rw [Real.rpow_def_of_pos hω, mul_comm])
  have hord_int (s : ℂ) (hs : s.re < β₁) : Integrable (fun ω => (Y ω : ℂ) ^ s) P :=
    (integrable_cexp_mul_of_re_mem_integrableExpSet hY.log (interior_subset (hsub_exp hs))).congr (by
      filter_upwards [hpos] with ω hω
      rw [cpow_def_of_ne_zero (ofReal_ne_zero.2 hω.ne'), ← ofReal_log hω.le, mul_comm])
  have hord_diff : DifferentiableOn ℂ (fun s : ℂ => ∫ ω, (Y ω : ℂ) ^ s ∂P) {s | s.re < β₁} :=
    (differentiableOn_complexMGF.mono fun s hs => hsub_exp hs).congr fun s _ => integral_congr_ae (by
      filter_upwards [hpos] with ω hω
      rw [cpow_def_of_ne_zero (ofReal_ne_zero.2 hω.ne'), ← ofReal_log hω.le, mul_comm])
  have hl_diff : Differentiable ℂ (mellin (lowerTailKernel (fun t => 1 - T t))) := fun s => by
    let q := max 1 (1 - s.re)
    have hq : 0 < q := zero_lt_one.trans_le (le_max_left _ _)
    have hs : -q < s.re := by dsimp [q]; linarith [le_max_right 1 (1 - s.re)]
    let C := ∫ ω, Y ω ^ (-q) ∂P
    have hC : 0 ≤ C := integral_nonneg_of_ae (hpos.mono fun ω hω => (Real.rpow_pos_of_pos hω _).le)
    have hb1 (t : ℝ) : 0 ≤ 1 - T t ∧ 1 - T t ≤ 1 := ⟨by linarith [(hb t).2], by linarith [(hb t).1]⟩
    have h1 (t : ℝ) : ‖lowerTailKernel (fun t => 1 - T t) t‖ ≤ 1 := by
      by_cases ht : t ∈ Ioc (0 : ℝ) 1
      · rw [lowerTailKernel, indicator_of_mem ht, norm_real, Real.norm_of_nonneg (hb1 t).1]; exact (hb1 t).2
      · simp [lowerTailKernel, indicator_of_notMem ht]
    have hpow : lowerTailKernel (fun t => 1 - T t) =O[𝓝[>] 0] fun t : ℝ => t ^ (-(-q)) :=
      IsBigO.of_bound C (by
        filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
        rw [neg_neg, Real.norm_of_nonneg (Real.rpow_pos_of_pos ht q).le]
        by_cases h : t ∈ Ioc (0 : ℝ) 1
        · rw [lowerTailKernel, indicator_of_mem h, norm_real, Real.norm_of_nonneg (hb1 t).1]
          have hu : NullMeasurableSet {ω | t < Y ω} P := hY.nullMeasurableSet_preimage measurableSet_Ioi
          have hl : NullMeasurableSet {ω | Y ω ≤ t} P := hY.nullMeasurableSet_preimage measurableSet_Iic
          have hind : 1 - T t = ∫ ω, {ω | Y ω ≤ t}.indicator (fun _ => (1 : ℝ)) ω ∂P := by
            rw [integral_indicator₀ hl, integral_const]
            simp only [smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ,
              show {ω | Y ω ≤ t} = {ω | t < Y ω}ᶜ by ext; simp [not_lt]]
            exact (probReal_compl_eq_one_sub₀ hu).symm
          rw [hind, mul_comm]
          rw [← integral_const_mul]
          refine integral_mono_ae ((integrable_const 1).indicator₀ hl) ((hinv q hq).const_mul _) ?_
          filter_upwards [hpos] with ω hω
          by_cases hle : Y ω ≤ t
          · rw [indicator_of_mem (show ω ∈ {ω | Y ω ≤ t} from hle)]
            have hp := mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_nonpos hω hle (neg_nonpos.2 hq.le)) (Real.rpow_pos_of_pos ht q).le
            rwa [← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero] at hp
          · rw [indicator_of_notMem (show ω ∉ {ω | Y ω ≤ t} from hle)]; positivity
        · rw [lowerTailKernel, indicator_of_notMem h, norm_zero]; positivity)
    have hloc := locInt_of_bound
      (((Complex.continuous_ofReal.measurable.comp (measurable_const.sub hT)).indicator
        measurableSet_Ioc).aestronglyMeasurable) zero_le_one h1
    have htop : lowerTailKernel (fun t => 1 - T t) =O[atTop] fun t : ℝ => t ^ (-(s.re + 1)) :=
      IsBigO.of_bound 0 (by
        filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
        simp [lowerTailKernel, indicator_of_notMem (fun h : t ∈ Ioc 0 1 => ht.not_ge h.2)])
    exact mellin_differentiableAt_of_isBigO_rpow hloc htop (by linarith) hpow hs
  have hu_err := mellin_upperTailErrorKernel T hT c₁ c₂ c₃ β₁ β₂ β₃ hc₃.le (hβ₁.trans (hβ₁₂.trans hβ₂₃)).le htail
  let r := inverseTailRemainder T c₁ c₂ β₁ β₂
  have hr : DifferentiableOn ℂ r {s | s.re < β₃} :=
    ((differentiableOn_const 1).sub (differentiableOn_id.mul hl_diff.differentiableOn)).add
      (differentiableOn_id.mul hu_err.2)
  have hopen₃ : IsOpen {s : ℂ | s.re < β₃} := isOpen_lt Complex.continuous_re continuous_const
  have hopen₁ : IsOpen {s : ℂ | s.re < β₁} := isOpen_lt Complex.continuous_re continuous_const
  have hrat_diff : DifferentiableOn ℂ (twoTailRational c₁ c₂ β₁ β₂) {s : ℂ | s.re < β₁} := fun s hs => by
    have hne {β : ℝ} (hlt : s.re < β) : (β : ℂ) - s ≠ 0 := fun h =>
      hlt.ne (by simpa using (congrArg Complex.re (sub_eq_zero.1 h)).symm)
    exact ((((differentiableAt_const _).mul differentiableAt_id).div
      ((differentiableAt_const _).sub differentiableAt_id) (hne hs)).add
      (((differentiableAt_const _).mul differentiableAt_id).div
        ((differentiableAt_const _).sub differentiableAt_id) (hne (hs.trans hβ₁₂)))).differentiableWithinAt
  have hformula : EqOn (fun s : ℂ => ∫ ω, (Y ω : ℂ) ^ s ∂P)
      (fun s => twoTailRational c₁ c₂ β₁ β₂ s + r s) {s : ℂ | s.re < β₁} := by
    refine (hord_diff.analyticOnNhd hopen₁).eqOn_of_preconnected_of_frequently_eq
      ((hrat_diff.add (hr.mono fun _ hs => hs.trans (hβ₁₂.trans hβ₂₃))).analyticOnNhd hopen₁)
      ((convex_Iio β₁).linear_preimage Complex.reLm).isPreconnected
      (show ((β₁ / 2 : ℝ) : ℂ) ∈ {s : ℂ | s.re < β₁} from half_lt_self hβ₁) ?_
    refine frequently_eq_of_real_interval (β₁ / 2) (β₁ / 2) (half_pos hβ₁) _ _ fun p hp => ?_
    have hp0 : 0 < p := by linarith [(abs_lt.1 hp).1]
    have hpβ : p < β₁ := by linarith [(abs_lt.1 hp).2]
    rw [(complexMoment_real_eq_mellin_tail (hpos.mono fun _ h => h.le) p hp0 (hm_full p hp0 hpβ)).2]
    have hmL := mellin_lowerTailKernel T hT hb (p : ℂ) hp0
    have hmL' := mellin_lowerTailKernel (fun t => 1 - T t) (measurable_const.sub hT)
      (fun t => ⟨by linarith [(hb t).2], by linarith [(hb t).1]⟩) (p : ℂ) hp0
    have hmE := hu_err.1 (p : ℂ) (by simpa using hpβ.trans (hβ₁₂.trans hβ₂₃))
    have hp1 := hasMellin_upperTailPowerKernel c₁ β₁ (p : ℂ) hpβ
    have hp2 := hasMellin_upperTailPowerKernel c₂ β₂ (p : ℂ) (hpβ.trans hβ₁₂)
    have hcomp : (p : ℂ) * (mellin (lowerTailKernel T) (p : ℂ) +
        mellin (lowerTailKernel (fun t => 1 - T t)) (p : ℂ)) = 1 := by
      have hsum := hasMellin_add hmL hmL'
      have heq_ind : (fun t => lowerTailKernel T t + lowerTailKernel (fun x => 1 - T x) t) =
          (Ioc (0 : ℝ) 1).indicator fun _ => (1 : ℂ) := by
        ext t; by_cases ht : t ∈ Ioc (0 : ℝ) 1
        · simp [lowerTailKernel, indicator_of_mem ht]
        · simp [lowerTailKernel, indicator_of_notMem ht]
      rw [heq_ind] at hsum
      rw [hsum.2.symm.trans (hasMellin_one_Ioc (s := (p : ℂ)) hp0).2,
        mul_one_div_cancel (ofReal_ne_zero.2 hp0.ne')]
    have hfull : mellin (fun t => (T t : ℂ)) (p : ℂ) =
        mellin (fun t => (lowerTailKernel T t + upperTailErrorKernel T c₁ c₂ β₁ β₂ t) +
          (upperTailPowerKernel c₁ β₁ t + upperTailPowerKernel c₂ β₂ t)) (p : ℂ) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => congrArg ((t : ℂ) ^ ((p : ℂ) - 1) • ·) ?_
      by_cases h1 : t ≤ 1
      · simp only [lowerTailKernel, upperTailErrorKernel, upperTailPowerKernel,
          indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht, h1⟩),
          indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from not_lt.2 h1), add_zero]
      · have h1' : 1 < t := lt_of_not_ge h1
        simp only [lowerTailKernel, upperTailErrorKernel, upperTailPowerKernel,
          indicator_of_notMem (show t ∉ Ioc (0 : ℝ) 1 from fun h => h1'.not_ge h.2),
          indicator_of_mem (show t ∈ Ioi (1 : ℝ) from h1')]
        push_cast; ring
    have hr_add := hasMellin_add hmL hmE
    have hp_add := hasMellin_add hp1.1 hp2.1
    rw [hfull, (hasMellin_add hr_add.1 hp_add.1).2, hr_add.2, hp_add.2, hp1.2, hp2.2]
    dsimp [r, inverseTailRemainder, twoTailRational]
    linear_combination hcomp
  refine ⟨hord_int, hord_diff, r, hr,
    MeromorphicOn.add (fun s _ => meromorphic_twoTailRational c₁ c₂ β₁ β₂ s) (hr.analyticOnNhd hopen₃).meromorphicOn,
    fun s hs => hformula hs, by simp [r, inverseTailRemainder],
    tendsto_twoTailRational_first c₁ c₂ β₁ β₂ hβ₁₂.ne r
      (hr.continuousOn.continuousAt (hopen₃.mem_nhds (hβ₁₂.trans hβ₂₃))),
    tendsto_twoTailRational_second c₁ c₂ β₁ β₂ hβ₁₂.ne r
      (hr.continuousOn.continuousAt (hopen₃.mem_nhds hβ₂₃))⟩

end DOZZ.Proofs
