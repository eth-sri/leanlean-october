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

The upper-tail estimate supplies the positive-strip holomorphic remainder.
Inverse moments extend its lower-tail correction through exponent zero. The residues
are punctured-neighborhood limits, so no values at the poles are asserted.
-/

@[expose] public section

open MeasureTheory Filter Topology Set Complex Asymptotics ProbabilityTheory
open scoped Real

namespace DOZZ.Proofs

/-- A measurable globally bounded kernel is locally integrable. -/
theorem locallyIntegrableOn_of_bound (g : ℝ → ℂ) (hg : AEStronglyMeasurable g volume)
    C (hC : 0 ≤ C) (hb : ∀ t, ‖g t‖ ≤ C) :
    LocallyIntegrableOn g (Ioi 0) := by
  apply (locallyIntegrableOn_const (c := C) (s := Ioi 0)).mono hg
  exact Eventually.of_forall fun t => (hb t).trans_eq (Real.norm_of_nonneg hC).symm

/-- Vanishing below one gives every power bound at the lower endpoint. -/
theorem isBigO_at_zero_of_eq_zero (g : ℝ → ℂ) (hg : ∀ t, t ≤ 1 → g t = 0) (b : ℝ) :
    g =O[𝓝[>] 0] (fun t : ℝ => t ^ (-b)) := by
  apply IsBigO.of_bound 0
  filter_upwards [((eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
    nhdsWithin_le_nhds)] with t ht
  rw [hg t ht.le, norm_zero, zero_mul]


/-- A power bound above one supplies the corresponding upper Mellin endpoint. -/
theorem isBigO_at_top_of_power_bound (g : ℝ → ℂ) (C β : ℝ)
    (hb : ∀ t, 1 ≤ t → ‖g t‖ ≤ C * t ^ (-β)) :
    g =O[atTop] (fun t : ℝ => t ^ (-β)) := by
  apply IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  exact (hb t ht).trans_eq (by rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)])

/-- Upper-tail Mellin convergence and holomorphy on the entire left half-plane. -/
theorem mellin_upper_kernel (g : ℝ → ℂ) (hg : AEStronglyMeasurable g volume)
    (C β : ℝ) (hC : 0 ≤ C) (hbound : ∀ t, ‖g t‖ ≤ C)
    (hzero : ∀ t, t ≤ 1 → g t = 0)
    (hpower : ∀ t, 1 ≤ t → ‖g t‖ ≤ C * t ^ (-β)) :
    (∀ s : ℂ, s.re < β → MellinConvergent g s) ∧
      DifferentiableOn ℂ (mellin g) {s | s.re < β} := by
  have hloc := locallyIntegrableOn_of_bound g hg C hC hbound
  have htop := isBigO_at_top_of_power_bound g C β hpower
  constructor
  · intro s hs
    exact mellinConvergent_of_isBigO_rpow hloc htop hs
      (isBigO_at_zero_of_eq_zero g hzero (s.re - 1)) (by linarith)
  · intro s hs
    exact (mellin_differentiableAt_of_isBigO_rpow hloc htop hs
      (isBigO_at_zero_of_eq_zero g hzero (s.re - 1)) (by linarith)).differentiableWithinAt







/-- The part of a real tail below one. -/
noncomputable def lowerTailKernel (T : ℝ → ℝ) : ℝ → ℂ :=
  (Ioc 0 1).indicator (fun t => (T t : ℂ))

/-- The upper-tail error after subtracting the two leading powers. -/
noncomputable def upperTailErrorKernel (T : ℝ → ℝ) (c₁ c₂ β₁ β₂ : ℝ) : ℝ → ℂ :=
  (Ioi 1).indicator (fun t => ((T t - c₁ * t ^ (-β₁) - c₂ * t ^ (-β₂) : ℝ) : ℂ))

/-- The leading upper-tail power kernel. -/
noncomputable def upperTailPowerKernel (c β : ℝ) : ℝ → ℂ :=
  (Ioi 1).indicator (fun t => ((c * t ^ (-β) : ℝ) : ℂ))


/-- The subtracted upper-tail kernel is measurable. -/
theorem measurable_upperTailErrorKernel T (hT : Measurable T)
    c₁ c₂ β₁ β₂ : Measurable (upperTailErrorKernel T c₁ c₂ β₁ β₂) :=
  (Complex.continuous_ofReal.measurable.comp
    ((hT.sub ((measurable_id.pow_const (-β₁)).const_mul c₁)).sub
      ((measurable_id.pow_const (-β₂)).const_mul c₂))).indicator measurableSet_Ioi



/-- The subtracted upper-tail kernel retains the stated faster power bound. -/
theorem norm_upperTailErrorKernel_le_power (T : ℝ → ℝ) (c₁ c₂ c₃ β₁ β₂ β₃ : ℝ)
    (hc₃ : 0 ≤ c₃)
    (htail : ∀ t : ℝ, 1 ≤ t → |T t - c₁ * t ^ (-β₁) - c₂ * t ^ (-β₂)| ≤ c₃ * t ^ (-β₃))
    t (ht : 1 ≤ t) :
    ‖upperTailErrorKernel T c₁ c₂ β₁ β₂ t‖ ≤ c₃ * t ^ (-β₃) := by
  by_cases h : t ∈ Ioi (1 : ℝ)
  · rw [upperTailErrorKernel, indicator_of_mem h, norm_real, Real.norm_eq_abs]
    exact htail t ht
  · rw [upperTailErrorKernel, indicator_of_notMem h, norm_zero]
    exact mul_nonneg hc₃ (Real.rpow_nonneg (by linarith) _)

/-- Positive decay makes the upper error globally bounded. -/
theorem norm_upperTailErrorKernel_le (T : ℝ → ℝ) (c₁ c₂ c₃ β₁ β₂ β₃ : ℝ)
    (hc₃ : 0 ≤ c₃) (hβ₃ : 0 ≤ β₃)
    (htail : ∀ t : ℝ, 1 ≤ t → |T t - c₁ * t ^ (-β₁) - c₂ * t ^ (-β₂)| ≤ c₃ * t ^ (-β₃))
    t : ‖upperTailErrorKernel T c₁ c₂ β₁ β₂ t‖ ≤ c₃ := by
  by_cases ht : 1 < t
  · exact (norm_upperTailErrorKernel_le_power T c₁ c₂ c₃ β₁ β₂ β₃ hc₃ htail t ht.le).trans
      ((mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos ht.le (neg_nonpos.mpr hβ₃))
        hc₃).trans_eq (mul_one _))
  · rw [upperTailErrorKernel, indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from ht), norm_zero]
    exact hc₃

/-- The upper error transform converges and is holomorphic to the left of the third exponent. -/
theorem mellin_upperTailErrorKernel T (hT : Measurable T)
    (c₁ c₂ c₃ β₁ β₂ β₃ : ℝ) (hc₃ : 0 ≤ c₃) (hβ₃ : 0 ≤ β₃)
    (htail : ∀ t : ℝ, 1 ≤ t → |T t - c₁ * t ^ (-β₁) - c₂ * t ^ (-β₂)| ≤ c₃ * t ^ (-β₃)) :
    (∀ s : ℂ, s.re < β₃ → MellinConvergent (upperTailErrorKernel T c₁ c₂ β₁ β₂) s) ∧
      DifferentiableOn ℂ (mellin (upperTailErrorKernel T c₁ c₂ β₁ β₂)) {s | s.re < β₃} := by
  apply mellin_upper_kernel _ (measurable_upperTailErrorKernel T hT c₁ c₂ β₁ β₂).aestronglyMeasurable
    c₃ β₃ hc₃ (norm_upperTailErrorKernel_le T c₁ c₂ c₃ β₁ β₂ β₃ hc₃ hβ₃ htail)
  · intro t ht
    exact indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from not_lt.mpr ht) _
  · exact norm_upperTailErrorKernel_le_power T c₁ c₂ c₃ β₁ β₂ β₃ hc₃ htail








/-- The positive-strip remainder after upper-tail subtraction. -/
noncomputable def twoTailRemainder (T : ℝ → ℝ) (c₁ c₂ β₁ β₂ : ℝ) (s : ℂ) : ℂ :=
  s * (mellin (lowerTailKernel T) s + mellin (upperTailErrorKernel T c₁ c₂ β₁ β₂) s)








/-- The lower-probability remainder extends the upper-error Mellin remainder through zero. -/
noncomputable def inverseTailRemainder (T : ℝ → ℝ) (c₁ c₂ β₁ β₂ : ℝ) (s : ℂ) : ℂ :=
  1 - s * mellin (lowerTailKernel (fun t => 1 - T t)) s +
    s * mellin (upperTailErrorKernel T c₁ c₂ β₁ β₂) s






theorem complexMoment_two_tail_residues_of_inverse_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : AEMeasurable Y P) (hpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hinv : ∀ q : ℝ, 0 < q → Integrable (fun ω => Y ω ^ (-q)) P)
    (c₁ c₂ c₃ β₁ β₂ β₃ : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ < β₂) (hβ₂₃ : β₂ < β₃)
    (htail : ∀ t : ℝ, 1 ≤ t →
      |realUpperTail P Y hY t - c₁ * t ^ (-β₁) - c₂ * t ^ (-β₂)| ≤ c₃ * t ^ (-β₃)) :
    (∀ s : ℂ, s.re < β₁ → Integrable (fun ω => (Y ω : ℂ) ^ s) P) ∧
    ∃ r : ℂ → ℂ, DifferentiableOn ℂ r {s | s.re < β₃} ∧
      ∀ s : ℂ, s.re < β₁ →
        (∫ ω, (Y ω : ℂ) ^ s ∂P) = twoTailRational c₁ c₂ β₁ β₂ s + r s := by
  have isOpen_realPart_lt β : IsOpen {s : ℂ | s.re < β} := isOpen_lt Complex.continuous_re continuous_const
  have complexMoment_real_eq_mellin_tail (hpos : ∀ᵐ ω ∂P, 0 ≤ Y ω) (p : ℝ) (hp : 0 < p) (hm : MellinConvergent (fun t => (realUpperTail P Y hY t : ℂ)) (p : ℂ)) : Integrable (fun ω => Y ω ^ p) P ∧ (∫ ω, (Y ω : ℂ) ^ (p : ℂ) ∂P) = (p : ℂ) * mellin (fun t => (realUpperTail P Y hY t : ℂ)) (p : ℂ) := by
    have ht := (fun (T : ℝ → ℝ) (hT : Measurable T) (hn : ∀ t, 0 ≤ T t) (p : ℝ) (hm : MellinConvergent (fun t => (T t : ℂ)) (p : ℂ)) => by apply ((mellin_convergent_iff_norm (T := Ioi 0) Subset.rfl measurableSet_Ioi ((Complex.continuous_ofReal.measurable.comp hT).aestronglyMeasurable.restrict)).mp hm).congr; filter_upwards with t; change t ^ (p - 1) * ‖(T t : ℂ)‖ = T t * t ^ (p - 1); rw [norm_real, Real.norm_of_nonneg (hn t), mul_comm]) (realUpperTail P Y hY) (measurable_realUpperTail P Y hY)
      (fun t => (realUpperTail_bounds P Y hY t).1) p hm
    have hreal := integral_rpow_eq_tail_of_integrable P Y hY hpos p hp ht
    refine ⟨hreal.1, ?_⟩
    rw [integral_congr_ae (hpos.mono fun ω hω => (ofReal_cpow hω p).symm), integral_complex_ofReal, hreal.2, ofReal_mul]
    congr 1
    rw [mellin, ← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change ((realUpperTail P Y hY t * t ^ (p - 1) : ℝ) : ℂ) =
      (t : ℂ) ^ ((p : ℂ) - 1) * (realUpperTail P Y hY t : ℂ)
    rw [ofReal_mul, ofReal_cpow ht.le, ofReal_sub, ofReal_one, mul_comm]
  have hasMellin_upperTailPowerKernel (c : ℝ) (β : ℝ) (s : ℂ) (hs : s.re < β) : HasMellin (upperTailPowerKernel c β) s ((c : ℂ) / ((β : ℂ) - s)) := by
    let a := s - 1 - (β : ℂ)
    have ha : a.re < -1 := by dsimp [a]; linarith
    have heq : (fun t : ℝ => (t : ℂ) ^ (s - 1) • upperTailPowerKernel c β t) =
        (Ioi (1 : ℝ)).indicator (fun t => (c : ℂ) * (t : ℂ) ^ a) := by
      funext t
      by_cases ht : t ∈ Ioi (1 : ℝ)
      · have htpos : 0 < t := lt_trans zero_lt_one ht
        rw [upperTailPowerKernel, indicator_of_mem ht, indicator_of_mem ht,
          ofReal_mul, ofReal_cpow htpos.le, ofReal_neg, smul_eq_mul]
        rw [mul_left_comm, ← cpow_add _ _ (ofReal_ne_zero.mpr htpos.ne')]
        rfl
      · rw [upperTailPowerKernel, indicator_of_notMem ht, indicator_of_notMem ht, smul_zero]
    have hsub : Ioi (1 : ℝ) ⊆ Ioi 0 := fun _ ht => lt_trans zero_lt_one ht
    have hint : IntegrableOn (fun t : ℝ => (c : ℂ) * (t : ℂ) ^ a) (Ioi 1) :=
      (integrableOn_Ioi_cpow_of_lt ha zero_lt_one).const_mul _
    constructor
    · rw [MellinConvergent, heq]
      exact hint.integrable_indicator measurableSet_Ioi |>.integrableOn
    · rw [mellin, heq, integral_indicator measurableSet_Ioi,
        Measure.restrict_restrict_of_subset hsub, integral_const_mul,
        integral_Ioi_cpow_of_lt ha zero_lt_one, ofReal_one, one_cpow]
      rw [(show a + 1 = -((β : ℂ) - s) by dsimp [a]; ring), div_neg, neg_div, neg_neg]
      ring
  have mellin_full_tail T (hT : Measurable T) (hb : ∀ t, 0 ≤ T t ∧ T t ≤ 1) (C : ℝ) (β : ℝ) (htop : ∀ t, 1 ≤ t → T t ≤ C * t ^ (-β)) (s : ℂ) (hs : 0 < s.re ∧ s.re < β) : MellinConvergent (fun t => (T t : ℂ)) s := by
    have hg : AEStronglyMeasurable (fun t => (T t : ℂ)) volume :=
      (Complex.continuous_ofReal.measurable.comp hT).aestronglyMeasurable
    have hbound : ∀ t, ‖(T t : ℂ)‖ ≤ 1 := fun t => by
      rw [norm_real, Real.norm_of_nonneg (hb t).1]; exact (hb t).2
    apply mellinConvergent_of_isBigO_rpow (locallyIntegrableOn_of_bound _ hg 1 zero_le_one hbound)
      (isBigO_at_top_of_power_bound _ C β fun t ht => by
        rw [norm_real, Real.norm_of_nonneg (hb t).1]; exact htop t ht) hs.2
      (b := 0)
    · apply IsBigO.of_bound 1
      exact Eventually.of_forall fun t => by
        simpa only [neg_zero, Real.rpow_zero, norm_one, one_mul] using hbound t
    · exact hs.1
  have tail_le_first_power (T : ℝ → ℝ) (c₁ : ℝ) (c₂ : ℝ) (c₃ : ℝ) (β₁ : ℝ) (β₂ : ℝ) (β₃ : ℝ) (_hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃) (hβ₁₂ : β₁ ≤ β₂) (hβ₂₃ : β₂ ≤ β₃) (htail : ∀ t : ℝ, 1 ≤ t → |T t - c₁ * t ^ (-β₁) - c₂ * t ^ (-β₂)| ≤ c₃ * t ^ (-β₃)) t (ht : 1 ≤ t) : T t ≤ (c₁ + c₂ + c₃) * t ^ (-β₁) := by
    have := (le_abs_self (T t - c₁ * t ^ (-β₁) - c₂ * t ^ (-β₂))).trans (htail t ht)
    have := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le ht (neg_le_neg hβ₁₂)) hc₂
    have := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le ht (neg_le_neg (hβ₁₂.trans hβ₂₃))) hc₃
    nlinarith
  have norm_lowerTailKernel_le (T : ℝ → ℝ) (hT : ∀ t, 0 ≤ T t ∧ T t ≤ 1) t : ‖lowerTailKernel T t‖ ≤ 1 := by
    by_cases ht : t ∈ Ioc (0 : ℝ) 1
    · rw [lowerTailKernel, indicator_of_mem ht, norm_real, Real.norm_of_nonneg (hT t).1]
      exact (hT t).2
    · rw [lowerTailKernel, indicator_of_notMem ht, norm_zero]
      exact zero_le_one
  have measurable_lowerTailKernel T (hT : Measurable T) : Measurable (lowerTailKernel T) := (Complex.continuous_ofReal.measurable.comp hT).indicator measurableSet_Ioc
  have isBigO_at_top_of_eq_zero (g : ℝ → ℂ) (hg : ∀ t, 1 < t → g t = 0) (a : ℝ) : g =O[atTop] (fun t : ℝ => t ^ (-a)) := by
    apply IsBigO.of_bound 0
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with t ht
    rw [hg t ht, norm_zero, zero_mul]
  have mellin_lowerTailKernel T (hT : Measurable T) (hb : ∀ t, 0 ≤ T t ∧ T t ≤ 1) : (∀ s : ℂ, 0 < s.re → MellinConvergent (lowerTailKernel T) s) ∧ DifferentiableOn ℂ (mellin (lowerTailKernel T)) {s | 0 < s.re} := by
    have mellin_bounded_lower_kernel (g : ℝ → ℂ) (hg : AEStronglyMeasurable g volume) C (hC : 0 ≤ C) (hbound : ∀ t, ‖g t‖ ≤ C) (hzero : ∀ t, 1 < t → g t = 0) : (∀ s : ℂ, 0 < s.re → MellinConvergent g s) ∧ DifferentiableOn ℂ (mellin g) {s | 0 < s.re} := by
      have mellin_lower_kernel (b : ℝ) (hC : 0 ≤ C) (hbound : ∀ t, ‖g t‖ ≤ C) (hzero : ∀ t, 1 < t → g t = 0) (hpower : g =O[𝓝[>] 0] (fun t => t ^ (-b))) : (∀ s : ℂ, b < s.re → MellinConvergent g s) ∧ DifferentiableOn ℂ (mellin g) {s | b < s.re} := by
        have hloc := locallyIntegrableOn_of_bound g hg C hC hbound
        constructor
        · intro s hs
          exact mellinConvergent_of_isBigO_rpow hloc
            (isBigO_at_top_of_eq_zero g hzero (s.re + 1)) (by linarith) hpower hs
        · intro s hs
          exact (mellin_differentiableAt_of_isBigO_rpow hloc
            (isBigO_at_top_of_eq_zero g hzero (s.re + 1)) (by linarith) hpower hs).differentiableWithinAt
      apply mellin_lower_kernel 0 hC hbound hzero
      apply IsBigO.of_bound C
      exact Eventually.of_forall fun t => by simpa only [neg_zero, Real.rpow_zero, norm_one, mul_one] using hbound t
    apply mellin_bounded_lower_kernel (lowerTailKernel T)
      (measurable_lowerTailKernel T hT).aestronglyMeasurable 1 zero_le_one
      (norm_lowerTailKernel_le T hb)
    intro t ht
    exact indicator_of_notMem (show t ∉ Ioc (0 : ℝ) 1 from fun h => (not_le.mpr ht) h.2) _
  have differentiableOn_inverseTailRemainder (hc₃ : 0 ≤ c₃) (hβ₃ : 0 ≤ β₃) (htail : ∀ t : ℝ, 1 ≤ t → |realUpperTail P Y hY t - c₁ * t ^ (-β₁) - c₂ * t ^ (-β₂)| ≤ c₃ * t ^ (-β₃)) : DifferentiableOn ℂ (inverseTailRemainder (realUpperTail P Y hY) c₁ c₂ β₁ β₂) {s : ℂ | s.re < β₃} := by
    have differentiable_mellin_lowerProbability : (∀ s : ℂ, MellinConvergent (lowerTailKernel (fun t => 1 - realUpperTail P Y hY t)) s) ∧ Differentiable ℂ (mellin (lowerTailKernel (fun t => 1 - realUpperTail P Y hY t))) := by
      have lowerProbability_le_inverseMoment (q : ℝ) (hq : 0 < q) (hint : Integrable (fun ω => Y ω ^ (-q)) P) t (ht : 0 < t) : 1 - realUpperTail P Y hY t ≤ (∫ ω, Y ω ^ (-q) ∂P) * t ^ q := by
        have lowerProbability_eq_integral_indicator : 1 - realUpperTail P Y hY t = ∫ ω, {ω | Y ω ≤ t}.indicator (fun _ => (1 : ℝ)) ω ∂P := by
          have hl : NullMeasurableSet {ω | Y ω ≤ t} P := hY.nullMeasurableSet_preimage measurableSet_Iic
          rw [integral_indicator₀ hl, integral_const]
          simp only [smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ]
          rw [(show {ω | Y ω ≤ t} = {ω | t < Y ω}ᶜ by ext ω; simp only [mem_ofPred_eq, mem_compl_iff, not_lt])]
          exact (probReal_compl_eq_one_sub₀ (hY.nullMeasurableSet_preimage measurableSet_Ioi)).symm
        have hbound : ∀ᵐ ω ∂P, {ω | Y ω ≤ t}.indicator (fun _ => (1 : ℝ)) ω ≤
            t ^ q * Y ω ^ (-q) := by
          filter_upwards [hpos] with ω hω
          by_cases h : Y ω ≤ t
          · rw [indicator_of_mem (show ω ∈ {ω | Y ω ≤ t} from h)]
            exact (show t ^ q * t ^ (-q) = 1 by rw [← Real.rpow_add ht, add_neg_cancel, Real.rpow_zero]) ▸ (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hω h (neg_nonpos.mpr hq.le)) (Real.rpow_pos_of_pos ht q).le)
          · rw [indicator_of_notMem (show ω ∉ {ω | Y ω ≤ t} from h)]
            exact mul_nonneg (Real.rpow_pos_of_pos ht q).le (Real.rpow_pos_of_pos hω (-q)).le
        rw [lowerProbability_eq_integral_indicator]
        have h := integral_mono_ae ((integrable_const 1).indicator₀ (hY.nullMeasurableSet_preimage measurableSet_Iic) : Integrable ({ω | Y ω ≤ t}.indicator (fun _ => (1 : ℝ))) P) (hint.const_mul (t ^ q)) hbound
        rw [integral_const_mul, mul_comm] at h
        exact h
      have lowerProbability_bounds t : 0 ≤ 1 - realUpperTail P Y hY t ∧ 1 - realUpperTail P Y hY t ≤ 1 := by
        have := realUpperTail_bounds P Y hY t
        constructor <;> linarith
      let T := fun t => 1 - realUpperTail P Y hY t
      have hb := lowerProbability_bounds
      have hlocal : ∀ s : ℂ, MellinConvergent (lowerTailKernel T) s ∧
          DifferentiableAt ℂ (mellin (lowerTailKernel T)) s := by
        intro s
        let q := max 1 (1 - s.re)
        have hq : 0 < q := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
        have hs : -q < s.re := by have := le_max_right (1 : ℝ) (1 - s.re); dsimp [q]; linarith
        have hpower : lowerTailKernel T =O[𝓝[>] 0] (fun t => t ^ (-(-q))) := by
          apply IsBigO.of_bound (∫ ω, Y ω ^ (-q) ∂P)
          filter_upwards [self_mem_nhdsWithin] with t ht
          change 0 < t at ht
          rw [neg_neg, Real.norm_of_nonneg (Real.rpow_pos_of_pos ht q).le]
          by_cases h : t ∈ Ioc (0 : ℝ) 1
          · rw [lowerTailKernel, indicator_of_mem h, norm_real, Real.norm_of_nonneg (hb t).1]
            exact lowerProbability_le_inverseMoment q hq (hinv q hq) t ht
          · rw [lowerTailKernel, indicator_of_notMem h, norm_zero]
            exact mul_nonneg (integral_nonneg_of_ae (hpos.mono fun ω hω => (Real.rpow_pos_of_pos hω _).le)) (Real.rpow_pos_of_pos ht q).le
        have hloc := locallyIntegrableOn_of_bound (lowerTailKernel T)
          (measurable_lowerTailKernel T (measurable_const.sub (measurable_realUpperTail P Y hY))).aestronglyMeasurable 1 zero_le_one (norm_lowerTailKernel_le T hb)
        have htop := isBigO_at_top_of_eq_zero (lowerTailKernel T) (by intro t ht; exact indicator_of_notMem (show t ∉ Ioc (0 : ℝ) 1 from fun h => (not_le.mpr ht) h.2) _) (s.re + 1)
        exact ⟨mellinConvergent_of_isBigO_rpow hloc htop (by linarith) hpower hs,
          mellin_differentiableAt_of_isBigO_rpow hloc htop (by linarith) hpower hs⟩
      exact ⟨fun s => (hlocal s).1, fun s => (hlocal s).2⟩
    exact ((differentiableOn_const (1 : ℂ)).sub (differentiableOn_id.mul ((differentiable_mellin_lowerProbability).2.differentiableOn))).add
      (differentiableOn_id.mul ((mellin_upperTailErrorKernel (realUpperTail P Y hY) (measurable_realUpperTail P Y hY) c₁ c₂ c₃ β₁ β₂ β₃ hc₃ hβ₃ htail).2))
  have integrable_real_power_of_two_tail_inverse (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃) (hβ₁₂ : β₁ ≤ β₂) (hβ₂₃ : β₂ ≤ β₃) (htail : ∀ t : ℝ, 1 ≤ t → |realUpperTail P Y hY t - c₁ * t ^ (-β₁) - c₂ * t ^ (-β₂)| ≤ c₃ * t ^ (-β₃)) p (hp : p < β₁) : Integrable (fun ω => Y ω ^ p) P := by
    by_cases h : p < 0
    · simpa only [neg_neg] using hinv (-p) (neg_pos.mpr h)
    · by_cases hzero : p = 0
      · simp only [hzero, Real.rpow_zero]
        exact integrable_const 1
      · have hposp : 0 < p := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hzero)
        exact (complexMoment_real_eq_mellin_tail (hpos.mono fun _ h => h.le) p hposp
          (mellin_full_tail (realUpperTail P Y hY) (measurable_realUpperTail P Y hY)
            (realUpperTail_bounds P Y hY) (c₁ + c₂ + c₃) β₁ (tail_le_first_power (realUpperTail P Y hY) c₁ c₂ c₃ β₁ β₂ β₃ hc₁ hc₂ hc₃ hβ₁₂ hβ₂₃ htail) (p : ℂ) ⟨hposp, hp⟩)).1
  have eqOn_realPart_lt_of_positive_real (β : ℝ) (hβ : 0 < β) (f : ℂ → ℂ) (g : ℂ → ℂ) (hf : DifferentiableOn ℂ f {s : ℂ | s.re < β}) (hg : DifferentiableOn ℂ g {s : ℂ | s.re < β}) (heq : ∀ p : ℝ, 0 < p → p < β → f (p : ℂ) = g (p : ℂ)) : EqOn f g {s : ℂ | s.re < β} := by
    have ha : ((β / 2 : ℝ) : ℂ) ∈ {s : ℂ | s.re < β} := half_lt_self hβ
    apply (hf.analyticOnNhd (isOpen_realPart_lt β)).eqOn_of_preconnected_of_frequently_eq
      (hg.analyticOnNhd (isOpen_realPart_lt β)) ((convex_Iio β).linear_preimage Complex.reLm).isPreconnected ha
    apply frequently_eq_of_real_interval (β / 2) (β / 2) (half_pos hβ)
    intro p hp
    have := abs_lt.mp hp
    apply heq p <;> linarith
  have inverseTailRemainder_eq_twoTailRemainder T (hT : Measurable T) (hb : ∀ t, 0 ≤ T t ∧ T t ≤ 1) (c₁ : ℝ) (c₂ : ℝ) (β₁ : ℝ) (β₂ : ℝ) (s : ℂ) (hs : 0 < s.re) : inverseTailRemainder T c₁ c₂ β₁ β₂ s = twoTailRemainder T c₁ c₂ β₁ β₂ s := by
    have lowerTail_mellin_complement : s * (mellin (lowerTailKernel T) s + mellin (lowerTailKernel (fun t => 1 - T t)) s) = 1 := by
      have lowerTailKernel_add_complement : (fun t => lowerTailKernel T t + lowerTailKernel (fun x => 1 - T x) t) = (Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℂ)) := by
        funext t
        by_cases ht : t ∈ Ioc (0 : ℝ) 1
        · simp only [lowerTailKernel, indicator_of_mem ht]
          push_cast
          ring
        · simp only [lowerTailKernel, indicator_of_notMem ht, add_zero]
      have hq : ∀ t, 0 ≤ 1 - T t ∧ 1 - T t ≤ 1 := by
        intro t
        have := hb t
        constructor <;> linarith
      have hsum := hasMellin_add ((mellin_lowerTailKernel T hT hb).1 s hs)
        ((mellin_lowerTailKernel (fun t => 1 - T t) (measurable_const.sub hT) hq).1 s hs)
      rw [lowerTailKernel_add_complement] at hsum
      rw [(hsum.2.symm.trans (hasMellin_one_Ioc hs).2), mul_one_div_cancel (fun h => (ne_of_gt hs) (congrArg Complex.re h))]
    unfold inverseTailRemainder twoTailRemainder
    linear_combination -(lowerTail_mellin_complement)
  have differentiableOn_twoTailRational_left (hβ : β₁ ≤ β₂) : DifferentiableOn ℂ (twoTailRational c₁ c₂ β₁ β₂) {s : ℂ | s.re < β₁} := by
    intro s hs
    change s.re < β₁ at hs
    have hne₁ : (β₁ : ℂ) - s ≠ 0 := by
      intro h
      have hr := congrArg Complex.re (sub_eq_zero.mp h)
      simp only [ofReal_re] at hr
      linarith
    have hne₂ : (β₂ : ℂ) - s ≠ 0 := by
      intro h
      have hr := congrArg Complex.re (sub_eq_zero.mp h)
      simp only [ofReal_re] at hr
      linarith
    exact (((differentiableAt_const (c := (c₁ : ℂ))).mul differentiableAt_id).div
      ((differentiableAt_const (c := (β₁ : ℂ))).sub differentiableAt_id) hne₁ |>.add
      (((differentiableAt_const (c := (c₂ : ℂ))).mul differentiableAt_id).div
        ((differentiableAt_const (c := (β₂ : ℂ))).sub differentiableAt_id) hne₂)).differentiableWithinAt
  have mellin_tail_decomposition T (c₁ : ℝ) (c₂ : ℝ) (β₁ : ℝ) (β₂ : ℝ) (s : ℂ) (h₁ : s.re < β₁) (h₂ : s.re < β₂) (hl : MellinConvergent (lowerTailKernel T) s) (he : MellinConvergent (upperTailErrorKernel T c₁ c₂ β₁ β₂) s) : s * mellin (fun t => (T t : ℂ)) s = twoTailRational c₁ c₂ β₁ β₂ s + s * (mellin (lowerTailKernel T) s + mellin (upperTailErrorKernel T c₁ c₂ β₁ β₂) s) := by
    have tail_kernel_decomposition : EqOn (fun t => (T t : ℂ)) (fun t => (lowerTailKernel T t + upperTailErrorKernel T c₁ c₂ β₁ β₂ t) + (upperTailPowerKernel c₁ β₁ t + upperTailPowerKernel c₂ β₂ t)) (Ioi 0) := by
      intro t ht
      change (T t : ℂ) = (lowerTailKernel T t + upperTailErrorKernel T c₁ c₂ β₁ β₂ t) +
        (upperTailPowerKernel c₁ β₁ t + upperTailPowerKernel c₂ β₂ t)
      by_cases h : t ≤ 1
      · simp only [lowerTailKernel, upperTailErrorKernel, upperTailPowerKernel,
          indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht, h⟩),
          indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from not_lt.mpr h)]
        simp only [add_zero]
      · have h1 : 1 < t := lt_of_not_ge h
        simp only [lowerTailKernel, upperTailErrorKernel, upperTailPowerKernel,
          indicator_of_notMem (show t ∉ Ioc (0 : ℝ) 1 from fun h => (not_le.mpr h1) h.2),
          indicator_of_mem (show t ∈ Ioi (1 : ℝ) from h1)]
        push_cast
        ring
    have hp₁ := hasMellin_upperTailPowerKernel c₁ β₁ s h₁
    have hp₂ := hasMellin_upperTailPowerKernel c₂ β₂ s h₂
    have hr := hasMellin_add hl he
    have hp := hasMellin_add hp₁.1 hp₂.1
    have hfull : mellin (fun t => (T t : ℂ)) s =
        mellin (fun t => lowerTailKernel T t + upperTailErrorKernel T c₁ c₂ β₁ β₂ t +
          (upperTailPowerKernel c₁ β₁ t + upperTailPowerKernel c₂ β₂ t)) s := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact congrArg (fun w : ℂ => (t : ℂ) ^ (s - 1) • w)
        (tail_kernel_decomposition ht)
    rw [hfull, (hasMellin_add hr.1 hp.1).2, hr.2, hp.2, hp₁.2, hp₂.2, twoTailRational]
    ring
  have complexMoments_of_positive_real_powers S (hS : IsOpen S) (hmom : ∀ p ∈ S, Integrable (fun ω => Y ω ^ p) P) : (∀ s : ℂ, s.re ∈ S → Integrable (fun ω => (Y ω : ℂ) ^ s) P) ∧ DifferentiableOn ℂ (fun s : ℂ => ∫ ω, (Y ω : ℂ) ^ s ∂P) {s | s.re ∈ S} := by
    have subset_interior_integrableExpSet_log : S ⊆ interior (integrableExpSet (fun ω => Real.log (Y ω)) P) := by
      rw [hS.subset_interior_iff]
      intro p hp
      exact (fun p hp => by apply hp.congr; filter_upwards [hpos] with ω hω; rw [Real.rpow_def_of_pos hω, mul_comm]) p (hmom p hp)
    have hsub := subset_interior_integrableExpSet_log
    constructor
    · intro s hs
      apply (integrable_cexp_mul_of_re_mem_integrableExpSet hY.log (interior_subset (hsub hs))).congr
      filter_upwards [hpos] with ω hω
      rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hω.ne'), ← ofReal_log hω.le, mul_comm]
    · exact (differentiableOn_complexMGF.mono (fun s hs => hsub hs)).congr
        (fun s _ => (fun s => by apply integral_congr_ae; filter_upwards [hpos] with ω hω; rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hω.ne'), ← ofReal_log hω.le, mul_comm]) s)
  let T := realUpperTail P Y hY
  have hT := measurable_realUpperTail P Y hY
  have hb := realUpperTail_bounds P Y hY
  have hβ₃ := hβ₁.trans (hβ₁₂.trans hβ₂₃)
  have hord := complexMoments_of_positive_real_powers (Iio β₁) isOpen_Iio (integrable_real_power_of_two_tail_inverse hc₁.le hc₂.le hc₃.le hβ₁₂.le hβ₂₃.le htail)
  let r := inverseTailRemainder T c₁ c₂ β₁ β₂
  have hr := differentiableOn_inverseTailRemainder hc₃.le hβ₃.le htail
  have hformula : EqOn (fun s : ℂ => ∫ ω, (Y ω : ℂ) ^ s ∂P)
      (fun s => twoTailRational c₁ c₂ β₁ β₂ s + r s) {s : ℂ | s.re < β₁} := by
    apply eqOn_realPart_lt_of_positive_real β₁ hβ₁ _ _ hord.2
      ((differentiableOn_twoTailRational_left hβ₁₂.le).add (hr.mono (fun _ hs => hs.trans (hβ₁₂.trans hβ₂₃))))
    intro p hp hpβ
    change (∫ ω, (Y ω : ℂ) ^ (p : ℂ) ∂P) = twoTailRational c₁ c₂ β₁ β₂ (p : ℂ) +
      inverseTailRemainder T c₁ c₂ β₁ β₂ (p : ℂ)
    rw [(inverseTailRemainder_eq_twoTailRemainder T hT hb c₁ c₂ β₁ β₂ (p : ℂ) hp), (complexMoment_real_eq_mellin_tail (hpos.mono fun _ h => h.le) p hp
      (mellin_full_tail T hT hb (c₁ + c₂ + c₃) β₁ (tail_le_first_power T c₁ c₂ c₃ β₁ β₂ β₃ hc₁.le hc₂.le hc₃.le hβ₁₂.le hβ₂₃.le htail) (p : ℂ) ⟨hp, hpβ⟩)).2]
    exact mellin_tail_decomposition T c₁ c₂ β₁ β₂ (p : ℂ) hpβ (hpβ.trans hβ₁₂)
      ((mellin_lowerTailKernel T hT hb).1 _ hp)
      ((mellin_upperTailErrorKernel T hT c₁ c₂ c₃ β₁ β₂ β₃ hc₃.le hβ₃.le htail).1 _
        (hpβ.trans (hβ₁₂.trans hβ₂₃)))
  exact ⟨hord.1, r, hr, fun s hs => hformula hs⟩

end DOZZ.Proofs
