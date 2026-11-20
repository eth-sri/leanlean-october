/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.WardPsi
import DOZZ.GMC.MeasurableIntegrals

/-! # Real mixed masses and their tilts

The real mixed mass and the untilted root-derivative functional, their measurability as functions
of the two measures, and the factorization of their tilts at a root. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The real mixed mass `∫ ρ k₁ dm₁ + ∫ (1 - ρ) k₂ dm₂`. -/
noncomputable def bpzMixedReal (ρ k₁ k₂ : ℂ → ℝ) (m₁ m₂ : Measure ℂ) : ℝ :=
  ∫ y, ρ y * k₁ y ∂m₁ + ∫ y, (1 - ρ y) * k₂ y ∂m₂

/-- The untilted root-derivative functional in a real direction `v`. -/
noncomputable def bpzMixedDerivReal (γ r : ℝ) (ρ k₁ k₂ : ℂ → ℝ) (x v : ℂ)
    (m₁ m₂ : Measure ℂ) : ℝ :=
  ∫ y, ρ y * k₁ y * (γ ^ 2 * bpzLamDeriv r (x - y) v) ∂m₁ +
    ∫ y, (1 - ρ y) * k₂ y * (γ ^ 2 * bpzTruncLogDeriv r (x - y) v) ∂m₂

/-- The Bochner integral of a fixed measurable function is measurable in the measure. -/
theorem measurable_integral_measure {g : ℂ → ℝ} (hg : Measurable g) :
    Measurable (fun m : Measure ℂ => ∫ y, g y ∂m) := by
  set A : Set (Measure ℂ) := {m | ∫⁻ y, ENNReal.ofReal |g y| ∂m < ⊤} with hA
  have hAm : MeasurableSet A :=
    measurableSet_lt (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp
      (continuous_abs.measurable.comp hg))) measurable_const
  have heq : (fun m : Measure ℂ => ∫ y, g y ∂m) = A.indicator (fun m =>
      (∫⁻ y, ENNReal.ofReal (g y) ∂m).toReal - (∫⁻ y, ENNReal.ofReal (-g y) ∂m).toReal) := by
    funext m
    by_cases hm : m ∈ A
    · rw [Set.indicator_of_mem hm]
      have hI : Integrable g m := by
        refine ⟨hg.aestronglyMeasurable, ?_⟩
        rw [hasFiniteIntegral_iff_norm]
        assumption
      exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hI
    · rw [Set.indicator_of_notMem hm]
      apply integral_undef
      intro hI
      apply hm
      have := hI.2
      rw [hasFiniteIntegral_iff_norm] at this
      assumption
  rw [heq]
  refine Measurable.indicator ?_ hAm
  fun_prop

theorem measurable_bpzMixedReal {ρ k₁ k₂ : ℂ → ℝ} (hρm : Measurable ρ) (hk₁ : Measurable k₁)
    (hk₂ : Measurable k₂) :
    Measurable (fun q : Measure ℂ × Measure ℂ => bpzMixedReal ρ k₁ k₂ q.1 q.2) :=
  ((measurable_integral_measure (hρm.mul hk₁)).comp measurable_fst).add
    ((measurable_integral_measure ((measurable_const.sub hρm).mul hk₂)).comp measurable_snd)

theorem measurable_bpzMixedDerivReal {γ r : ℝ} {ρ k₁ k₂ : ℂ → ℝ} (hρm : Measurable ρ)
    (hk₁ : Measurable k₁) (hk₂ : Measurable k₂) (x v : ℂ) :
    Measurable (fun q : Measure ℂ × Measure ℂ => bpzMixedDerivReal γ r ρ k₁ k₂ x v q.1 q.2) := by
  have h1 : Measurable fun y => ρ y * k₁ y * (γ ^ 2 * bpzLamDeriv r (x - y) v) :=
    (hρm.mul hk₁).mul (measurable_const.mul ((ContinuousLinearMap.apply ℝ ℝ v).continuous
      |>.measurable.comp ((measurable_bpzLamDeriv r).comp (measurable_const.sub measurable_id))))
  have h2 : Measurable fun y => (1 - ρ y) * k₂ y * (γ ^ 2 * bpzTruncLogDeriv r (x - y) v) :=
    ((measurable_const.sub hρm).mul hk₂).mul (measurable_const.mul
      ((ContinuousLinearMap.apply ℝ ℝ v).continuous.measurable.comp
        ((measurable_bpzTruncLogDeriv r).comp (measurable_const.sub measurable_id))))
  exact ((measurable_integral_measure h1).comp measurable_fst).add
    ((measurable_integral_measure h2).comp measurable_snd)

private theorem integral_withDensity_exp_split (m : Measure ℂ) (f : ℂ → ℝ)
    (a : ℝ) (b c : ℂ → ℝ) (hb : Measurable b) (h : ∀ y, b y = a + c y) :
    (∫ y, f y ∂m.withDensity (fun y => ENNReal.ofReal (Real.exp (b y)))) =
      Real.exp a * ∫ y, f y * Real.exp (c y) ∂m := by
  have hm : Measurable (fun y => ENNReal.ofReal (Real.exp (b y))) :=
    ENNReal.measurable_ofReal.comp hb.exp
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  dsimp only
  rw [ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul, h y, Real.exp_add]
  ring

/-- Tilting the real mixed mass at a root factors out the root pinning. -/
theorem bpzMixedReal_tilt (γ r : ℝ) (ρ k₁ k₂ : ℂ → ℝ) (x : ℂ) (m₁ m₂ : Measure ℂ) :
    bpzMixedReal ρ k₁ k₂ (m₁.withDensity (bpzCutRootDensity γ r x))
        (m₂.withDensity (bpzLimRootDensity γ r x)) =
      Real.exp (γ ^ 2 * bpzPin r x) * bpzRootedMixedReal γ r ρ k₁ k₂ x m₁ m₂ := by
  unfold bpzMixedReal bpzRootedMixedReal bpzCutRootDensity bpzLimRootDensity
  rw [mul_add]
  congr 1
  · exact integral_withDensity_exp_split _ _ _ _ _
      (measurable_const.mul (((continuous_bpzLam r).measurable.comp
        (measurable_const.sub measurable_id)).add_const _ |>.add
        (continuous_bpzPin r).measurable)) (fun _ => by ring)
  · exact integral_withDensity_exp_split _ _ _ _ _
      (measurable_const.mul (((continuous_bpzTruncLog r).measurable.comp
        (measurable_const.sub measurable_id)).add_const _ |>.add
        continuous_normPlus.measurable.log)) (fun _ => by ring)

/-- The scalar root derivative of the rooted mixed mass in a direction `v`. -/
noncomputable def bpzRootedMixedDerivApply (γ r : ℝ) (ρ k₁ k₂ : ℂ → ℝ) (x v : ℂ)
    (m₁ m₂ : Measure ℂ) : ℝ :=
  ∫ y, ρ y * k₁ y * (bpzCutRootKernel γ r x y * γ ^ 2) * bpzLamDeriv r (x - y) v ∂m₁ +
    ∫ y, (1 - ρ y) * k₂ y * (bpzLimRootKernel γ r x y * γ ^ 2) *
      bpzTruncLogDeriv r (x - y) v ∂m₂

/-- Tilting the untilted root-derivative functional factors out the root pinning. -/
theorem bpzMixedDerivReal_tilt (γ r : ℝ) (ρ k₁ k₂ : ℂ → ℝ) (x v : ℂ) (m₁ m₂ : Measure ℂ) :
    bpzMixedDerivReal γ r ρ k₁ k₂ x v (m₁.withDensity (bpzCutRootDensity γ r x))
        (m₂.withDensity (bpzLimRootDensity γ r x)) =
      Real.exp (γ ^ 2 * bpzPin r x) * bpzRootedMixedDerivApply γ r ρ k₁ k₂ x v m₁ m₂ := by
  convert bpzMixedReal_tilt γ r ρ (fun y => k₁ y * (γ ^ 2 * bpzLamDeriv r (x - y) v))
    (fun y => k₂ y * (γ ^ 2 * bpzTruncLogDeriv r (x - y) v)) x m₁ m₂ using 1
  · simp only [bpzMixedReal, bpzMixedDerivReal, mul_assoc]
  · unfold bpzRootedMixedDerivApply bpzRootedMixedReal
    congr 1
    congr 1 <;> congr 1 <;> funext y <;> ring

private theorem integrable_smul_deriv {m : Measure ℂ} {f : ℂ → ℝ}
    {D : ℂ → ℂ →L[ℝ] ℝ} {c K : ℝ} (hf : Integrable f m) (hf₀ : ∀ y, 0 ≤ f y)
    (hfm : Measurable f) (hDm : Measurable D) (hD : ∀ y, ‖D y‖ ≤ K) (hc : 0 ≤ c) :
    Integrable (fun y => (f y * c) • D y) m := by
  refine (hf.mul_const (c * K)).mono'
    ((hfm.mul_const c).smul hDm).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hf₀ y) hc), ← mul_assoc]
  exact mul_le_mul_of_nonneg_left (hD y) (mul_nonneg (hf₀ y) hc)

/-- The operator derivative applied to a direction is the scalar derivative. -/
theorem bpzRootedMixedDeriv_apply {γ r δ : ℝ} {ρ k₁ k₂ : ℂ → ℝ} {m₁ m₂ : Measure ℂ} {x₀ : ℂ}
    (hρm : Measurable ρ) (hk₁ : Measurable k₁) (hk₂ : Measurable k₂) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∀ y, ρ y ≤ 1) (hk₁0 : ∀ y, 0 ≤ k₁ y) (hk₂0 : ∀ y, 0 ≤ k₂ y)
    (hI₁ : Integrable (fun y => ρ y * k₁ y * Real.exp (γ ^ 2 * bpzPin r y)) m₁)
    (hI₂ : Integrable (fun y => (1 - ρ y) * k₂ y) m₂)
    (hδ : 0 < δ) (hδr : Real.exp (-r) ≤ δ) (hsep : ∀ y, ρ y < 1 → 2 * δ ≤ ‖x₀ - y‖) (v : ℂ) :
    bpzRootedMixedDeriv γ r ρ k₁ k₂ x₀ m₁ m₂ v =
      bpzRootedMixedDerivApply γ r ρ k₁ k₂ x₀ v m₁ m₂ := by
  have hc := integrable_bpz_cut_part (γ := γ) hρm hk₁ hρ0 hk₁0 hI₁ x₀
  have hl := integrable_bpz_lim_part (γ := γ) hρm hk₂ hρ1 hk₂0 hI₂ hδ hδr hsep
    (Metric.mem_ball_self hδ)
  have hcI := integrable_smul_deriv hc
    (fun y => mul_nonneg (mul_nonneg (hρ0 y) (hk₁0 y)) (bpzCutRootKernel_pos γ r x₀ y).le)
    ((hρm.mul hk₁).mul (continuous_bpzCutRootKernel_snd γ r x₀).measurable)
    ((measurable_bpzLamDeriv r).comp (measurable_const.sub measurable_id))
    (fun y => norm_bpzLamDeriv_le_exp r (x₀ - y)) (sq_nonneg γ)
  have hlI := integrable_smul_deriv hl
    (fun y => mul_nonneg (mul_nonneg (sub_nonneg.mpr (hρ1 y)) (hk₂0 y))
      (bpzLimRootKernel_pos γ r x₀ y).le)
    (((measurable_const.sub hρm).mul hk₂).mul (continuous_bpzLimRootKernel_snd γ r x₀).measurable)
    ((measurable_bpzTruncLogDeriv r).comp (measurable_const.sub measurable_id))
    (fun y => (norm_bpzTruncLogDeriv_le r (x₀ - y)).1) (sq_nonneg γ)
  unfold bpzRootedMixedDeriv bpzRootedMixedDerivApply
  simp only [← mul_assoc, Function.comp_def, Pi.sub_apply, id_eq] at hcI hlI ⊢
  rw [add_apply, ContinuousLinearMap.integral_apply hcI,
    ContinuousLinearMap.integral_apply hlI]
  rfl

/-- Parametric integrals against a measurable family of finite measures are jointly
measurable. -/
theorem measurable_integral_finite_family {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (m : α → Measure ℂ) (hm : Measurable m) (hfin : ∀ a, IsFiniteMeasure (m a))
    (g : β → ℂ → ℝ) (hg : Measurable (Function.uncurry g)) :
    Measurable (fun p : α × β => ∫ y, g p.2 y ∂m p.1) :=
  (stronglyMeasurable_integral_finite_family (fun p : α × β => m p.1)
    (hm.comp measurable_fst) (fun p => hfin p.1) _
    (hg.comp (measurable_fst.snd.prodMk measurable_snd)).stronglyMeasurable).measurable

end DOZZ.Proofs
