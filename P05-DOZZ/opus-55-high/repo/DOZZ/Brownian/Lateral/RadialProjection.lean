/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFFStructure.CircleVersion
public import DOZZ.GMC.Construction.GMCMeasurableVersion
public import DOZZ.Brownian.LateralLocalFiniteness
public import DOZZ.Brownian.LateralPolarFormula
public import DOZZ.Brownian.MeasureTranslationFinite
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# The actual two-sided radial path and its polar projection

The continuous modification of the circle averages yields a continuous path on the full real
line. Its two halves are Brownian and independent. This construction uses the same probability
space and the actual circle-average witness of the field.

The GMC has a measurable finite version. Joint integration against a finite measure then makes
its radial Wick projection almost everywhere measurable. Its bounded-interval masses are finite
without any moment assumption. These results supply the radial and measurability clauses of the
lateral decomposition; independence of the projection requires identification with the chaos of
the lateral field.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- Pack the circle averages at the origin into a full continuous radial path. -/
noncomputable def originRadialPath {Ω : Type*} (Xc : Ω → ℂ → ℝ → ℝ)
    (ω : Ω) : TwoSidedPath :=
  ContinuousMap.mkD (fun s => Xc ω 0 s) 0
section
variable {Ω : Type*} [MeasurableSpace Ω]
section
variable {P : Measure Ω}

/-- One common continuity event identifies the packed path at every real radius. -/
theorem originRadialPath_eval_ae {Xc : Ω → ℂ → ℝ → ℝ}
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2)) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, originRadialPath Xc ω s = Xc ω 0 s := by
  filter_upwards [hcont] with ω hω s
  apply ContinuousMap.mkD_apply_of_continuous
  fun_prop

/-- Dense real evaluations detect almost-everywhere measurability of full radial paths. -/
theorem aemeasurable_twoSidedPath_of_eval {A : Ω → TwoSidedPath}
    (hA : ∀ s, AEMeasurable (fun ω => A ω s) P) : AEMeasurable A P := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ
  let _ := hDc.to_subtype
  let E : TwoSidedPath → (D → ℝ) := fun p t => p t.1
  have hmE : Measurable E := by fun_prop
  have hinj : Function.Injective E := by
    intro p q hpq
    apply ContinuousMap.ext
    have he := hDd.denseRange_val.equalizer p.continuous q.continuous hpq
    simp_all
  apply (hmE.measurableEmbedding hinj).aemeasurable_comp_iff.mp
  measurability

end
section
variable (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
section
variable (hc : IsCircleAverage P X Xc) (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
include hc hcont

/-- The packed origin path is measurable up to a null set under the circle-average witness. -/
theorem originRadialPath_aemeasurable :
    AEMeasurable (originRadialPath Xc) P := by
  apply aemeasurable_twoSidedPath_of_eval
  intro s
  exact (hc.2.1 0 s).aemeasurable.congr
    ((originRadialPath_eval_ae hcont).mono (fun ω hω => (hω s).symm))

/-- The radial path starts at the equator pin on the same probability space. -/
theorem originRadialPath_zero_ae :
    ∀ᵐ ω ∂P, originRadialPath Xc ω 0 = 0 := by
  filter_upwards [originRadialPath_eval_ae hcont,
    circleAverage_equator_ae_eq_zero X Xc hc] with ω hω hzero
  simp_all

end
section
variable (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
include hX hc hcont

/-- Both halves of the packed path have the Brownian path law. -/
theorem originRadialPath_isBrownian :
    IsBrownianReal (fun t ω => originRadialPath Xc ω (t : ℝ)) P ∧
      IsBrownianReal (fun t ω => originRadialPath Xc ω (-(t : ℝ))) P := by
  have hpre := circleAverage_origin_preBrownian P X Xc hX hc
  have heq := originRadialPath_eval_ae hcont
  constructor
  · refine ⟨hpre.1.congr (fun t => heq.mono (fun ω hω => (hω t).symm)), ?_⟩
    exact ae_of_all P (fun ω => (originRadialPath Xc ω).continuous.comp NNReal.continuous_coe)
  · refine ⟨hpre.2.1.congr (fun t => heq.mono (fun ω hω => (hω (-t)).symm)), ?_⟩
    exact ae_of_all P (fun ω =>
      (originRadialPath Xc ω).continuous.comp NNReal.continuous_coe.neg)

/-- The two full half-path coordinate families are independent. -/
theorem originRadialPath_halves_indep :
    IndepFun (fun ω => fun t : ℝ≥0 => originRadialPath Xc ω (t : ℝ))
      (fun ω => fun t : ℝ≥0 => originRadialPath Xc ω (-(t : ℝ))) P := by
  apply (circleAverage_origin_preBrownian P X Xc hX hc).2.2.1.congr
  · filter_upwards [originRadialPath_eval_ae hcont] with ω hω
    simp_all
  · filter_upwards [originRadialPath_eval_ae hcont] with ω hω
    simp_all

end

end

end

/-- The radial Wick weight, including its zero value at the origin. -/
noncomputable def lateralRadialWeight (γ : ℝ) (A : TwoSidedPath) (x : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (if ‖x‖ = 0 then 0 else
    Real.exp (-γ * A (-Real.log ‖x‖) + γ * Q γ * |Real.log ‖x‖|))

/-- Joint measurability includes the radial path, charge, and spatial parameter. -/
theorem measurable_lateralRadialWeight :
    Measurable (fun p : (ℝ × TwoSidedPath) × ℂ =>
      lateralRadialWeight p.1.1 p.1.2 p.2) := by
  apply ENNReal.measurable_ofReal.comp
  apply Measurable.ite
  · measurability
  · exact measurable_const
  · have hev : Measurable (fun p : (ℝ × TwoSidedPath) × ℂ =>
        p.1.2 (-Real.log ‖p.2‖)) := by
      fun_prop
    have hQ : Measurable Q := by
      unfold Q
      fun_prop
    fun_prop

/-- Polar projection is jointly measurable on finite plane measures. -/
theorem measurable_lateralProjectedGMC_finite :
    Measurable (fun p : (ℝ × TwoSidedPath) × FiniteMeasure ℂ =>
      lateralProjectedGMC p.1.1 p.1.2 (p.2 : Measure ℂ)) := by
  apply Measure.measurable_of_measurable_coe
  intro S hS
  let ρ : ℂ → ℝ := fun x => -Real.log ‖x‖
  have hρ : Measurable ρ := by fun_prop
  have hpre := hS.preimage hρ
  have hi : Measurable (fun p : (ℝ × TwoSidedPath) × ℂ =>
      (ρ ⁻¹' S).indicator (fun x => lateralRadialWeight p.1.1 p.1.2 x) p.2) := measurable_lateralRadialWeight.indicator
      (hpre.preimage measurable_snd)
  convert (measurable_lintegral_finiteMeasure_parameter hi) using 1
  funext p
  unfold lateralProjectedGMC
  rw [Measure.map_apply hρ hS, withDensity_apply _ hpre, ← lintegral_indicator hpre]
  rfl
section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

/-- An arbitrary GMC version is almost-everywhere measurable as a measure. -/
theorem equatorGFF_GMC_aemeasurable (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) : AEMeasurable M P := by
  obtain ⟨N, hNm, _, hMN⟩ := equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM
  tauto

/-- Removing the radial Wick factor preserves measure-valued AE measurability. -/
theorem lateralProjectedGMC_aemeasurable (γ : ℝ) (A : Ω → TwoSidedPath) (hA : AEMeasurable A P)
    (M : Ω → Measure ℂ) (hMm : AEMeasurable M P)
    (hMf : ∀ ω, IsFiniteMeasure (M ω)) :
    AEMeasurable (fun ω => lateralProjectedGMC γ (A ω) (M ω)) P := by
  let N : Ω → FiniteMeasure ℂ := fun ω => ⟨M ω, hMf ω⟩
  have hN : AEMeasurable N P := @AEMeasurable.subtype_mk Ω (Measure ℂ) _ _ M P hMm
      {μ | IsFiniteMeasure μ} hMf
  have hγa : AEMeasurable (fun _ => γ) P := aemeasurable_const
  have hr := measurable_lateralProjectedGMC_finite.comp_aemeasurable ((hγa.prodMk hA).prodMk hN)
  assumption

end
section
variable (γ : ℝ) (A : TwoSidedPath)

/-- The polar projection assigns no mass to the plane origin, before taking its pushforward. -/
theorem lateralRadialWeight_zero :
    lateralRadialWeight γ A (0 : ℂ) = 0 := by
  simp [lateralRadialWeight]

/-- Reinserting the radial factor cancels the removal weight exactly. -/
theorem lateralRadialWeight_cancel (x : ℂ) :
    lateralRadialWeight γ A x *
      ENNReal.ofReal (Real.exp (γ * A (-Real.log ‖x‖) - γ * Q γ * |Real.log ‖x‖|)) =
        if x = 0 then 0 else 1 := by
  by_cases hx : x = 0
  · simp [hx, lateralRadialWeight]
  · have hnorm := norm_ne_zero_iff.mpr hx
    simp only [lateralRadialWeight, hnorm, hx, reduceIte]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    simp

end

/-- The forward radial Wick factor on the full cylinder. -/
noncomputable def lateralForwardWeight (γ : ℝ) (A : TwoSidedPath) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (γ * A s - γ * Q γ * |s|))
section
variable (γ : ℝ)
section
variable (A : TwoSidedPath)

/-- The forward factor is measurable for every continuous radial path. -/
theorem measurable_lateralForwardWeight :
    Measurable (lateralForwardWeight γ A) := by
  unfold lateralForwardWeight
  fun_prop

/-- The projected chaos recovers every nonnegative radial test of the original plane chaos,
with its possible atom at the origin removed. No lateral-law assertion is used in this identity. -/
theorem lateralProjectedGMC_reinsert_lintegral (M : Measure ℂ) (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ s, lateralForwardWeight γ A s * f s ∂lateralProjectedGMC γ A M) =
      ∫⁻ x, if x = 0 then 0 else f (-Real.log ‖x‖) ∂M := by
  have hg : Measurable (fun s => lateralForwardWeight γ A s * f s) :=
    (measurable_lateralForwardWeight γ A).mul hf
  rw [lateralProjectedGMC_lintegral_eq γ A M _ hg]
  apply lintegral_congr
  intro x
  change lateralRadialWeight γ A x *
    (lateralForwardWeight γ A _ * f _) = _
  rw [← mul_assoc]
  have hforward : lateralForwardWeight γ A (-Real.log ‖x‖) =
      ENNReal.ofReal (Real.exp (γ * A (-Real.log ‖x‖) - γ * Q γ * |Real.log ‖x‖|)) := by
    simp only [lateralForwardWeight, abs_neg]
  rw [hforward, lateralRadialWeight_cancel]
  simp

end

/-- The charge coefficient is exactly the polar Jacobian plus the radial Wick variance. -/
theorem gamma_mul_Q_eq (hγ : γ ≠ 0) : γ * Q γ = 2 + γ ^ 2 / 2 := by
  unfold Q
  field_simp

end

end DOZZ.Proofs
