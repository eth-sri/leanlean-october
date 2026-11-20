/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.GMCJointCoordinateLimit

/-! The general GMC tilt identity after passing the finite-coordinate laws to their limit. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

private theorem isFiniteMeasure_covarianceWeight (μ : Measure ℂ) [IsFiniteMeasure μ]
    (γ : ℝ) (c : ℂ →ᵇ ℝ) :
    IsFiniteMeasure (μ.withDensity fun z => ENNReal.ofReal (Real.exp (γ * c z))) := by
  apply isFiniteMeasure_withDensity
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal (Real.exp (|γ| * ‖c‖)) * μ Set.univ)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) ?_
  rw [← lintegral_const]
  refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  exact (le_abs_self _).trans (by
    rw [abs_mul]
    gcongr
    exact c.norm_coe_le_norm z)

private theorem exists_measurable_gmcTiltCoordinatePath_factor
    (H : (TestFn → ℝ) → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun p : (TestFn → ℝ) × Measure ℂ => H p.1 p.2)) :
    ∃ K : (gmcTiltCoordinateIndex → ℝ) → ℝ≥0∞, Measurable K ∧
      ∀ (q : TestFn → ℝ) (μ : Measure ℂ), IsFiniteMeasure μ →
        H q μ = K (gmcTiltCoordinatePath q μ) := by
  obtain ⟨G, hG, he⟩ := gmc_measurable_function_factors_through_finite_eval H hH
  exact Exists.intro (G ∘ fun v => (fun f => v (Sum.inl f), fun j => ENNReal.ofReal (v (Sum.inr j))))
    ⟨Measurable.comp hG
        (Measurable.prodMk (Measurable.of_eval fun a => measurable_pi_apply (Sum.inl a))
          (Measurable.of_eval fun a => Measurable.ennreal_ofReal (measurable_pi_apply (Sum.inr a)))),
      fun q μ hμ =>
      Eq.trans (congrFun he (q, ⟨μ, hμ⟩))
        (congrArg G
          (Eq.symm (Prod.ext rfl (funext fun j => ENNReal.ofReal_toReal (measure_ne_top μ (gmcTiltCoordinateSet j))))))⟩

/-- General GMC Cameron--Martin identity for every measurable nonnegative functional of the
test field and the limiting chaos measure. -/
theorem equatorGFF_GMC_tilt
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (L : Ω → ℝ) (hL : IsGaussianL2Limit P X L) (c : BoundedContinuousFunction ℂ ℝ)
    (hc : TendstoUniformly
      (fun (r : ℝ) (x : ℂ) => gaussianCovariance P (fun ω => Xc ω x r) L) c atTop)
    (H : (TestFn → ℝ) → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun q : (TestFn → ℝ) × Measure ℂ => H q.1 q.2)) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (L ω - gaussianVariance P L / 2)) *
        H (fun f => X ω f) (M ω) ∂P) =
      ∫⁻ ω, H (fun f => X ω f + gaussianCovariance P (fun ω => X ω f) L)
        ((M ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * c x)))) ∂P := by
  classical
  let density  := fun ω => ENNReal.ofReal
    (Real.exp (L ω - gaussianVariance P L / 2))
  let Q  := P.withDensity density
  let eval  := fun ω f => X ω f
  let shift  := fun f => gaussianCovariance P (fun ω => X ω f) L
  let leftPath  := fun ω =>
    gmcTiltCoordinatePath (eval ω) (M ω)
  let rightPath  := fun ω =>
    gmcTiltCoordinatePath (fun f => eval ω f + shift f)
      ((M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z))))
  obtain ⟨K, hK, hFactor⟩ := exists_measurable_gmcTiltCoordinatePath_factor H hH
  have hleftAEMeasP : AEMeasurable leftPath P := aemeasurable_gmcTiltCoordinatePath P X hX γ M hM
  have hleftAEMeasQ := hleftAEMeasP.mono_ac (withDensity_absolutelyContinuous P density)
  have hrightAEMeasP : AEMeasurable rightPath P :=
    aemeasurable_gmcTiltCoordinatePath_withDensity P X hX γ M hM shift _ (by fun_prop)
  have hdenAEMeas : AEMeasurable density P := ENNReal.measurable_ofReal.comp_aemeasurable
    (Real.measurable_exp.comp_aemeasurable (hL.1.aestronglyMeasurable.aemeasurable.sub_const _))
  have hjoint : Measure.map leftPath Q = Measure.map rightPath P :=
    equatorGFF_GMC_fullCoordinate_limit_law P X hX γ M hM Xc hXc L hL c hc
  have hLeftFactor (ω : Ω) : H (eval ω) (M ω) = K (leftPath ω) := hFactor _ _ (hM.1 ω)
  have hRightFactor (ω : Ω) : H (fun f => eval ω f + shift f)
      ((M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z)))) = K (rightPath ω) := by
    haveI := hM.1 ω
    exact hFactor _ _ (isFiniteMeasure_covarianceWeight _ γ c)
  calc
    (∫⁻ ω, density ω * H (eval ω) (M ω) ∂P) =
        ∫⁻ ω, density ω * K (leftPath ω) ∂P := by
          apply lintegral_congr_ae
          filter_upwards [] with ω
          rw [hLeftFactor ω]
    _ = ∫⁻ ω, K (leftPath ω) ∂Q := by
      symm
      exact lintegral_withDensity_eq_lintegral_mul₀ hdenAEMeas (hK.comp_aemeasurable hleftAEMeasP)
    _ = ∫⁻ y, K y ∂Measure.map leftPath Q :=
      (lintegral_map' hK.aemeasurable hleftAEMeasQ).symm
    _ = ∫⁻ y, K y ∂Measure.map rightPath P := by rw [hjoint]
    _ = ∫⁻ ω, K (rightPath ω) ∂P :=
      lintegral_map' hK.aemeasurable hrightAEMeasP
    _ = ∫⁻ ω, H (fun f => eval ω f + shift f)
        ((M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z)))) ∂P := by
          apply lintegral_congr_ae
          filter_upwards [] with ω
          rw [hRightFactor ω]

end DOZZ.Proofs
