/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.GMCJointCoordinateLimit

/-! The general GMC tilt identity after passing the finite-coordinate laws to their limit. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

variable {Ω : Type*} [_inst1 : MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)

private theorem weightedMeasure_isFinite
    (μ : Measure ℂ) [IsFiniteMeasure μ]
    (w : BoundedContinuousFunction ℂ ℝ) :
    IsFiniteMeasure (μ.withDensity (fun z => ENNReal.ofReal (w z))) := by
  apply MeasureTheory.isFiniteMeasure_withDensity
  have hpoint : ∀ z, ENNReal.ofReal (w z) ≤ ENNReal.ofReal ‖w‖ := by
    intro z
    apply ENNReal.ofReal_le_ofReal
    exact le_trans (le_abs_self _) (w.norm_coe_le_norm z)
  have hbound : (∫⁻ z, ENNReal.ofReal (w z) ∂μ) ≤ ENNReal.ofReal ‖w‖ * μ Set.univ := by
    calc
      (∫⁻ z, ENNReal.ofReal (w z) ∂μ) ≤ ∫⁻ z, ENNReal.ofReal ‖w‖ ∂μ :=
        lintegral_mono hpoint
      _ = ENNReal.ofReal ‖w‖ * μ Set.univ := lintegral_const _
  have hprod : ENNReal.ofReal ‖w‖ * μ Set.univ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_of_lt (measure_lt_top μ Set.univ))
  continuity

private theorem gmcTilt_density_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr)
    (L : Ω → ℝ) (hL : IsGaussianL2Limit P X L) :
    let density : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal
      (Real.exp (L ω - gaussianVariance P L / 2))
    AEMeasurable density P ∧ ∀ᵐ ω ∂P, density ω ≠ 0 := by
  dsimp
  constructor
  · have hLmeas  := hL.1.aestronglyMeasurable.aemeasurable
    fun_prop
  · filter_upwards [] with ω
    positivity

include Ω _inst1 P X hX γ in
/-- General GMC Cameron--Martin identity for every measurable nonnegative functional of the
test field and the limiting chaos measure. -/
theorem equatorGFF_GMC_tilt
     (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
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
  have _ := hγ

  classical
  let density  := fun ω => ENNReal.ofReal
    (Real.exp (L ω - gaussianVariance P L / 2))
  let Q  := P.withDensity density
  let eval : Ω → TestFn → ℝ := fun ω f => X ω f
  let shift : TestFn → ℝ := fun f => gaussianCovariance P (fun ω => X ω f) L
  let leftPath  := fun ω =>
    gmcTiltCoordinatePath (eval ω) (M ω)
  let rightPath  := fun ω =>
    gmcTiltCoordinatePath (fun f => eval ω f + shift f)
      ((M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z))))
  let decode : (gmcTiltCoordinateIndex → ℝ) →
      (TestFn → ℝ) × (Option (ℚ × ℚ) → ℝ≥0∞) := fun v =>
    (fun f => v (.inl f), fun j => ENNReal.ofReal (v (.inr j)))
  obtain ⟨G, hG, hGfactor⟩ := gmc_measurable_function_factors_through_finite_eval H hH
  have hdecode : Measurable decode := by
    fun_prop
  let K  := fun v => G (decode v)
  have hK  := hG.comp hdecode
  obtain ⟨u, w, -, hw, hconv, heventual, -⟩ :=
    equatorGFF_expCovariance_finiteCoordinate_tendstoInMeasure
      P X hX Xc hXc γ M hM L hL c hc (∅ : Finset gmcTiltCoordinateIndex)
  have hwEq : ∀ z : ℂ, w z = Real.exp (γ * c z) := by
    intro z
    exact equatorGFF_expCovariance_weight_limit_value
      P Xc L γ c hc u w hconv heventual z
  obtain ⟨leftProxy, hleftProxyMeas, hleftProxyAE⟩ :=
    equatorGFF_GMC_unweighted_path_proxy P X hX γ M hM
  have hleftAE_P : leftPath =ᵐ[P] leftProxy := hleftProxyAE
  have hleftAEMeasP  :=
    hleftProxyMeas.aemeasurable.congr hleftAE_P.symm
  have hdenData := gmcTilt_density_aemeasurable P X L hL
  have hdenAEMeas : AEMeasurable density P := hdenData.1
  have hdenNe : ∀ᵐ ω ∂P, density ω ≠ 0 := hdenData.2
  have hleftAE_Q  := (withDensity_ae_eq hdenAEMeas hdenNe).2 hleftAE_P
  have hleftAEMeasQ  :=
    hleftProxyMeas.aemeasurable.congr hleftAE_Q.symm
  obtain ⟨rightProxy, hrightProxyMeas, hrightProxyAE⟩ :=
    equatorGFF_GMC_weighted_path_proxy P X hX γ M hM shift w
  have hweightEq (ω : Ω) :
      (M ω).withDensity (fun z => ENNReal.ofReal (w z)) =
      (M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z))) := by
    congr 1
    funext z
    rw [hwEq z]
  have hrightAE_P : rightPath =ᵐ[P] rightProxy := by
    aesop
  have hrightAEMeasP  :=
    hrightProxyMeas.aemeasurable.congr hrightAE_P.symm
  have hjoint := equatorGFF_GMC_fullCoordinate_limit_law
    P X hX γ M hM Xc hXc L hL c hc
  have hFiniteLeft (ω : Ω) : IsFiniteMeasure (M ω) := hM.1 ω
  have hDecodeLeft (ω : Ω) : decode (leftPath ω) =
      (eval ω, gmcFiniteMeasureEval ⟨M ω, hFiniteLeft ω⟩) := by
    apply Prod.ext
    · funext f
      rfl
    · funext j
      simp only [decode, leftPath, gmcTiltCoordinatePath,
        gmcFiniteMeasureEval, gmcTiltCoordinateSet]
      rw [ENNReal.ofReal_toReal
        (@MeasureTheory.measure_ne_top ℂ _ (M ω) (hFiniteLeft ω) _)]
      rfl
  have hLeftFactor (ω : Ω) : H (eval ω) (M ω) = K (leftPath ω) := by
    have hfactor := congrFun hGfactor (eval ω, ⟨M ω, hFiniteLeft ω⟩)
    have hfactor' : H (eval ω) (M ω) =
        G (eval ω, gmcFiniteMeasureEval ⟨M ω, hFiniteLeft ω⟩) := hfactor
    grind
  have hFiniteRight (ω : Ω) : IsFiniteMeasure
      ((M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z)))) := by
    rw [← hweightEq ω]
    exact weightedMeasure_isFinite (M ω) w
  have hDecodeRight (ω : Ω) : decode (rightPath ω) =
      ((fun f => eval ω f + shift f),
        gmcFiniteMeasureEval ⟨(M ω).withDensity
          (fun z => ENNReal.ofReal (Real.exp (γ * c z))), hFiniteRight ω⟩) := by
    apply Prod.ext
    · funext f
      rfl
    · funext j
      simp only [decode, rightPath, gmcTiltCoordinatePath,
        gmcFiniteMeasureEval, gmcTiltCoordinateSet]
      rw [ENNReal.ofReal_toReal
        (@MeasureTheory.measure_ne_top ℂ _
          ((M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z))))
          (hFiniteRight ω) _)]
      rfl
  have hRightFactor (ω : Ω) :
      H (fun f => eval ω f + shift f)
        ((M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z)))) =
      K (rightPath ω) := by
    let μω := (M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z)))
    have hfactor := congrFun hGfactor
      ((fun f => eval ω f + shift f), ⟨μω, hFiniteRight ω⟩)
    have hfactor' : H (fun f => eval ω f + shift f) μω =
        G ((fun f => eval ω f + shift f), gmcFiniteMeasureEval ⟨μω, hFiniteRight ω⟩) := by
      bound
    grind
  have hObsLeftAEMeas  :=
    hK.aemeasurable.comp_aemeasurable hleftAEMeasP


  calc
    (∫⁻ ω, density ω * H (eval ω) (M ω) ∂P) =
        ∫⁻ ω, density ω * K (leftPath ω) ∂P := by
          simp_all
    _ = ∫⁻ ω, K (leftPath ω) ∂Q := by
      symm
      exact lintegral_withDensity_eq_lintegral_mul₀ hdenAEMeas hObsLeftAEMeas
    _ = ∫⁻ y, K y ∂Measure.map leftPath Q :=
      (lintegral_map' hK.aemeasurable hleftAEMeasQ).symm
    _ = ∫⁻ y, K y ∂Measure.map rightPath P := by rw [hjoint]
    _ = ∫⁻ ω, K (rightPath ω) ∂P :=
      lintegral_map' hK.aemeasurable hrightAEMeasP
    _ = ∫⁻ ω, H (fun f => eval ω f + shift f)
        ((M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z)))) ∂P := by
          simp_all

end DOZZ.Proofs
