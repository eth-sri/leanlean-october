/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.GMCFiniteCoordinateTilt
public import DOZZ.GMC.Construction.GMCWeightedBoxMass
public import DOZZ.GMC.Construction.GMCWeightedBoxMassVarying
public import DOZZ.GMC.Construction.GMCVaryingWeightedTotalMassLimit
public import DOZZ.GMC.Construction.GMCExpCovarianceWeight
public import DOZZ.GMC.Construction.GMCGeneralTiltBasisProxy
public import DOZZ.GMC.Construction.RootedSizeBiasedLimit
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Topology.EMetricSpace.Pi
public import DOZZ.GMC.ConvergenceInMeasure

/-! Finite-coordinate convergence for the two sides of the general GMC tilt. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal BoundedContinuousFunction

namespace DOZZ.Proofs

private def gmcCoordinateB (i : Option (ℚ × ℚ)) : Set ℂ :=
  match i with
  | none => Set.univ
  | some j => gmcLowerBox j

private theorem exists_measurable_unweighted_finitePath_proxy
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (s : Finset gmcTiltCoordinateIndex) :
    ∃ G : Ω → (∀ _i : {i // i ∈ s}, ℝ),
      Measurable G ∧
      (fun ω => gmcTiltFiniteCoordinatePath s (fun f => X ω f) (M ω)) =ᵐ[P] G := by
  obtain ⟨E, hE, hEae⟩ := equatorGFF_GMC_finiteEval_field_proxy P X hX γ M hM
  let eval  := fun ω f => X ω f
  have heval : Measurable eval := by
    rw [measurable_pi_iff]
    exact fun f => (hX.2 f).1
  let G : Ω → (∀ _i : {i // i ∈ s}, ℝ) := fun ω i =>
    match i.1 with
    | .inl f => eval ω f
    | .inr j => (E (eval ω) j).toReal
  have hG : Measurable G := by
    rw [measurable_pi_iff]
    intro i
    cases hi : i.1 with
    | inl f =>
      simpa [G, hi, eval, Function.comp_def] using (hX.2 f).1
    | inr j =>
      simpa [G, hi, eval, Function.comp_def] using ENNReal.measurable_toReal.comp
        ((measurable_pi_apply j).comp (hE.comp heval))
  have hEq : (fun ω => gmcTiltFiniteCoordinatePath s (eval ω) (M ω)) =ᵐ[P] G := by
    filter_upwards [hEae] with ω hω
    funext i
    cases hi : i.1 with
    | inl f =>
      simp [gmcTiltFiniteCoordinatePath, gmcTiltCoordinatePath, G, eval, hi]
    | inr j =>
      have hcoord := congrFun hω j
      simp only [gmcTiltFiniteCoordinatePath, gmcTiltCoordinatePath, G, hi, eval]
      convert congrArg ENNReal.toReal hcoord using 1
      rfl
  exact ⟨G, hG, hEq⟩

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
include Ω X hX hXc

private theorem measurable_regularizedGMC_withDensity
    (γ r : ℝ) (W : ℂ → ℝ≥0∞) (hW : Measurable W) :
    Measurable (fun ω => (regularizedGMC P Xc γ r ω).withDensity W) := by
  have hμ  :=
    regularizedGMC_measurable P X hX Xc hXc γ r
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have hEq : (fun ω => (regularizedGMC P Xc γ r ω).withDensity W A) =
      fun ω => ∫⁻ z, A.indicator W z ∂regularizedGMC P Xc γ r ω := by
    funext ω
    rw [withDensity_apply _ hA, ← lintegral_indicator hA]
  rw [hEq]
  exact (Measure.measurable_lintegral (hW.indicator hA)).comp hμ

/-- The unweighted joint field/chaos finite coordinates converge in measure to any `IsGMCOf`
limit. -/
theorem regularizedGMC_finiteCoordinatePath_tendstoInMeasure (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (s : Finset gmcTiltCoordinateIndex) :
    TendstoInMeasure P
      (fun r ω => gmcTiltFiniteCoordinatePath s (fun f => X ω f)
        (regularizedGMC P Xc γ r ω)) atTop
      (fun ω => gmcTiltFiniteCoordinatePath s (fun f => X ω f) (M ω)) := by
  refine tendstoInMeasure_pi_finite P _ _ ?_
  intro i
  change TendstoInMeasure P
    (fun r ω => gmcTiltCoordinatePath (fun f => X ω f)
      (regularizedGMC P Xc γ r ω) i.1) atTop
    (fun ω => gmcTiltCoordinatePath (fun f => X ω f) (M ω) i.1)
  rcases i.1 with f | j
  · intro ε hε
    simp [gmcTiltCoordinatePath, hε.ne']
  · cases j with
    | none =>
      have h := regularizedGMC_withDensity_univ_mass_tendstoInMeasure
        P X hX Xc hXc γ M hM (1 : BoundedContinuousFunction ℂ ℝ)
        (by intro z; norm_num)
      simpa [gmcTiltFiniteCoordinatePath, gmcTiltCoordinatePath,
        gmcTiltCoordinateSet, gmcCoordinateB] using h
    | some j =>
      apply regularizedGMC_box_mass_tendstoInMeasure <;> assumption

/-- Under a uniformly convergent family of nonnegative covariance weights, the shifted field and
weighted cutoff chaos converge in measure on every finite coordinate set. -/
theorem regularizedGMC_varyingWeighted_finiteCoordinatePath_tendstoInMeasure (γ : ℝ)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (shift : TestFn → ℝ)
    (u : ℝ → BoundedContinuousFunction ℂ ℝ) (hu : ∀ r z, 0 ≤ u r z)
    (v : BoundedContinuousFunction ℂ ℝ) (hv : ∀ z, 0 ≤ v z)
    (hconv : TendstoUniformly (fun r z => u r z) v atTop)
    (s : Finset gmcTiltCoordinateIndex) :
    TendstoInMeasure P
      (fun r ω => gmcTiltFiniteCoordinatePath s (fun f => X ω f + shift f)
        ((regularizedGMC P Xc γ r ω).withDensity
          (fun z => ENNReal.ofReal (u r z)))) atTop
      (fun ω => gmcTiltFiniteCoordinatePath s (fun f => X ω f + shift f)
        ((M ω).withDensity (fun z => ENNReal.ofReal (v z)))) := by
  refine tendstoInMeasure_pi_finite P _ _ ?_
  intro i
  change TendstoInMeasure P
    (fun r ω => gmcTiltCoordinatePath (fun f => X ω f + shift f)
      ((regularizedGMC P Xc γ r ω).withDensity
        (fun z => ENNReal.ofReal (u r z))) i.1) atTop
    (fun ω => gmcTiltCoordinatePath (fun f => X ω f + shift f)
      ((M ω).withDensity (fun z => ENNReal.ofReal (v z))) i.1)
  rcases i.1 with f | j
  · intro ε hε
    simp [gmcTiltCoordinatePath, hε.ne']
  · cases j with
    | none =>
      apply regularizedGMC_varyingWithDensity_univ_mass_tendstoInMeasure <;> assumption
    | some j =>
      let leftVarying  := fun r ω =>
        (((regularizedGMC P Xc γ r ω).withDensity
          (fun z => ENNReal.ofReal (u r z))) (gmcLowerBox j)).toReal
      let rightVarying  := fun r ω =>
        (((regularizedGMC P Xc γ r ω).withDensity
          (fun z => ENNReal.ofReal (v z))) (gmcLowerBox j)).toReal
      let limitMass  := fun ω =>
        (((M ω).withDensity (fun z => ENNReal.ofReal (v z)))
          (gmcLowerBox j)).toReal
      have hdiff : TendstoInMeasure P
          (fun r ω => leftVarying r ω - rightVarying r ω) atTop (fun _ => 0) := by
        simpa [leftVarying, rightVarying] using
          (regularizedGMC_varyingWithDensity_set_mass_diff_tendstoInMeasure
            P X hX Xc hXc γ u hu v hv hconv (gmcLowerBox_measurableSet j))
      have hfix : TendstoInMeasure P rightVarying atTop limitMass := by
        simpa [rightVarying, limitMass] using
          regularizedGMC_withDensity_box_mass_tendstoInMeasure
            P X hX Xc hXc γ M hM v hv j
      simpa [gmcTiltCoordinatePath, gmcTiltCoordinateSet, gmcCoordinateB,
        leftVarying, limitMass] using
        tendstoInMeasure_add_of_sub P leftVarying rightVarying limitMass hdiff hfix

end

/-- A fixed Cameron--Martin density has total mass one. -/
theorem equatorGFF_gaussianL2_tilt_density_integral_eq_one
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (L : Ω → ℝ) (hL : IsGaussianL2Limit P X L) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (L ω - gaussianVariance P L / 2)) ∂P = 1 := by
  have htilt := equatorGFF_finite_test_circle_tilt
    (P := P) (X := X) (hX := hX) (Xc := Xc) (hXc := hXc) (r := 0)
    (L := L) (hL := hL) (coord := fun i : Empty => i.elim)
    (t := 1) (F := fun _ => (1 : ℝ≥0∞)) (hF := measurable_const)
  calc
    _ = P Set.univ := by simpa [div_eq_mul_inv, mul_comm] using htilt
    _ = 1 := measure_univ

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
  (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ) (M : Ω → Measure ℂ)
  (hM : IsGMCOf P X γ M) (L : Ω → ℝ) (hL : IsGaussianL2Limit P X L)
include Ω hX hXc hM hL

/-- The unweighted finite coordinate vector converges in measure under a fixed Gaussian tilt. -/
theorem equatorGFF_unweightedFiniteCoordinate_tendstoInMeasure_under_tilt
    (s : Finset gmcTiltCoordinateIndex) :
    TendstoInMeasure
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (L ω - gaussianVariance P L / 2))))
      (fun r ω => gmcTiltFiniteCoordinatePath s (fun f => X ω f)
        (regularizedGMC P Xc γ r ω)) atTop
      (fun ω => gmcTiltFiniteCoordinatePath s (fun f => X ω f) (M ω)) := by
  let density  := fun ω => ENNReal.ofReal
    (Real.exp (L ω - gaussianVariance P L / 2))
  let Q  := P.withDensity density
  let field  := fun ω f => X ω f
  have hmass : ∫⁻ ω, density ω ∂P = 1 := by
    simpa [density] using
      @equatorGFF_gaussianL2_tilt_density_integral_eq_one Ω _ P hX.1 X hX Xc hXc L hL
  have hdenAEMeas : AEMeasurable density P := by
    have hLmeas  := hL.1.aestronglyMeasurable.aemeasurable
    apply ENNReal.measurable_ofReal.comp_aemeasurable <;> fun_prop
  have hdenNe : ∀ᵐ ω ∂P, density ω ≠ 0 := by
    filter_upwards [] with ω
    positivity
  obtain ⟨proxy, hproxyMeas, hproxyAE⟩ :=
    exists_measurable_unweighted_finitePath_proxy P X hX γ M hM s
  have hfieldMeas : Measurable field := by
    rw [measurable_pi_iff]
    exact fun f => (hX.2 f).1
  have hcutoffMeas : ∀ r, Measurable (fun ω =>
      gmcTiltFiniteCoordinatePath s (field ω) (regularizedGMC P Xc γ r ω)) := by
    intro r
    exact (measurable_gmcTiltFiniteCoordinatePath s).comp
      (Measurable.prodMk hfieldMeas
        (regularizedGMC_measurable P X hX Xc hXc γ r))
  have hbase := (regularizedGMC_finiteCoordinatePath_tendstoInMeasure
      P X hX Xc hXc γ M hM s).congr_right (by simpa [field] using hproxyAE)
  have htiltedProxy := tendstoInMeasure_withDensity_of_lintegral_lt_top density
      (by rw [hmass]; norm_num) hcutoffMeas hproxyMeas hbase
  have hproxyQ := (withDensity_ae_eq hdenAEMeas hdenNe).2 (by simpa [field, Q, density] using hproxyAE)
  exact htiltedProxy.congr_right hproxyQ.symm

/-- The radius-dependent exact covariance weights have the same finite-coordinate limit as
their uniformly convergent bounded-continuous representatives. -/
theorem equatorGFF_expCovariance_finiteCoordinate_tendstoInMeasure
    (c : BoundedContinuousFunction ℂ ℝ)
    (hc : TendstoUniformly
      (fun r z => gaussianCovariance P (fun ω => Xc ω z r) L) c atTop)
    (s : Finset gmcTiltCoordinateIndex) :
    ∃ u : ℝ → BoundedContinuousFunction ℂ ℝ,
    ∃ w : BoundedContinuousFunction ℂ ℝ,
      (∀ r z, 0 ≤ u r z) ∧ (∀ z, 0 ≤ w z) ∧
      TendstoUniformly (fun r z => u r z) w atTop ∧
      (∀ᶠ r : ℝ in atTop, ∀ z : ℂ,
        u r z = Real.exp (γ * gaussianCovariance P (fun ω => Xc ω z r) L)) ∧
      TendstoInMeasure P
        (fun r ω => gmcTiltFiniteCoordinatePath s
          (fun f => X ω f + gaussianCovariance P (fun ω' => X ω' f) L)
          ((regularizedGMC P Xc γ r ω).withDensity
            (fun z => ENNReal.ofReal (Real.exp
              (γ * gaussianCovariance P (fun ω' => Xc ω' z r) L))))) atTop
        (fun ω => gmcTiltFiniteCoordinatePath s
          (fun f => X ω f + gaussianCovariance P (fun ω' => X ω' f) L)
          ((M ω).withDensity (fun z => ENNReal.ofReal (w z)))) := by
  obtain ⟨u, w, hu, hw, hconv, heventual⟩ :=
    equatorGFF_circleCovariance_exp_weight_family P X hX Xc hXc L hL γ c hc
  let cutoffBCF  := fun r ω =>
    gmcTiltFiniteCoordinatePath s
      (fun f => X ω f + gaussianCovariance P (fun ω' => X ω' f) L)
      ((regularizedGMC P Xc γ r ω).withDensity
        (fun z => ENNReal.ofReal (u r z)))
  let cutoffExact  := fun r ω =>
    gmcTiltFiniteCoordinatePath s
      (fun f => X ω f + gaussianCovariance P (fun ω' => X ω' f) L)
      ((regularizedGMC P Xc γ r ω).withDensity
        (fun z => ENNReal.ofReal (Real.exp
          (γ * gaussianCovariance P (fun ω' => Xc ω' z r) L))))
  let limit  := fun ω =>
    gmcTiltFiniteCoordinatePath s
      (fun f => X ω f + gaussianCovariance P (fun ω' => X ω' f) L)
      ((M ω).withDensity (fun z => ENNReal.ofReal (w z)))
  have hBCF : TendstoInMeasure P cutoffBCF atTop limit := by
    apply regularizedGMC_varyingWeighted_finiteCoordinatePath_tendstoInMeasure <;> assumption
  have hcutoffEq : ∀ᶠ r : ℝ in atTop, cutoffBCF r =ᵐ[P] cutoffExact r := by
    filter_upwards [heventual] with r hr
    have hweight : (fun z : ℂ => ENNReal.ofReal (u r z)) =
        fun z => ENNReal.ofReal (Real.exp
          (γ * gaussianCovariance P (fun ω' => Xc ω' z r) L)) := by
      funext z
      rw [hr z]
    have hmeasure (ω : Ω) :
        (regularizedGMC P Xc γ r ω).withDensity (fun z => ENNReal.ofReal (u r z)) =
        (regularizedGMC P Xc γ r ω).withDensity (fun z => ENNReal.ofReal (Real.exp
          (γ * gaussianCovariance P (fun ω' => Xc ω' z r) L))) := by
      rw [hweight]
    filter_upwards [] with ω
    simp [cutoffBCF, cutoffExact, hmeasure ω]
  refine ⟨u, w, hu, hw, hconv, heventual, ?_⟩
  exact hBCF.congr' hcutoffEq EventuallyEq.rfl

end

section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

/-- The uniform limit of the bounded-continuous covariance exponential weights is the stated
exponential of the limiting covariance profile. -/
theorem equatorGFF_expCovariance_weight_limit_value (Xc : Ω → ℂ → ℝ → ℝ) (L : Ω → ℝ) (γ : ℝ)
    (c : BoundedContinuousFunction ℂ ℝ)
    (hc : TendstoUniformly
      (fun r z => gaussianCovariance P (fun ω => Xc ω z r) L) c atTop)
    (u : ℝ → BoundedContinuousFunction ℂ ℝ)
    (w : BoundedContinuousFunction ℂ ℝ)
    (hconv : TendstoUniformly (fun r z => u r z) w atTop)
    (heventual : ∀ᶠ r : ℝ in atTop, ∀ z : ℂ,
      u r z = Real.exp (γ * gaussianCovariance P (fun ω => Xc ω z r) L))
    (z : ℂ) : w z = Real.exp (γ * c z) := by
  have hcovPoint := hc.tendsto_at z
  have harg : Tendsto (fun r : ℝ => γ *
      gaussianCovariance P (fun ω => Xc ω z r) L) atTop (𝓝 (γ * c z)) :=
    tendsto_const_nhds.mul hcovPoint
  have hexp := (Real.continuous_exp.tendsto (γ * c z)).comp harg
  have huPoint := hconv.tendsto_at z
  have hEqEvent : (fun r : ℝ => u r z) =ᶠ[atTop]
      fun r => Real.exp (γ * gaussianCovariance P (fun ω => Xc ω z r) L) := by
    filter_upwards [heventual] with r hr
    exact hr z
  exact tendsto_nhds_unique huPoint (hexp.congr' hEqEvent.symm)

/-- Equality of the finite-dimensional weak limits passes the exact finite-radius
Cameron--Martin identity to the limiting chaos coordinates. -/
theorem equatorGFF_finiteGmcCoordinate_limit_law (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (L : Ω → ℝ) (hL : IsGaussianL2Limit P X L)
    (c : BoundedContinuousFunction ℂ ℝ)
    (hc : TendstoUniformly
      (fun r z => gaussianCovariance P (fun ω => Xc ω z r) L) c atTop)
    (s : Finset gmcTiltCoordinateIndex) :
    Measure.map
      (fun ω => gmcTiltFiniteCoordinatePath s (fun f => X ω f) (M ω))
      (P.withDensity (fun ω => ENNReal.ofReal
        (Real.exp (L ω - gaussianVariance P L / 2)))) =
    Measure.map
      (fun ω => gmcTiltFiniteCoordinatePath s
        (fun f => X ω f + gaussianCovariance P (fun ω' => X ω' f) L)
        ((M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z))))) P := by
  classical
  let density  := fun ω => ENNReal.ofReal
    (Real.exp (L ω - gaussianVariance P L / 2))
  let Q  := P.withDensity density
  let field  := fun ω f => X ω f
  let shift  := fun f => gaussianCovariance P (fun ω => X ω f) L
  let leftCutoff  := fun r ω =>
    gmcTiltFiniteCoordinatePath s (field ω) (regularizedGMC P Xc γ r ω)
  let leftLimit  := fun ω =>
    gmcTiltFiniteCoordinatePath s (field ω) (M ω)
  obtain ⟨u, w, hu, hw, hconv, heventual, hrightMeasure⟩ :=
    equatorGFF_expCovariance_finiteCoordinate_tendstoInMeasure
      P X hX Xc hXc γ M hM L hL c hc s
  let rightCutoff  := fun r ω =>
    gmcTiltFiniteCoordinatePath s (fun f => field ω f + shift f)
      ((regularizedGMC P Xc γ r ω).withDensity
        (fun z => ENNReal.ofReal (Real.exp
          (γ * gaussianCovariance P (fun ω' => Xc ω' z r) L))))
  let rightLimit  := fun ω =>
    gmcTiltFiniteCoordinatePath s (fun f => field ω f + shift f)
      ((M ω).withDensity (fun z => ENNReal.ofReal (w z)))
  have hwEq : ∀ z : ℂ, w z = Real.exp (γ * c z) := by
    intro z
    exact equatorGFF_expCovariance_weight_limit_value
      P Xc L γ c hc u w hconv heventual z
  have hleftMeasure : TendstoInMeasure Q leftCutoff atTop leftLimit := by
    apply equatorGFF_unweightedFiniteCoordinate_tendstoInMeasure_under_tilt <;> assumption
  have hrightMeasure' : TendstoInMeasure P rightCutoff atTop rightLimit := by
    assumption
  have hfield : Measurable field := by
    rw [measurable_pi_iff]
    exact fun f => (hX.2 f).1
  have hleftMeas : ∀ r, Measurable (leftCutoff r) := by
    intro r
    exact (measurable_gmcTiltFiniteCoordinatePath s).comp
      (Measurable.prodMk hfield (regularizedGMC_measurable P X hX Xc hXc γ r))
  have hshiftMeas : Measurable (fun ω f => field ω f + shift f) := by
    fun_prop
  have hrightMeas : ∀ r, Measurable (rightCutoff r) := by
    intro r
    have hcov := continuous_gaussianCovariance_circle_of_IsGaussianL2Limit P X hX Xc hXc L hL r
    have hW : Measurable (fun z : ℂ => ENNReal.ofReal (Real.exp
        (γ * gaussianCovariance P (fun ω' => Xc ω' z r) L))) :=
      ENNReal.measurable_ofReal.comp
        (Real.measurable_exp.comp (measurable_const.mul hcov.measurable))
    exact (measurable_gmcTiltFiniteCoordinatePath s).comp
      (Measurable.prodMk hshiftMeas
        (measurable_regularizedGMC_withDensity P X hX Xc hXc γ r _ hW))
  have hmass : ∫⁻ ω, density ω ∂P = 1 := by
    simpa [density] using
      @equatorGFF_gaussianL2_tilt_density_integral_eq_one Ω _ P hX.1 X hX Xc hXc L hL
  have hQprob : IsProbabilityMeasure Q := by
    refine ⟨?_⟩
    have hQmass : Q Set.univ = ∫⁻ ω, density ω ∂P := by
      dsimp [Q]
      simp
    rwa [hQmass]
  have hleftDistAux [IsProbabilityMeasure Q] := hleftMeasure.tendstoInDistribution (fun r => (hleftMeas r).aemeasurable)
  have hleftDist := @hleftDistAux hQprob
  have hrightDistAux [IsProbabilityMeasure P] := hrightMeasure'.tendstoInDistribution (fun r => (hrightMeas r).aemeasurable)
  have hrightDist := @hrightDistAux hX.1
  have hcutlaw (r : ℝ) : Measure.map (leftCutoff r) Q = Measure.map (rightCutoff r) P := by
    apply equatorGFF_tilted_finiteGmcCoordinate_law_at_cutoff <;> assumption
  have hseqAux [IsProbabilityMeasure Q] [IsProbabilityMeasure P] :
      (fun r : ℝ => (⟨Q.map (leftCutoff r), inferInstance⟩ :
        ProbabilityMeasure (∀ _i : {i // i ∈ s}, ℝ))) = fun r =>
      (⟨P.map (rightCutoff r), inferInstance⟩ :
        ProbabilityMeasure (∀ _i : {i // i ∈ s}, ℝ)) := by
    funext r
    apply Subtype.ext
    exact hcutlaw r
  have hseq := @hseqAux hQprob hX.1
  have hleftTendsto := @TendstoInDistribution.tendsto
    (ι := ℝ) (E := ∀ _i : {i // i ∈ s}, ℝ) (Ω' := Ω)
    (Ω := fun _ : ℝ => Ω) (m := fun _ => inferInstance)
    (m' := inferInstance) (mE := inferInstance) inferInstance inferInstance
    (X := leftCutoff) (l := atTop) (Z := leftLimit)
    (μ := fun _ : ℝ => Q) (fun _ => hQprob)
    (μ' := Q) hQprob hleftDist
  have hrightTendsto := @TendstoInDistribution.tendsto
    (ι := ℝ) (E := ∀ _i : {i // i ∈ s}, ℝ) (Ω' := Ω)
    (Ω := fun _ : ℝ => Ω) (m := fun _ => inferInstance)
    (m' := inferInstance) (mE := inferInstance) inferInstance inferInstance
    (X := rightCutoff) (l := atTop) (Z := rightLimit)
    (μ := fun _ : ℝ => P) (fun _ => hX.1)
    (μ' := P) hX.1 hrightDist
  rw [← hseq] at hrightTendsto
  have hlimit := tendsto_nhds_unique hleftTendsto hrightTendsto
  have hmapLimit := congrArg Subtype.val hlimit
  have hleftPath : (fun ω => gmcTiltFiniteCoordinatePath s
      (fun f => X ω f) (M ω)) = leftLimit := by
    funext ω
    rfl
  have hweight : (fun z : ℂ => ENNReal.ofReal (Real.exp (γ * c z))) =
      fun z => ENNReal.ofReal (w z) := by
    funext z
    rw [← hwEq z]
  have hrightPath : (fun ω => gmcTiltFiniteCoordinatePath s
      (fun f => X ω f + gaussianCovariance P (fun ω' => X ω' f) L)
      ((M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z))))) = rightLimit := by
    funext ω
    simp only [rightLimit, field, shift]
    simp_rw [hweight]
  change Measure.map (fun ω => gmcTiltFiniteCoordinatePath s
      (fun f => X ω f) (M ω)) (P.withDensity density) =
    Measure.map (fun ω => gmcTiltFiniteCoordinatePath s
      (fun f => X ω f + gaussianCovariance P (fun ω' => X ω' f) L)
      ((M ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * c z))))) P
  rw [hleftPath, hrightPath]
  assumption

end

end DOZZ.Proofs
