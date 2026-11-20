/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.CircleAverage
public import DOZZ.GMC.CircleAverageLimits
public import DOZZ.GMC.EquatorGFFFiniteFDD
public import DOZZ.GFFStructure.PoissonL2
public import DOZZ.GMC.Moments.GaussianFDD
public import DOZZ.GMC.Moments.CircleScaleWick
public import DOZZ.GMC.Moments.InversionSpatialLaw
public import DOZZ.GMC.OpenMassLaw
public import DOZZ.GMC.Moments.ReferenceFinite
import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure
import DOZZ.GMC.Construction.GMCMeasurableVersion
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import DOZZ.GMC.Moments.InversionCutoff

/-! Finite joint laws of the field and arbitrary circle-average regularizations. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

private theorem equatorGFF_test_second_moment {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (X : Ω → Distr) (hX : IsEquatorGFF P X) (f g : TestFn) :
    gaussianCovariance P (fun ω => X ω f) (fun ω => X ω g) = gffCov f g := by
  simpa [ProbabilityTheory.covariance, gaussianCovariance,
    equatorGFF_test_integral X hX f, equatorGFF_test_integral X hX g] using
    equatorGFF_test_covariance X hX f g

private theorem gaussianCovariance_swap {A : Type*} [MeasurableSpace A] (μ : Measure A) (a b : A → ℝ) :
    gaussianCovariance μ a b = gaussianCovariance μ b a := by simp [gaussianCovariance, mul_comm]

private theorem mixed_test_circle_centered {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (q : I → (ℂ × ℝ) ⊕ TestFn) :
    IsCenteredJointlyGaussian P (fun ω i =>
      Sum.elim (fun p => fun ω => Xc ω p.1 p.2) (fun g => fun ω => X ω g) (q i) ω) := by
  apply centeredJointlyGaussian_of_isGaussianProcess
  · exact (circleAverage_tests_isGaussianProcess X Xc hX hXc).comp_right q
  · intro i
    rcases q i with p | g
    · exact (circleAverage_isGaussianProcess P X Xc hX hXc).2 p.1 p.2
    · exact equatorGFF_test_integral X hX g

/-- Finite families of test evaluations and circle averages have the same joint law for any two
equator GFF models. The mixed covariances are fixed by the test and circle kernel identities. -/
theorem equatorGFF_test_circle_fdd_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (P' : Measure Ω') (X' : Ω' → Distr) (hX' : IsEquatorGFF P' X')
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (Xc' : Ω' → ℂ → ℝ → ℝ) (hXc' : IsCircleAverage P' X' Xc')
    {k m : ℕ} (f : Fin k → TestFn) (z : Fin m → ℂ) (r : Fin m → ℝ) :
    Measure.map (fun ω => (fun i => X ω (f i), fun j => Xc ω (z j) (r j))) P =
      Measure.map (fun ω => (fun i => X' ω (f i), fun j => Xc' ω (z j) (r j))) P' := by
  let I := Fin k ⊕ Fin m
  let q : I → (ℂ × ℝ) ⊕ TestFn := Sum.elim (Sum.inr ∘ f) (fun j => Sum.inl (z j, r j))
  let U : Ω → I → ℝ := fun ω i =>
    Sum.elim (fun p => fun ω => Xc ω p.1 p.2) (fun g => fun ω => X ω g) (q i) ω
  let U' : Ω' → I → ℝ := fun ω i =>
    Sum.elim (fun p => fun ω => Xc' ω p.1 p.2) (fun g => fun ω => X' ω g) (q i) ω
  have hu : IsCenteredJointlyGaussian P U := mixed_test_circle_centered P X hX Xc hXc q
  have hu' : IsCenteredJointlyGaussian P' U' := mixed_test_circle_centered P' X' hX' Xc' hXc' q
  have hcov : ∀ i j, gaussianCovariance P (U · i) (U · j) =
      gaussianCovariance P' (U' · i) (U' · j) := by
    intro i j
    cases i <;> cases j <;> simp only [U, U', q, Sum.elim_inl, Sum.elim_inr, Function.comp_apply]
    · simp [equatorGFF_test_second_moment X hX, equatorGFF_test_second_moment X' hX']
    · rw [isCircleAverage_cross_covariance P X hX Xc hXc,
        isCircleAverage_cross_covariance P' X' hX' Xc' hXc']
    · rw [gaussianCovariance_swap P, gaussianCovariance_swap P', isCircleAverage_cross_covariance P X hX Xc hXc,
        isCircleAverage_cross_covariance P' X' hX' Xc' hXc']
    · rw [isCircleAverage_covariance P X hX Xc hXc, isCircleAverage_covariance P' X' hX' Xc' hXc']
  let π : (I → ℝ) → (Fin k → ℝ) × (Fin m → ℝ) := fun w =>
    (fun i => w (Sum.inl i), fun j => w (Sum.inr j))
  have hπ : Measurable π := Measurable.prodMk
    (measurable_pi_iff.mpr fun _ => measurable_pi_apply _) (measurable_pi_iff.mpr fun _ => measurable_pi_apply _)
  have hm := congrArg (Measure.map π)
    (map_eq_of_centeredJointlyGaussian_of_covariance_eq P P' U U' hu hu' hcov)
  rw [AEMeasurable.map_map_of_aemeasurable hπ.aemeasurable (AEMeasurable.of_eval hu.2.1),
    AEMeasurable.map_map_of_aemeasurable hπ.aemeasurable (AEMeasurable.of_eval hu'.2.1)] at hm
  exact hm

private theorem measurable_cutoffWickDensity {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Xc : Ω → ℂ → ℝ → ℝ)
    (h : ∀ r, Measurable (fun p : Ω × ℂ => Xc p.1 p.2 r)) (γ r : ℝ) (ω : Ω) :
    Measurable (fun x => ENNReal.ofReal (circleWick P Xc γ r ω x)) :=
  (measurable_circleWick (P := P) h γ r).ennreal_ofReal.comp (measurable_const.prodMk measurable_id)

private theorem regularizedGMC_eq_withDensity_reference {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Xc : Ω → ℂ → ℝ → ℝ)
    (h : ∀ r, Measurable (fun p : Ω × ℂ => Xc p.1 p.2 r)) (γ r : ℝ) (ω : Ω) :
    regularizedGMC P Xc γ r ω = gmcReferenceMeasure.withDensity
      (fun x => ENNReal.ofReal (circleWick P Xc γ r ω x)) := by
  have he : gmcCircleWickDensity P Xc γ r ω = fun x => ENNReal.ofReal (circleWick P Xc γ r ω x) := by
    funext x
    simp only [gmcCircleWickDensity, circleWick, gaussianVariance, gaussianCovariance, pow_two]
  rw [← he]
  exact regularizedGMC_eq_reference_withDensity P Xc γ r ω
    ((measurable_gmcCircleWickDensity_joint P Xc γ r (h r)).comp (measurable_const.prodMk measurable_id))

/-- Cutoff test integrals are the Wick integrals against the finite GMC reference measure. -/
theorem regularizedGMC_test_integral_eq_reference_wick
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ r : ℝ) (f : BoundedContinuousFunction ℂ ℝ) (ω : Ω) :
    (∫ x, f x ∂regularizedGMC P Xc γ r ω) =
      ∫ x, f x * Real.exp (γ * Xc ω x r - γ ^ 2 / 2 *
        gaussianVariance P (fun ω' => Xc ω' x r)) ∂gmcReferenceMeasure := by
  let := hX.1
  rw [regularizedGMC_eq_withDensity_reference P Xc hXc.1 γ r ω,
    integral_withDensity_eq_integral_toReal_smul (measurable_cutoffWickDensity P Xc hXc.1 γ r ω)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp [circleWick, ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul, mul_comm]

private theorem regularizedGMC_weighted_wick_integrable_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ)
    (f : BoundedContinuousFunction ℂ ℝ) :
    ∀ᵐ ω ∂P, Integrable (fun x => f x * circleWick P Xc γ r ω x) gmcReferenceMeasure := by
  let := hX.1
  filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ r] with ω hw
  let := hw
  have hf := f.integrable (μ := regularizedGMC P Xc γ r ω)
  rw [regularizedGMC_eq_withDensity_reference P Xc hXc.1 γ r ω] at hf
  simpa [circleWick, ENNReal.toReal_ofReal (Real.exp_nonneg _), smul_eq_mul, mul_comm] using
    (integrable_withDensity_iff_integrable_smul' (measurable_cutoffWickDensity P Xc hXc.1 γ r ω)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).mp hf

/-- The mixed field law determines all signed cutoff test integrals jointly. -/
theorem equatorGFF_regularized_test_vector_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (P' : Measure Ω') (X' : Ω' → Distr) (hX' : IsEquatorGFF P' X')
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (Xc' : Ω' → ℂ → ℝ → ℝ) (hXc' : IsCircleAverage P' X' Xc')
    {k m : ℕ} (tests : Fin k → TestFn) (f : Fin m → BoundedContinuousFunction ℂ ℝ)
    (γ r : ℝ) :
    Measure.map (fun ω => (fun i => X ω (tests i), fun j =>
      ∫ x, f j x ∂regularizedGMC P Xc γ r ω)) P =
    Measure.map (fun ω => (fun i => X' ω (tests i), fun j =>
      ∫ x, f j x ∂regularizedGMC P' Xc' γ r ω)) P' := by
  let := hX.1
  let := hX'.1
  let ν : FiniteMeasure ℂ := ⟨gmcReferenceMeasure, ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩⟩
  let v := fun x => gaussianVariance P (fun ω => Xc ω x r)
  let z : Fin m → ℂ → ℝ → ℝ := fun i x t => f i x * Real.exp (γ * t - γ ^ 2 / 2 * v x)
  have hv : Measurable v := circleAverage_variance_measurable Xc hXc.1 r
  have hv' (x : ℂ) : v x = gaussianVariance P' (fun ω => Xc' ω x r) :=
    (isCircleAverage_covariance P X hX Xc hXc x x r r).trans
      (isCircleAverage_covariance P' X' hX' Xc' hXc' x x r r).symm
  have he := spatialIntegral_joint_vector_law_of_fdd_finite ν (fun ω x => Xc ω x r) (fun ω x => Xc' ω x r)
    (fun ω i => X ω (tests i)) (fun ω i => X' ω (tests i))
    (measurable_pi_iff.mpr fun i => (hX.2 (tests i)).1)
    (measurable_pi_iff.mpr fun i => (hX'.2 (tests i)).1)
    z (hXc.1 r) (hXc'.1 r) (fun j => by dsimp [z]; fun_prop)
    (fun i => regularizedGMC_weighted_wick_integrable_ae P X hX Xc hXc γ r (f i))
    (fun i => by
      change ∀ᵐ ω ∂P', Integrable (fun x => z i x (Xc' ω x r)) gmcReferenceMeasure
      simpa only [z, ← hv', circleWick] using
        regularizedGMC_weighted_wick_integrable_ae P' X' hX' Xc' hXc' γ r (f i))
    (fun n xs => equatorGFF_test_circle_fdd_law P X hX P' X' hX' Xc hXc Xc' hXc' tests xs (fun _ => r))
  simp_rw [regularizedGMC_test_integral_eq_reference_wick P X hX Xc hXc,
    regularizedGMC_test_integral_eq_reference_wick P' X' hX' Xc' hXc', ← hv']
  exact he


section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
include hX

/-- Test integrals against a GMC version are almost surely measurable, by the cutoff
approximations in its definition. -/
theorem regularizedGMC_test_integral_aemeasurable_EquatorGFFChaosTransport
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ)
    (f : BoundedContinuousFunction ℂ ℝ) :
    AEMeasurable (fun ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) P :=
  (measurable_integral_of_measurable_measure (regularizedGMC_measurable P X hX Xc hXc γ r)
    f.continuous.stronglyMeasurable).aemeasurable

theorem gmc_test_integral_aemeasurable_of_IsGMCOf
    (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (f : BoundedContinuousFunction ℂ ℝ) :
    AEMeasurable (fun ω => ∫ x, f x ∂M ω) P := by
  obtain ⟨_, Xc, hXc, hconv⟩ := hM
  exact gmc_testIntegral_aemeasurable P X hX γ Xc hXc M hconv f

end

/-- Finite test evaluations and finite families of bounded-continuous GMC integrals have the
same joint law for any two equator-GFF GMC versions. -/
theorem equatorGFF_GMC_test_integral_vector_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (P' : Measure Ω') (X' : Ω' → Distr) (hX' : IsEquatorGFF P' X')
    (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (M' : Ω' → Measure ℂ) (hM' : IsGMCOf P' X' γ M')
    {k m : ℕ} (tests : Fin k → TestFn) (f : Fin m → BoundedContinuousFunction ℂ ℝ) :
    Measure.map (fun ω => (fun i => X ω (tests i), fun j => ∫ x, f j x ∂M ω)) P =
      Measure.map (fun ω => (fun i => X' ω (tests i), fun j => ∫ x, f j x ∂M' ω)) P' := by
  let := hX.1
  let := hX'.1
  obtain ⟨Xc, hXc, hconvX⟩ := hM.2
  obtain ⟨Xc', hXc', hconvY⟩ := hM'.2
  apply gmc_limit_joint_test_vector_law (fun ω i => X ω (tests i)) (fun ω i => X' ω (tests i))
    (AEMeasurable.of_eval fun i => (hX.2 (tests i)).1.aemeasurable)
    (AEMeasurable.of_eval fun i => (hX'.2 (tests i)).1.aemeasurable)
    (fun (n : ℕ) ω j => ∫ x, f j x ∂regularizedGMC P Xc γ n ω)
    (fun (n : ℕ) ω j => ∫ x, f j x ∂regularizedGMC P' Xc' γ n ω) _ _
  · exact fun n => AEMeasurable.of_eval fun j =>
      regularizedGMC_test_integral_aemeasurable_EquatorGFFChaosTransport P X hX Xc hXc γ n (f j)
  · exact fun n => AEMeasurable.of_eval fun j =>
      regularizedGMC_test_integral_aemeasurable_EquatorGFFChaosTransport P' X' hX' Xc' hXc' γ n (f j)
  · exact AEMeasurable.of_eval fun j => gmc_test_integral_aemeasurable_of_IsGMCOf P X hX γ M hM (f j)
  · exact AEMeasurable.of_eval fun j => gmc_test_integral_aemeasurable_of_IsGMCOf P' X' hX' γ M' hM' (f j)
  · exact fun n => equatorGFF_regularized_test_vector_law P X hX P' X' hX' Xc hXc Xc' hXc' tests f γ n
  · exact fun j => (hconvX (f j)).comp tendsto_natCast_atTop_atTop
  · exact fun j => (hconvY (f j)).comp tendsto_natCast_atTop_atTop

/-! For each finite family of open sets, the joint law of their limiting masses and field
evaluations follows by the distance-cutoff approximation and `IsGMCOf` convergence. -/
theorem equatorGFF_GMC_open_mass_test_vector_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (P' : Measure Ω') (X' : Ω' → Distr) (hX' : IsEquatorGFF P' X')
    (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (M' : Ω' → Measure ℂ) (hM' : IsGMCOf P' X' γ M')
    {k m : ℕ} (tests : Fin k → TestFn) (U : Fin m → Set ℂ)
    (hU : ∀ j, IsOpen (U j)) :
    IdentDistrib (fun ω => (fun i => X ω (tests i), fun j => M ω (U j)))
      (fun ω => (fun i => X' ω (tests i), fun j => M' ω (U j))) P P' := by
  let := hX.1
  let := hX'.1
  apply identDistrib_open_mass_pair U hU M M' (fun ω _ => by let := hM.1 ω; exact measure_lt_top _ _)
    (fun ω _ => by let := hM'.1 ω; exact measure_lt_top _ _)
  intro n
  let f := fun j => gmcOpenApprox (U j) (hU j) n
  exact ⟨(AEMeasurable.of_eval fun i => (hX.2 (tests i)).1.aemeasurable).prodMk
      (AEMeasurable.of_eval fun j => gmc_test_integral_aemeasurable_of_IsGMCOf P X hX γ M hM (f j)),
    (AEMeasurable.of_eval fun i => (hX'.2 (tests i)).1.aemeasurable).prodMk
      (AEMeasurable.of_eval fun j => gmc_test_integral_aemeasurable_of_IsGMCOf P' X' hX' γ M' hM' (f j)),
    equatorGFF_GMC_test_integral_vector_law P X hX P' X' hX' γ M hM M' hM' tests f⟩

end DOZZ.Proofs
