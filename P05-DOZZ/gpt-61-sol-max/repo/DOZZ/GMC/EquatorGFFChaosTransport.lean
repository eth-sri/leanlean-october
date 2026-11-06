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
public import DOZZ.GMC.Moments.ChaosLawFDD
public import DOZZ.GMC.Moments.ChaosLawFDDLimit
public import DOZZ.GMC.Moments.ReferenceFinite
import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure
import DOZZ.GMC.Construction.GMCMeasurableVersion
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-! Finite joint laws of the field and arbitrary circle-average regularizations. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω Ω' : Type*} [_inst1 : MeasurableSpace Ω] [_inst2 : MeasurableSpace Ω'] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (P' : Measure Ω') (X' : Ω' → Distr) (hX' : IsEquatorGFF P' X')

include Ω Ω' _inst1 _inst2 P X hX P' X' hX' in
/-- Finite families of test evaluations and circle averages have the same joint law for any two
equator GFF models. The mixed covariances are fixed by the test and circle kernel identities. -/
theorem equatorGFF_test_circle_fdd_law

    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (Xc' : Ω' → ℂ → ℝ → ℝ) (hXc' : IsCircleAverage P' X' Xc')
    {k m : ℕ} (f : Fin k → TestFn) (z : Fin m → ℂ) (r : Fin m → ℝ) :
    Measure.map (fun ω => (fun i => X ω (f i), fun j => Xc ω (z j) (r j))) P =
      Measure.map (fun ω => (fun i => X' ω (f i), fun j => Xc' ω (z j) (r j))) P' := by
  classical
  let T := Fin k ⊕ Fin m
  let q  := fun i =>
    match i with
    | Sum.inl i => Sum.inr (f i)
    | Sum.inr j => Sum.inl (z j, r j)
  let U  := fun ω i =>
    match i with
    | Sum.inl i => X ω (f i)
    | Sum.inr j => Xc ω (z j) (r j)
  let U'  := fun ω i =>
    match i with
    | Sum.inl i => X' ω (f i)
    | Sum.inr j => Xc' ω (z j) (r j)
  have hproc : IsGaussianProcess
      (fun t : (ℂ × ℝ) ⊕ TestFn =>
        Sum.elim (fun p => fun ω => Xc ω p.1 p.2) (fun g => fun ω => X ω g) t) P :=
    circleAverage_tests_isGaussianProcess X Xc hX hXc
  have hproc' : IsGaussianProcess
      (fun t : (ℂ × ℝ) ⊕ TestFn =>
        Sum.elim (fun p => fun ω => Xc' ω p.1 p.2) (fun g => fun ω => X' ω g) t) P' :=
    circleAverage_tests_isGaussianProcess X' Xc' hX' hXc'
  have hUXproc : IsGaussianProcess (fun i : T => fun ω => U ω i) P := by
    have hfun : (fun i : T => fun ω => U ω i) =
        (fun t : (ℂ × ℝ) ⊕ TestFn =>
          Sum.elim (fun p => fun ω => Xc ω p.1 p.2) (fun g => fun ω => X ω g) t) ∘ q := by
      funext i ω
      cases i <;> rfl
    rw [hfun]
    exact hproc.comp_right q
  have hUYproc : IsGaussianProcess (fun i : T => fun ω => U' ω i) P' := by
    have hfun : (fun i : T => fun ω => U' ω i) =
        (fun t : (ℂ × ℝ) ⊕ TestFn =>
          Sum.elim (fun p => fun ω => Xc' ω p.1 p.2) (fun g => fun ω => X' ω g) t) ∘ q := by
      funext i ω
      cases i <;> rfl
    rw [hfun]
    exact hproc'.comp_right q
  have hmeanX : ∀ i : T, (∫ ω, U ω i ∂P) = 0 := by
    intro i
    cases i with
    | inl i => exact equatorGFF_test_integral X hX (f i)
    | inr j => exact (circleAverage_isGaussianProcess P X Xc hX hXc).2 (z j) (r j)
  have hmeanY : ∀ i : T, (∫ ω, U' ω i ∂P') = 0 := by
    intro i
    cases i with
    | inl i => exact equatorGFF_test_integral X' hX' (f i)
    | inr j => exact (circleAverage_isGaussianProcess P' X' Xc' hX' hXc').2 (z j) (r j)
  have hUX  :=
    centeredJointlyGaussian_of_isGaussianProcess P (fun i ω => U ω i) hUXproc hmeanX
  have hUY  :=
    centeredJointlyGaussian_of_isGaussianProcess P' (fun i ω => U' ω i) hUYproc hmeanY
  have hcov : ∀ i j : T,
      gaussianCovariance P (fun ω => U ω i) (fun ω => U ω j) =
        gaussianCovariance P' (fun ω => U' ω i) (fun ω => U' ω j) := by
    have hsymX (A B : Ω → ℝ) : gaussianCovariance P A B = gaussianCovariance P B A := by
      unfold gaussianCovariance
      grind
    have hsymY (A B : Ω' → ℝ) : gaussianCovariance P' A B = gaussianCovariance P' B A := by
      unfold gaussianCovariance
      grind
    intro i j
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        simp only [U, U']
        have hXcov (g h : TestFn) :
            gaussianCovariance P (fun ω => X ω g) (fun ω => X ω h) = gffCov g h := by
          unfold gaussianCovariance
          calc
            (∫ ω, X ω g * X ω h ∂P) = covariance (fun ω => X ω g) (fun ω => X ω h) P := by
              rw [ProbabilityTheory.covariance, equatorGFF_test_integral X hX g,
                equatorGFF_test_integral X hX h]
              simp
            _ = gffCov g h := equatorGFF_test_covariance X hX g h
        have hYcov (g h : TestFn) :
            gaussianCovariance P' (fun ω => X' ω g) (fun ω => X' ω h) = gffCov g h := by
          unfold gaussianCovariance
          calc
            (∫ ω, X' ω g * X' ω h ∂P') = covariance (fun ω => X' ω g) (fun ω => X' ω h) P' := by
              rw [ProbabilityTheory.covariance, equatorGFF_test_integral X' hX' g,
                equatorGFF_test_integral X' hX' h]
              simp
            _ = gffCov g h := equatorGFF_test_covariance X' hX' g h
        rw [hXcov, hYcov]
      | inr j =>
        have hx := isCircleAverage_cross_covariance P X hX Xc hXc (z j) (r j) (f i)
        have hy := isCircleAverage_cross_covariance P' X' hX' Xc' hXc' (z j) (r j) (f i)
        simp only [U, U']
        rw [hx, hy]
    | inr i =>
      cases j with
      | inl j =>
        have hx := isCircleAverage_cross_covariance P X hX Xc hXc (z i) (r i) (f j)
        have hy := isCircleAverage_cross_covariance P' X' hX' Xc' hXc' (z i) (r i) (f j)
        grind
      | inr j =>
        simp only [U, U']
        rw [isCircleAverage_covariance P X hX Xc hXc,
          isCircleAverage_covariance P' X' hX' Xc' hXc']
  have hUlaw  := map_eq_of_centeredJointlyGaussian_of_covariance_eq P P' U U' hUX hUY hcov
  let π : (T → ℝ) → (Fin k → ℝ) × (Fin m → ℝ) := fun w =>
    (fun i => w (Sum.inl i), fun j => w (Sum.inr j))
  have hπ : Measurable π := by
    fun_prop
  have hUmeas : AEMeasurable U P := by
    apply AEMeasurable.of_eval
    intro i
    exact hUX.2.1 i
  have hUYmeas : AEMeasurable U' P' := by
    apply AEMeasurable.of_eval
    intro i
    exact hUY.2.1 i
  have hXmap : Measure.map (fun ω => (fun i => X ω (f i), fun j => Xc ω (z j) (r j))) P =
      (Measure.map U P).map π := (AEMeasurable.map_map_of_aemeasurable hπ.aemeasurable hUmeas).symm
  have hYmap : Measure.map (fun ω => (fun i => X' ω (f i), fun j => Xc' ω (z j) (r j))) P' =
      (Measure.map U' P').map π := (AEMeasurable.map_map_of_aemeasurable hπ.aemeasurable hUYmeas).symm
  rw [hXmap, hYmap, hUlaw]


/-- Cutoff test integrals are the Wick integrals against the finite GMC reference measure. -/
theorem regularizedGMC_test_integral_eq_reference_wick
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ r : ℝ) (f : BoundedContinuousFunction ℂ ℝ) (ω : Ω) :
    (∫ x, f x ∂regularizedGMC P Xc γ r ω) =
      ∫ x, f x * Real.exp (γ * Xc ω x r - γ ^ 2 / 2 *
        gaussianVariance P (fun ω' => Xc ω' x r)) ∂gmcReferenceMeasure := by
  let V  := fun x => ∫ ω', Xc ω' x r ^ 2 ∂P
  let D  := fun x => ENNReal.ofReal
    (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * V x) * normPlus x ^ (-4 : ℝ))
  let G  := fun x => ENNReal.ofReal (normPlus x ^ (-4 : ℝ))
  have hVmeas : Measurable V := by
    have h := @circleAverage_variance_measurable Ω _ P hX.1 Xc hXc.1 r
    convert h using 1
    funext x
    simp [V, gaussianVariance, gaussianCovariance, pow_two]
  have hfield : Measurable (fun x : ℂ => Xc ω x r) :=
    (hXc.1 r).comp (measurable_const.prodMk measurable_id)
  have hnorm : Measurable (fun x : ℂ => normPlus x) := measurable_const.max measurable_norm
  have hD : Measurable D := by
    dsimp [D]
    fun_prop
  have hG : Measurable G := by
    dsimp [G]
    fun_prop
  have hDtop : ∀ᵐ x ∂volume, D x < ∞ := by
    continuity
  have hGtop : ∀ᵐ x ∂volume, G x < ∞ := by
    filter_upwards [] with x
    exact ENNReal.ofReal_lt_top
  have hnormpos (x : ℂ) : 0 < normPlus x :=
    lt_of_lt_of_le one_pos (le_max_left _ _)
  have hfactor (x : ℂ) :
      (D x).toReal * f x = (G x).toReal * (f x *
        Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * gaussianVariance P
          (fun ω' => Xc ω' x r))) := by
    simp only [D, G]
    have hvariance : V x = gaussianVariance P (fun ω' => Xc ω' x r) := by
      simp [V, gaussianVariance, gaussianCovariance, pow_two]
    rw [hvariance]
    have hnormpow : 0 ≤ normPlus x ^ (-4 : ℝ) :=
      le_of_lt (Real.rpow_pos_of_pos (hnormpos x) _)
    have hnonneg : 0 ≤ Real.exp (γ * Xc ω x r - γ ^ 2 / 2 *
        gaussianVariance P (fun ω' => Xc ω' x r)) *
        normPlus x ^ (-4 : ℝ) := mul_nonneg (le_of_lt (Real.exp_pos _)) hnormpow
    rw [ENNReal.toReal_ofReal hnonneg, ENNReal.toReal_ofReal hnormpow]
    ring
  calc
    (∫ x, f x ∂regularizedGMC P Xc γ r ω) =
        ∫ x, (D x).toReal * f x ∂volume := by
      rw [regularizedGMC, show
          (fun x => ENNReal.ofReal (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 *
            ∫ ω', Xc ω' x r ^ 2 ∂P) * normPlus x ^ (-4 : ℝ))) = D by
            funext x
            simp [D, V]]
      rw [integral_withDensity_eq_integral_toReal_smul hD hDtop]
      simp only [smul_eq_mul]
    _ = ∫ x, (G x).toReal * (f x *
        Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * gaussianVariance P
          (fun ω' => Xc ω' x r))) ∂volume := by
      simp_all
    _ = ∫ x, f x * Real.exp (γ * Xc ω x r - γ ^ 2 / 2 *
        gaussianVariance P (fun ω' => Xc ω' x r)) ∂gmcReferenceMeasure := by
      rw [gmcReferenceMeasure, show
          (fun x => ENNReal.ofReal (normPlus x ^ (-4 : ℝ))) = G by rfl]
      rw [integral_withDensity_eq_integral_toReal_smul hG hGtop]
      simp only [smul_eq_mul]


include Ω Ω' _inst1 _inst2 P X hX P' X' hX' in
/-- Any finite vector of cutoff test masses has the same law jointly with finitely many field
tests for two equator GFF models. Signed tests are split into their positive and negative parts;
the Wick laws are transferred by `ChaosLawFDD`. -/
theorem equatorGFF_regularized_test_vector_law

    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (Xc' : Ω' → ℂ → ℝ → ℝ) (hXc' : IsCircleAverage P' X' Xc')
    {k m : ℕ} (tests : Fin k → TestFn) (f : Fin m → BoundedContinuousFunction ℂ ℝ)
    (γ r : ℝ) :
    Measure.map (fun ω => (fun i => X ω (tests i), fun j =>
      ∫ x, f j x ∂regularizedGMC P Xc γ r ω)) P =
    Measure.map (fun ω => (fun i => X' ω (tests i), fun j =>
      ∫ x, f j x ∂regularizedGMC P' Xc' γ r ω)) P' := by
  classical
  let  := hX.1
  let  := hX'.1
  let ν : FiniteMeasure ℂ := ⟨gmcReferenceMeasure,
    ⟨lt_top_iff_ne_top.mpr gmcReferenceMeasure_univ_ne_top⟩⟩
  let N := m + m
  let V  := fun ω i => X ω (tests i)
  let V'  := fun ω i => X' ω (tests i)
  let FX  := fun ω x => Xc ω x r
  let FY  := fun ω x => Xc' ω x r
  let variance  := fun x =>
    (gaussianVariance P (fun ω => Xc ω x r)).toNNReal
  let wPos  := fun j => max (f j) 0
  let wNeg  := fun j => max (-(f j)) 0
  let weightBCF : Fin N → BoundedContinuousFunction ℂ ℝ := Fin.addCases wPos wNeg
  let weight  := fun i x => weightBCF i x
  let WickX  := fun ω i =>
    ∫ x, weight i x * Real.exp (γ * FX ω x - γ ^ 2 / 2 * (variance x : ℝ)) ∂(ν : Measure ℂ)
  let WickY  := fun ω i =>
    ∫ x, weight i x * Real.exp (γ * FY ω x - γ ^ 2 / 2 * (variance x : ℝ)) ∂(ν : Measure ℂ)
  let LX  := fun ω => (V ω, WickX ω)
  let LY  := fun ω => (V' ω, WickY ω)
  let A : ((Fin k → ℝ) × (Fin N → ℝ)) → (Fin k → ℝ) × (Fin m → ℝ) := fun p =>
    (p.1, fun j => p.2 (Fin.castAdd m j) - p.2 (Fin.natAdd m j))
  let TargetX  := fun ω =>
    (V ω, fun j => ∫ x, f j x ∂regularizedGMC P Xc γ r ω)
  let TargetY  := fun ω =>
    (V' ω, fun j => ∫ x, f j x ∂regularizedGMC P' Xc' γ r ω)
  have hV : Measurable V := by
    apply measurable_pi_iff.2
    intro i
    exact (hX.2 (tests i)).1
  have hV' : Measurable V' := by
    apply measurable_pi_iff.2
    intro i
    exact (hX'.2 (tests i)).1
  have hFX  := hXc.1 r
  have hFY  := hXc'.1 r
  have hvariance  := measurable_real_toNNReal.comp
      (@circleAverage_variance_measurable Ω _ P hX.1 Xc hXc.1 r)
  have hvariance_nonneg (x : ℂ) :
      0 ≤ gaussianVariance P (fun ω => Xc ω x r) :=
    (circleAverage_gaussian_law_and_variance_nonneg P X hX Xc hXc x r).2
  have hvariance_real (x : ℂ) : (variance x : ℝ) =
      gaussianVariance P (fun ω => Xc ω x r) := by
    continuity
  have hvariance_eq (x : ℂ) :
      gaussianVariance P (fun ω => Xc ω x r) =
        gaussianVariance P' (fun ω => Xc' ω x r) := by
    have hleft := isCircleAverage_covariance P X hX Xc hXc x x r r
    have hright := isCircleAverage_covariance P' X' hX' Xc' hXc' x x r r
    exact hleft.trans hright.symm

  have hvarianceY_real (x : ℂ) : (variance x : ℝ) =
      gaussianVariance P' (fun ω => Xc' ω x r) := by
    simp_all
  have hweightCast (j : Fin m) : weight (Fin.castAdd m j) = wPos j := by
    grind
  have hweightNat (j : Fin m) : weight (Fin.natAdd m j) = wNeg j := by
    grind
  have hweight_meas : ∀ i, Measurable (weight i) := by
    fun_prop (disch := positivity)
  have hweight_nonneg : ∀ i x, 0 ≤ weight i x := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j x
      rw [hweightCast]
      exact le_max_right _ _
    · intro j x
      rw [hweightNat]
      exact le_max_right _ _
  have hweight_bdd : ∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, weight i x ≤ C := by
    have hbound (g : BoundedContinuousFunction ℂ ℝ) (hg : ∀ x, 0 ≤ g x) :
        ∃ C : ℝ, 0 ≤ C ∧ ∀ x, g x ≤ C := by
      obtain ⟨C, hC⟩ := g.map_bounded'
      have hC0 : 0 ≤ C := by simpa using hC 0 0
      refine ⟨|g 0| + C, by positivity, ?_⟩
      intro x
      have hd : |g x - g 0| ≤ C := hC x 0
      grind
    bound
  have hweight_int : ∀ i, Integrable (weight i) (ν.normalize : Measure ℂ) := by
    intro i
    obtain ⟨C, hC0, hC⟩ := hweight_bdd i
    refine (integrable_const C).mono' (weightBCF i).continuous.aestronglyMeasurable ?_
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hweight_nonneg i x)]
    exact hC x
  have hXlaw : ∀ x, HasLaw (fun ω => FX ω x) (gaussianReal 0 (variance x)) P := by
    intro x
    exact (circleAverage_gaussian_law_and_variance_nonneg P X hX Xc hXc x r).1
  have hYlaw : ∀ x, HasLaw (fun ω => FY ω x) (gaussianReal 0 (variance x)) P' := by
    intro x
    have h := (circleAverage_gaussian_law_and_variance_nonneg P' X' hX' Xc' hXc' x r).1
    have hv : (gaussianVariance P' (fun ω => Xc' ω x r)).toNNReal = variance x := by
      rw [← hvariance_eq]
    simpa [FY, hv] using h
  have hFDD : ∀ (s : ℕ) (xs : Fin s → ℂ),
      Measure.map (fun ω => (V ω, fun i => FX ω (xs i))) P =
        Measure.map (fun ω => (V' ω, fun i => FY ω (xs i))) P' := by
    intro s xs
    exact (equatorGFF_test_circle_fdd_law P X hX P' X' hX' Xc hXc Xc' hXc'
        tests xs (fun _ => r))


  have hWickXmeas (i : Fin N) : Measurable
      (fun ω => ∫ x, weight i x * Real.exp
        (γ * FX ω x - γ ^ 2 / 2 * (variance x : ℝ)) ∂(ν : Measure ℂ)) := by
    have hG : Measurable (fun p : Ω × ℂ => weight i p.2 * Real.exp
        (γ * FX p.1 p.2 - γ ^ 2 / 2 * (variance p.2 : ℝ))) := by
      fun_prop
    exact hG.stronglyMeasurable.integral_prod_right'.measurable
  have hWickYmeas (i : Fin N) : Measurable
      (fun ω => ∫ x, weight i x * Real.exp
        (γ * FY ω x - γ ^ 2 / 2 * (variance x : ℝ)) ∂(ν : Measure ℂ)) := by
    have hG : Measurable (fun p : Ω' × ℂ => weight i p.2 * Real.exp
        (γ * FY p.1 p.2 - γ ^ 2 / 2 * (variance p.2 : ℝ))) := by
      fun_prop
    exact hG.stronglyMeasurable.integral_prod_right'.measurable
  have hLXmeas : Measurable LX := by
    apply Measurable.prodMk hV
    exact measurable_pi_iff.2 hWickXmeas
  have hLYmeas : Measurable LY := by
    apply Measurable.prodMk hV'
    exact measurable_pi_iff.2 hWickYmeas
  have htest : ∀ φ : BoundedContinuousFunction
      ((Fin k → ℝ) × (Fin N → ℝ)) ℝ,
      (∫ ω, φ (LX ω) ∂P) = ∫ ω, φ (LY ω) ∂P' := by
    intro φ
    exact chaosLawFDD_boundedWeights ν FX FY V V' variance weight γ
      hV hV' hFX hFY hvariance hweight_meas hweight_nonneg hweight_bdd
      hXlaw hYlaw hFDD φ
  have hLaw : Measure.map LX P = Measure.map LY P' := by
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro φ
    calc
      (∫ y, φ y ∂Measure.map LX P) = ∫ ω, φ (LX ω) ∂P :=
        integral_map hLXmeas.aemeasurable φ.continuous.measurable.aestronglyMeasurable
      _ = ∫ ω, φ (LY ω) ∂P' := htest φ
      _ = ∫ y, φ y ∂Measure.map LY P' :=
        (integral_map hLYmeas.aemeasurable φ.continuous.measurable.aestronglyMeasurable).symm
  have hA : Measurable A := by
    fun_prop
  have hALaw : Measure.map (A ∘ LX) P = Measure.map (A ∘ LY) P' := by
    calc
      Measure.map (A ∘ LX) P = Measure.map A (Measure.map LX P) :=
        (Measure.map_map hA hLXmeas).symm
      _ = Measure.map A (Measure.map LY P') := congrArg (Measure.map A) hLaw
      _ = Measure.map (A ∘ LY) P' :=
        Measure.map_map hA hLYmeas
  have hνeq : (ν : Measure ℂ) = (ν.mass : ℝ≥0) • (ν.normalize : Measure ℂ) := congrArg (fun μ : FiniteMeasure ℂ => (μ : Measure ℂ)) ν.self_eq_mass_smul_normalize
  have hWickIntXNorm : ∀ i, ∀ᵐ ω ∂P, Integrable (fun x => weight i x *
      Real.exp (γ * FX ω x - γ ^ 2 / 2 * (variance x : ℝ))) (ν.normalize : Measure ℂ) := by
    intro i
    exact ae_integrable_weighted_wick_sections (ν.normalize : Measure ℂ) FX variance
      (weight i) γ hFX hvariance (hweight_meas i) hXlaw (hweight_nonneg i) (hweight_int i)
  have hWickIntYNorm : ∀ i, ∀ᵐ ω ∂P', Integrable (fun x => weight i x *
      Real.exp (γ * FY ω x - γ ^ 2 / 2 * (variance x : ℝ))) (ν.normalize : Measure ℂ) := by
    intro i
    exact ae_integrable_weighted_wick_sections (ν.normalize : Measure ℂ) FY variance
      (weight i) γ hFY hvariance (hweight_meas i) hYlaw (hweight_nonneg i) (hweight_int i)
  have hWickIntX : ∀ i, ∀ᵐ ω ∂P, Integrable (fun x => weight i x *
      Real.exp (γ * FX ω x - γ ^ 2 / 2 * (variance x : ℝ))) (ν : Measure ℂ) := by
    intro i
    filter_upwards [hWickIntXNorm i] with ω hω
    rw [hνeq]
    exact hω.smul_measure_nnreal
  have hWickIntY : ∀ i, ∀ᵐ ω ∂P', Integrable (fun x => weight i x *
      Real.exp (γ * FY ω x - γ ^ 2 / 2 * (variance x : ℝ))) (ν : Measure ℂ) := by
    intro i
    filter_upwards [hWickIntYNorm i] with ω hω
    rw [hνeq]
    exact hω.smul_measure_nnreal
  have hsplit (j : Fin m) (x : ℂ) : f j x =
      weight (Fin.castAdd m j) x - weight (Fin.natAdd m j) x := by
    rw [hweightCast, hweightNat]
    change f j x = max (f j x) 0 - max (-(f j x)) 0
    norm_num
  have hmassX (ω : Ω) (j : Fin m)
      (hω : ∀ i, Integrable (fun x => weight i x *
        Real.exp (γ * FX ω x - γ ^ 2 / 2 * (variance x : ℝ))) (ν : Measure ℂ)) :
      (∫ x, f j x ∂regularizedGMC P Xc γ r ω) =
        WickX ω (Fin.castAdd m j) - WickX ω (Fin.natAdd m j) := by
    have hpoint (x : ℂ) : f j x * Real.exp
        (γ * FX ω x - γ ^ 2 / 2 * gaussianVariance P (fun ω' => Xc ω' x r)) =
        (weight (Fin.castAdd m j) x * Real.exp
            (γ * FX ω x - γ ^ 2 / 2 * (variance x : ℝ))) -
          (weight (Fin.natAdd m j) x * Real.exp
            (γ * FX ω x - γ ^ 2 / 2 * (variance x : ℝ))) := by
      rw [← hvariance_real x, hsplit, sub_mul]
    calc
      (∫ x, f j x ∂regularizedGMC P Xc γ r ω) =
          ∫ x, f j x * Real.exp
            (γ * FX ω x - γ ^ 2 / 2 * gaussianVariance P (fun ω' => Xc ω' x r))
              ∂gmcReferenceMeasure :=
        regularizedGMC_test_integral_eq_reference_wick P X hX Xc hXc γ r (f j) ω
      _ = ∫ x, (weight (Fin.castAdd m j) x * Real.exp
          (γ * FX ω x - γ ^ 2 / 2 * (variance x : ℝ))) -
          (weight (Fin.natAdd m j) x * Real.exp
          (γ * FX ω x - γ ^ 2 / 2 * (variance x : ℝ))) ∂(ν : Measure ℂ) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
      _ = WickX ω (Fin.castAdd m j) - WickX ω (Fin.natAdd m j) := by
        rw [integral_sub (hω _) (hω _)]
  have hmassY (ω : Ω') (j : Fin m)
      (hω : ∀ i, Integrable (fun x => weight i x *
        Real.exp (γ * FY ω x - γ ^ 2 / 2 * (variance x : ℝ))) (ν : Measure ℂ)) :
      (∫ x, f j x ∂regularizedGMC P' Xc' γ r ω) =
        WickY ω (Fin.castAdd m j) - WickY ω (Fin.natAdd m j) := by
    have hpoint (x : ℂ) : f j x * Real.exp
        (γ * FY ω x - γ ^ 2 / 2 * gaussianVariance P' (fun ω' => Xc' ω' x r)) =
        (weight (Fin.castAdd m j) x * Real.exp
            (γ * FY ω x - γ ^ 2 / 2 * (variance x : ℝ))) -
          (weight (Fin.natAdd m j) x * Real.exp
            (γ * FY ω x - γ ^ 2 / 2 * (variance x : ℝ))) := by
      rw [← hvarianceY_real x, hsplit, sub_mul]
    calc
      (∫ x, f j x ∂regularizedGMC P' Xc' γ r ω) =
          ∫ x, f j x * Real.exp
            (γ * FY ω x - γ ^ 2 / 2 * gaussianVariance P' (fun ω' => Xc' ω' x r))
              ∂gmcReferenceMeasure :=
        regularizedGMC_test_integral_eq_reference_wick P' X' hX' Xc' hXc' γ r (f j) ω
      _ = ∫ x, (weight (Fin.castAdd m j) x * Real.exp
          (γ * FY ω x - γ ^ 2 / 2 * (variance x : ℝ))) -
          (weight (Fin.natAdd m j) x * Real.exp
          (γ * FY ω x - γ ^ 2 / 2 * (variance x : ℝ))) ∂(ν : Measure ℂ) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hpoint
      _ = WickY ω (Fin.castAdd m j) - WickY ω (Fin.natAdd m j) := by
        rw [integral_sub (hω _) (hω _)]
  have hTargetX : TargetX =ᵐ[P] A ∘ LX := by
    filter_upwards [ae_all_iff.2 hWickIntX] with ω hω
    dsimp [TargetX, A, LX]
    congr 1
    funext j
    exact hmassX ω j hω
  have hTargetY : TargetY =ᵐ[P'] A ∘ LY := by
    filter_upwards [ae_all_iff.2 hWickIntY] with ω hω
    dsimp [TargetY, A, LY]
    congr 1
    funext j
    exact hmassY ω j hω
  calc
    Measure.map TargetX P = Measure.map (A ∘ LX) P := Measure.map_congr hTargetX
    _ = Measure.map (A ∘ LY) P' := hALaw
    _ = Measure.map TargetY P' := (Measure.map_congr hTargetY).symm


theorem gmc_test_integral_aemeasurable_of_IsGMCOf
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (f : BoundedContinuousFunction ℂ ℝ) :
    AEMeasurable (fun ω => ∫ x, f x ∂M ω) P := by
  rcases hM.2 with ⟨Xc, hXc, hconv⟩
  apply (hconv f).aemeasurable
  intro r
  exact regularizedGMC_testIntegral_aemeasurable P X hX Xc hXc γ r f

include Ω Ω' _inst1 _inst2 P X hX P' X' hX' in
/-- Finite test evaluations and finite families of bounded-continuous GMC integrals have the
same joint law for any two equator-GFF GMC versions. -/
theorem equatorGFF_GMC_test_integral_vector_law

    (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (M' : Ω' → Measure ℂ) (hM' : IsGMCOf P' X' γ M')
    {k m : ℕ} (tests : Fin k → TestFn) (f : Fin m → BoundedContinuousFunction ℂ ℝ) :
    Measure.map (fun ω => (fun i => X ω (tests i), fun j => ∫ x, f j x ∂M ω)) P =
      Measure.map (fun ω => (fun i => X' ω (tests i), fun j => ∫ x, f j x ∂M' ω)) P' := by
  classical
  let  := hX.1
  let  := hX'.1
  rcases hM.2 with ⟨Xc, hXc, hconvX⟩
  rcases hM'.2 with ⟨Xc', hXc', hconvY⟩
  let I := Fin k ⊕ Fin m
  let pairX  := fun ω =>
    (fun i => X ω (tests i), fun j => ∫ x, f j x ∂M ω)
  let pairY  := fun ω =>
    (fun i => X' ω (tests i), fun j => ∫ x, f j x ∂M' ω)
  let cutoffX : ℕ → Ω → (Fin k → ℝ) × (Fin m → ℝ) := fun n ω =>
    (fun i => X ω (tests i), fun j =>
      ∫ x, f j x ∂regularizedGMC P Xc γ (n : ℝ) ω)
  let cutoffY : ℕ → Ω' → (Fin k → ℝ) × (Fin m → ℝ) := fun n ω =>
    (fun i => X' ω (tests i), fun j =>
      ∫ x, f j x ∂regularizedGMC P' Xc' γ (n : ℝ) ω)
  let pack : ((Fin k → ℝ) × (Fin m → ℝ)) → I → ℝ := fun q i =>
    Sum.elim q.1 q.2 i
  let unpack : (I → ℝ) → (Fin k → ℝ) × (Fin m → ℝ) := fun q =>
    (fun i => q (Sum.inl i), fun j => q (Sum.inr j))
  let UcutX  := fun n => pack ∘ cutoffX n
  let UcutY  := fun n => pack ∘ cutoffY n
  let UlimX  := fun ω => pack (pairX ω)
  let UlimY  := fun ω => pack (pairY ω)
  have hV : Measurable (fun ω : Ω => fun i => X ω (tests i)) := by
    apply measurable_pi_iff.2
    intro i
    exact (hX.2 (tests i)).1
  have hV' : Measurable (fun ω : Ω' => fun i => X' ω (tests i)) := by
    apply measurable_pi_iff.2
    intro i
    exact (hX'.2 (tests i)).1
  have hpack : Measurable pack := by
    rw [measurable_pi_iff]
    intro i
    cases i with
    | inl i => measurability
    | inr j => measurability
  have hunpack : Measurable unpack := by
    fun_prop
  have hpairCutX : ∀ n, AEMeasurable (cutoffX n) P := by
    intro n
    refine hV.aemeasurable.prodMk ?_
    apply AEMeasurable.of_eval
    intro j
    exact regularizedGMC_testIntegral_aemeasurable P X hX Xc hXc γ (n : ℝ) (f j)
  have hpairCutY : ∀ n, AEMeasurable (cutoffY n) P' := by
    intro n
    refine hV'.aemeasurable.prodMk ?_
    apply AEMeasurable.of_eval
    intro j
    exact regularizedGMC_testIntegral_aemeasurable P' X' hX' Xc' hXc' γ (n : ℝ) (f j)
  have hpairLimX : AEMeasurable pairX P := by
    refine hV.aemeasurable.prodMk ?_
    apply AEMeasurable.of_eval
    exact fun a => gmc_test_integral_aemeasurable_of_IsGMCOf P X hX γ M hM (f a)
  have hpairLimY : AEMeasurable pairY P' := by
    refine hV'.aemeasurable.prodMk ?_
    apply AEMeasurable.of_eval
    exact fun a => gmc_test_integral_aemeasurable_of_IsGMCOf P' X' hX' γ M' hM' (f a)
  have hUcutX  := fun n =>
    hpack.aemeasurable.comp_aemeasurable (hpairCutX n)
  have hUcutY  := fun n =>
    hpack.aemeasurable.comp_aemeasurable (hpairCutY n)
  have hUlimX  :=
    hpack.aemeasurable.comp_aemeasurable hpairLimX
  have hUlimY  :=
    hpack.aemeasurable.comp_aemeasurable hpairLimY
  have hcutoffPairLaw (n : ℕ) : Measure.map (cutoffX n) P = Measure.map (cutoffY n) P' := equatorGFF_regularized_test_vector_law P X hX P' X' hX' Xc hXc Xc' hXc'
      tests f γ (n : ℝ)
  have hcutoffLaw (n : ℕ) : Measure.map (UcutX n) P = Measure.map (UcutY n) P' := by
    have hcompX : pack ∘ cutoffX n = UcutX n := rfl
    have hcompY : pack ∘ cutoffY n = UcutY n := rfl
    rw [← hcompX, ← hcompY]
    calc
      Measure.map (pack ∘ cutoffX n) P = (Measure.map (cutoffX n) P).map pack :=
        (AEMeasurable.map_map_of_aemeasurable hpack.aemeasurable (hpairCutX n)).symm
      _ = (Measure.map (cutoffY n) P').map pack := congrArg (Measure.map pack) (hcutoffPairLaw n)
      _ = Measure.map (pack ∘ cutoffY n) P' :=
        AEMeasurable.map_map_of_aemeasurable hpack.aemeasurable (hpairCutY n)
  have hr : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hconvXcoord (i : I) : TendstoInMeasure P (fun n ω => UcutX n ω i) atTop
      (fun ω => UlimX ω i) := by
    cases i with
    | inl i =>
      rw [tendstoInMeasure_iff_norm]
      intro ε hε
      have hset : ∀ n : ℕ, {ω | ε ≤ ‖UcutX n ω (Sum.inl i) - UlimX ω (Sum.inl i)‖} = ∅ := by
        intro n
        ext ω
        simp [UcutX, UlimX, pack, cutoffX, pairX, not_le_of_gt hε]
      simp_all
    | inr j =>
      exact (hconvX (f j)).comp hr
  have hconvYcoord (i : I) : TendstoInMeasure P' (fun n ω => UcutY n ω i) atTop
      (fun ω => UlimY ω i) := by
    cases i with
    | inl i =>
      rw [tendstoInMeasure_iff_norm]
      intro ε hε
      have hset : ∀ n : ℕ, {ω | ε ≤ ‖UcutY n ω (Sum.inl i) - UlimY ω (Sum.inl i)‖} = ∅ := by
        intro n
        ext ω
        simp [UcutY, UlimY, pack, cutoffY, pairY, not_le_of_gt hε]
      simp_all
    | inr j =>
      exact (hconvY (f j)).comp hr
  have hconvUlimX  :=
    tendstoInMeasure_pi_finite P UcutX UlimX hconvXcoord
  have hconvUlimY  :=
    tendstoInMeasure_pi_finite P' UcutY UlimY hconvYcoord
  have hULaw  :=
    map_eq_of_seq_map_eq_of_tendstoInMeasure UcutX UcutY UlimX UlimY
      hUcutX hUcutY hUlimX hUlimY hcutoffLaw hconvUlimX hconvUlimY
  have hpackUnpackX : unpack ∘ UlimX = pairX := by
    abel
  have hpackUnpackY : unpack ∘ UlimY = pairY := by
    abel
  calc
    Measure.map pairX P = Measure.map (unpack ∘ UlimX) P := by rw [hpackUnpackX]
    _ = (Measure.map UlimX P).map unpack :=
      (AEMeasurable.map_map_of_aemeasurable hunpack.aemeasurable hUlimX).symm
    _ = (Measure.map UlimY P').map unpack := congrArg (Measure.map unpack) hULaw
    _ = Measure.map pairY P' := AEMeasurable.map_map_of_aemeasurable hunpack.aemeasurable hUlimY


/-- Bounded continuous distance cutoffs increasing to the indicator of an open set. -/
noncomputable def gmcOpenApprox (U : Set ℂ) (hU : IsOpen U) (n : ℕ) :
    BoundedContinuousFunction ℂ ℝ := by
  have _ := hU
  classical
  by_cases h : U = Set.univ
  · exact 1
  · exact BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x => min 1 ((n : ℝ) * Metric.infDist x Uᶜ))
      (continuous_const.min (continuous_const.mul (Metric.continuous_infDist_pt _)))
      1 (by
        intro x
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · exact min_le_left _ _
        · exact le_min (by norm_num) (mul_nonneg (by positivity) Metric.infDist_nonneg))

theorem gmcOpenApprox_bounds (U : Set ℂ) (hU : IsOpen U) (n : ℕ) (x : ℂ) :
    0 ≤ gmcOpenApprox U hU n x ∧ gmcOpenApprox U hU n x ≤ 1 := by
  classical
  by_cases h : U = Set.univ
  · simp [gmcOpenApprox, h]
  · constructor
    · simp only [gmcOpenApprox, h]
      exact le_min (by norm_num) (mul_nonneg (by positivity) Metric.infDist_nonneg)
    · simp only [gmcOpenApprox, h]
      exact min_le_left _ _

theorem gmcOpenApprox_tendsto (U : Set ℂ) (hU : IsOpen U) (x : ℂ) :
    Tendsto (fun n => gmcOpenApprox U hU n x) atTop (𝓝 (U.indicator 1 x)) := by
  classical
  by_cases h : U = Set.univ
  · simp [gmcOpenApprox, h]
  · have hcomp : (Uᶜ : Set ℂ).Nonempty := by
      by_contra hn
      have he  := Set.not_nonempty_iff_eq_empty.mp hn
      simp_all
    by_cases hx : x ∈ U
    · let d  := Metric.infDist x (Uᶜ : Set ℂ)
      have hx' : x ∉ Uᶜ := by simpa using hx
      have hd : 0 < d := (hU.isClosed_compl.notMem_iff_infDist_pos hcomp).1 hx'
      obtain ⟨N, hN⟩ := exists_nat_gt (d⁻¹)
      have hev : ∀ᶠ n : ℕ in atTop,
          gmcOpenApprox U hU n x = 1 := by
        filter_upwards [eventually_ge_atTop N] with n hn
        have hn' : d⁻¹ < (n : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast hn)
        have hmul : 1 ≤ (n : ℝ) * d := by
          have hlt := mul_lt_mul_of_pos_right hn' hd
          grind
        have hmul' : 1 ≤ (n : ℝ) * Metric.infDist x Uᶜ := hmul
        simp [gmcOpenApprox, h, min_eq_left hmul']
      have htarget : U.indicator (1 : ℂ → ℝ) x = 1 := by simp [hx]
      rw [htarget]
      exact tendsto_nhds_of_eventually_eq hev
    · have hd : Metric.infDist x (Uᶜ : Set ℂ) = 0 := Metric.infDist_zero_of_mem hx
      have hev : ∀ᶠ n : ℕ in atTop, gmcOpenApprox U hU n x = 0 := by
        filter_upwards [] with n
        simp [gmcOpenApprox, h, hd]
      have htarget : U.indicator (1 : ℂ → ℝ) x = 0 := by simp [hx]
      rw [htarget]
      exact tendsto_nhds_of_eventually_eq hev

theorem gmcOpenApprox_integral_tendsto
    (μ : Measure ℂ) [IsFiniteMeasure μ] (U : Set ℂ) (hU : IsOpen U) :
    Tendsto (fun n => ∫ x, gmcOpenApprox U hU n x ∂μ) atTop
      (𝓝 ((μ U).toReal)) := by
  let F : ℂ → ℝ := U.indicator 1
  have hboundInt : Integrable (fun _ : ℂ => (1 : ℝ)) μ := integrable_const 1
  have hbound (n : ℕ) : ∀ᵐ x ∂μ, ‖gmcOpenApprox U hU n x‖ ≤ (1 : ℝ) := by
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (gmcOpenApprox_bounds U hU n x).1]
    exact (gmcOpenApprox_bounds U hU n x).2
  have hpoint : ∀ᵐ x ∂μ,
      Tendsto (fun n => gmcOpenApprox U hU n x) atTop (𝓝 (F x)) := by
    filter_upwards [] with x
    exact gmcOpenApprox_tendsto U hU x
  have hDCT := tendsto_integral_of_dominated_convergence
    (bound := fun _ : ℂ => (1 : ℝ))
    (fun n => (gmcOpenApprox U hU n).continuous.aestronglyMeasurable)
    hboundInt hbound hpoint
  have hFint : (∫ x, F x ∂μ) = (μ U).toReal := by
    simp [F, integral_indicator_one hU.measurableSet, measureReal_def]
  simpa [F, hFint] using hDCT

/-! For each finite family of open sets, the joint law of their limiting masses and field
evaluations follows by the distance-cutoff approximation and `IsGMCOf` convergence. -/
include Ω Ω' _inst1 _inst2 P X hX P' X' hX' in
theorem equatorGFF_GMC_open_mass_test_vector_law

    (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (M' : Ω' → Measure ℂ) (hM' : IsGMCOf P' X' γ M')
    {k m : ℕ} (tests : Fin k → TestFn) (U : Fin m → Set ℂ)
    (hU : ∀ j, IsOpen (U j)) :
    Measure.map (fun ω => (fun i => X ω (tests i), fun j => M ω (U j))) P =
      Measure.map (fun ω => (fun i => X' ω (tests i), fun j => M' ω (U j))) P' := by
  classical
  let  := hX.1
  let  := hX'.1
  let I := Fin k ⊕ Fin m
  let cutoffX  := fun n ω =>
    (fun i => X ω (tests i), fun j =>
      ∫ x, gmcOpenApprox (U j) (hU j) n x ∂M ω)
  let cutoffY  := fun n ω =>
    (fun i => X' ω (tests i), fun j =>
      ∫ x, gmcOpenApprox (U j) (hU j) n x ∂M' ω)
  let limitX  := fun ω =>
    (fun i => X ω (tests i), fun j => (M ω (U j)).toReal)
  let limitY  := fun ω =>
    (fun i => X' ω (tests i), fun j => (M' ω (U j)).toReal)
  let pack : ((Fin k → ℝ) × (Fin m → ℝ)) → I → ℝ := fun q i => Sum.elim q.1 q.2 i
  let unpack : (I → ℝ) → (Fin k → ℝ) × (Fin m → ℝ) := fun q =>
    (fun i => q (Sum.inl i), fun j => q (Sum.inr j))
  let FX  := fun n => pack ∘ cutoffX n
  let FY  := fun n => pack ∘ cutoffY n
  let LX  := fun ω => pack (limitX ω)
  let LY  := fun ω => pack (limitY ω)
  have hV : Measurable (fun ω : Ω => fun i => X ω (tests i)) := by
    apply measurable_pi_iff.2
    intro i
    exact (hX.2 (tests i)).1
  have hV' : Measurable (fun ω : Ω' => fun i => X' ω (tests i)) := by
    apply measurable_pi_iff.2
    intro i
    exact (hX'.2 (tests i)).1
  have hpack : Measurable pack := by
    rw [measurable_pi_iff]
    measurability
  have hunpack : Measurable unpack := by
    fun_prop
  have hcutAEX : ∀ n, AEMeasurable (cutoffX n) P := by
    intro n
    refine hV.aemeasurable.prodMk ?_
    apply AEMeasurable.of_eval
    intro j
    exact gmc_test_integral_aemeasurable_of_IsGMCOf P X hX γ M hM
      (gmcOpenApprox (U j) (hU j) n)
  have hcutAEY : ∀ n, AEMeasurable (cutoffY n) P' := by
    intro n
    refine hV'.aemeasurable.prodMk ?_
    apply AEMeasurable.of_eval
    intro j
    exact gmc_test_integral_aemeasurable_of_IsGMCOf P' X' hX' γ M' hM'
      (gmcOpenApprox (U j) (hU j) n)
  have hlimAEX : AEMeasurable limitX P := by
    refine hV.aemeasurable.prodMk ?_
    apply AEMeasurable.of_eval
    intro j
    let f  := fun n ω =>
      ∫ x, gmcOpenApprox (U j) (hU j) n x ∂M ω
    have hf  := fun n =>
      gmc_test_integral_aemeasurable_of_IsGMCOf P X hX γ M hM
        (gmcOpenApprox (U j) (hU j) n)
    have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop
        (𝓝 ((M ω (U j)).toReal)) := by
      filter_upwards [] with ω
      let  := hM.1 ω
      exact gmcOpenApprox_integral_tendsto (M ω) (U j) (hU j)
    exact aemeasurable_of_tendsto_metrizable_ae atTop hf hlim
  have hlimAEY : AEMeasurable limitY P' := by
    refine hV'.aemeasurable.prodMk ?_
    apply AEMeasurable.of_eval
    intro j
    let f  := fun n ω =>
      ∫ x, gmcOpenApprox (U j) (hU j) n x ∂M' ω
    have hf  := fun n =>
      gmc_test_integral_aemeasurable_of_IsGMCOf P' X' hX' γ M' hM'
        (gmcOpenApprox (U j) (hU j) n)
    have hlim : ∀ᵐ ω ∂P', Tendsto (fun n => f n ω) atTop
        (𝓝 ((M' ω (U j)).toReal)) := by
      filter_upwards [] with ω
      let  := hM'.1 ω
      exact gmcOpenApprox_integral_tendsto (M' ω) (U j) (hU j)
    exact aemeasurable_of_tendsto_metrizable_ae atTop hf hlim
  have hFXae  := fun n =>
    hpack.aemeasurable.comp_aemeasurable (hcutAEX n)
  have hFYae  := fun n =>
    hpack.aemeasurable.comp_aemeasurable (hcutAEY n)
  have hLXae  := hpack.aemeasurable.comp_aemeasurable hlimAEX
  have hLYae  := hpack.aemeasurable.comp_aemeasurable hlimAEY
  have hcutLaw : ∀ n, Measure.map (FX n) P = Measure.map (FY n) P' := by
    intro n
    have hbase := equatorGFF_GMC_test_integral_vector_law P X hX P' X' hX' γ M hM M' hM'
      tests (fun j => gmcOpenApprox (U j) (hU j) n)
    have hcompX : pack ∘ cutoffX n = FX n := rfl
    have hcompY : pack ∘ cutoffY n = FY n := rfl
    rw [← hcompX, ← hcompY]
    calc
      Measure.map (pack ∘ cutoffX n) P = (Measure.map (cutoffX n) P).map pack :=
        (AEMeasurable.map_map_of_aemeasurable hpack.aemeasurable (hcutAEX n)).symm
      _ = (Measure.map (cutoffY n) P').map pack := congrArg (Measure.map pack) hbase
      _ = Measure.map (pack ∘ cutoffY n) P' :=
        AEMeasurable.map_map_of_aemeasurable hpack.aemeasurable (hcutAEY n)
  have hcoordX (i : I) : TendstoInMeasure P (fun n ω => FX n ω i) atTop
      (fun ω => LX ω i) := by
    cases i with
    | inl i =>
      rw [tendstoInMeasure_iff_norm]
      intro ε hε
      have he : ∀ n : ℕ, {ω | ε ≤ ‖FX n ω (Sum.inl i) - LX ω (Sum.inl i)‖} = ∅ := by
        intro n
        ext ω
        simp [FX, LX, pack, cutoffX, limitX, not_le_of_gt hε]
      simp_all
    | inr j =>
      have hpt : ∀ᵐ ω ∂P, Tendsto (fun n => FX n ω (Sum.inr j)) atTop
          (𝓝 (LX ω (Sum.inr j))) := by
        filter_upwards [] with ω
        let  := hM.1 ω
        exact gmcOpenApprox_integral_tendsto (M ω) (U j) (hU j)
      exact tendstoInMeasure_of_tendsto_ae
        (fun n => ((hcutAEX n).snd.eval j).aestronglyMeasurable) hpt
  have hcoordY (i : I) : TendstoInMeasure P' (fun n ω => FY n ω i) atTop
      (fun ω => LY ω i) := by
    cases i with
    | inl i =>
      rw [tendstoInMeasure_iff_norm]
      intro ε hε
      have he : ∀ n : ℕ, {ω | ε ≤ ‖FY n ω (Sum.inl i) - LY ω (Sum.inl i)‖} = ∅ := by
        intro n
        ext ω
        simp [FY, LY, pack, cutoffY, limitY, not_le_of_gt hε]
      simp_all
    | inr j =>
      have hpt : ∀ᵐ ω ∂P', Tendsto (fun n => FY n ω (Sum.inr j)) atTop
          (𝓝 (LY ω (Sum.inr j))) := by
        filter_upwards [] with ω
        let  := hM'.1 ω
        exact gmcOpenApprox_integral_tendsto (M' ω) (U j) (hU j)
      exact tendstoInMeasure_of_tendsto_ae
        (fun n => ((hcutAEY n).snd.eval j).aestronglyMeasurable) hpt
  have hvecX  := tendstoInMeasure_pi_finite P FX LX hcoordX
  have hvecY  := tendstoInMeasure_pi_finite P' FY LY hcoordY
  have hlaw  :=
    map_eq_of_seq_map_eq_of_tendstoInMeasure FX FY LX LY hFXae hFYae hLXae hLYae
      hcutLaw hvecX hvecY
  have hpackUnpackX : unpack ∘ LX = limitX := by
    abel
  have hpackUnpackY : unpack ∘ LY = limitY := by
    abel
  have hrealLaw : Measure.map limitX P = Measure.map limitY P' := by
    rw [← hpackUnpackX, ← hpackUnpackY]
    calc
      Measure.map (unpack ∘ LX) P = (Measure.map LX P).map unpack :=
        (AEMeasurable.map_map_of_aemeasurable hunpack.aemeasurable hLXae).symm
      _ = (Measure.map LY P').map unpack := congrArg (Measure.map unpack) hlaw
      _ = Measure.map (unpack ∘ LY) P' :=
        AEMeasurable.map_map_of_aemeasurable hunpack.aemeasurable hLYae
  let toMass : ((Fin k → ℝ) × (Fin m → ℝ)) →
      (Fin k → ℝ) × (Fin m → ℝ≥0∞) := fun q =>
        (q.1, fun j => ENNReal.ofReal (q.2 j))
  have htoMass : Measurable toMass := by fun_prop
  have hmassX : ∀ ω j, ENNReal.ofReal ((M ω (U j)).toReal) = M ω (U j) := by
    intro ω j
    let  := hM.1 ω
    simp_all
  have hmassY : ∀ ω j, ENNReal.ofReal ((M' ω (U j)).toReal) = M' ω (U j) := by
    intro ω j
    let  := hM'.1 ω
    simp_all
  have hfinal : Measure.map (toMass ∘ limitX) P = Measure.map (toMass ∘ limitY) P' := by
    calc
      Measure.map (toMass ∘ limitX) P = (Measure.map limitX P).map toMass :=
        (AEMeasurable.map_map_of_aemeasurable htoMass.aemeasurable hlimAEX).symm
      _ = (Measure.map limitY P').map toMass := congrArg (Measure.map toMass) hrealLaw
      _ = Measure.map (toMass ∘ limitY) P' :=
        AEMeasurable.map_map_of_aemeasurable htoMass.aemeasurable hlimAEY
  calc
    Measure.map (fun ω => (fun i => X ω (tests i), fun j => M ω (U j))) P =
        Measure.map (toMass ∘ limitX) P := by
          congr 1
          grind
    _ = Measure.map (toMass ∘ limitY) P' := hfinal
    _ = Measure.map (fun ω => (fun i => X' ω (tests i), fun j => M' ω (U j))) P' := by
          congr 1
          bound


end DOZZ.Proofs
