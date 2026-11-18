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

/-! Finite joint laws of the field and arbitrary circle-average regularizations. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]


private noncomputable def refFinMeas : FiniteMeasure ℂ :=
  ⟨gmcReferenceMeasure, ⟨lt_top_iff_ne_top.2 gmcReferenceMeasure_univ_ne_top⟩⟩

section
variable (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
include hX

private lemma centeredGaussian_test_circle

    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    {k m : ℕ} (f : Fin k → TestFn) (z : Fin m → ℂ) (r : Fin m → ℝ) :
    IsCenteredJointlyGaussian P
      (fun ω (i : Fin k ⊕ Fin m) => match i with | Sum.inl i => X ω (f i) | Sum.inr j => Xc ω (z j) (r j)) := by
  classical
  let q : Fin k ⊕ Fin m → (ℂ × ℝ) ⊕ TestFn :=
    fun i => match i with | Sum.inl i => Sum.inr (f i) | Sum.inr j => Sum.inl (z j, r j)
  have hproc : IsGaussianProcess
      (fun (i : Fin k ⊕ Fin m) ω => match i with | Sum.inl i => X ω (f i) | Sum.inr j => Xc ω (z j) (r j)) P := by
    have hf : (fun (i : Fin k ⊕ Fin m) ω => match i with | Sum.inl i => X ω (f i) | Sum.inr j => Xc ω (z j) (r j)) =
        (fun t : (ℂ × ℝ) ⊕ TestFn => Sum.elim (fun p ω => Xc ω p.1 p.2) (fun g ω => X ω g) t) ∘ q := by
      ext i ω; cases i <;> rfl
    rw [hf]; exact (circleAverage_tests_isGaussianProcess X Xc hX hXc).comp_right q
  refine centeredJointlyGaussian_of_isGaussianProcess P _ hproc fun i => ?_
  cases i with
  | inl i => exact equatorGFF_test_integral X hX (f i)
  | inr j => exact (circleAverage_isGaussianProcess P X Xc hX hXc).2 (z j) (r j)

private lemma test_cov_eq (g h : TestFn) :
    gaussianCovariance P (fun ω => X ω g) (fun ω => X ω h) = gffCov g h := by
  let _ := hX.1
  rw [gaussianCovariance, ← equatorGFF_test_covariance X hX g h, ProbabilityTheory.covariance,
    equatorGFF_test_integral X hX g, equatorGFF_test_integral X hX h]; simp


private lemma regGMC_test_aemeasurable

    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ r : ℝ)
    (f : BoundedContinuousFunction ℂ ℝ) :
    AEMeasurable (fun ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) P := by
  have := regularizedGMC_measurable P X hX Xc hXc γ r
  have hp : Measurable fun ω =>
      (∫⁻ x, (f.nnrealPart x : ℝ≥0∞) ∂regularizedGMC P Xc γ r ω).toReal -
        (∫⁻ x, ((-f).nnrealPart x : ℝ≥0∞) ∂regularizedGMC P Xc γ r ω).toReal := by fun_prop
  refine hp.aemeasurable.congr ((regularizedGMC_finite_ae P X hX Xc hXc γ r).mono fun ω hω => ?_)
  dsimp only
  rw [BoundedContinuousFunction.integral_eq_integral_nnrealPart_sub (μ := regularizedGMC P Xc γ r ω) f,
    ← BoundedContinuousFunction.toReal_lintegral_coe_eq_integral f.nnrealPart _,
    ← BoundedContinuousFunction.toReal_lintegral_coe_eq_integral (-f).nnrealPart _]

theorem gmc_test_integral_aemeasurable_of_IsGMCOf


    (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (f : BoundedContinuousFunction ℂ ℝ) :
    AEMeasurable (fun ω => ∫ x, f x ∂M ω) P := by
  rcases hM.2 with ⟨Xc, hXc, hconv⟩
  exact (hconv f).aemeasurable fun r => regGMC_test_aemeasurable P X hX Xc hXc γ r f


end
private lemma pack_tendstoInMeasure_coord {μ : Measure Ω}
    {k m : ℕ} (V : Ω → Fin k → ℝ) (F : ℕ → Ω → Fin m → ℝ) (L : Ω → Fin m → ℝ)
    (hc : ∀ j, TendstoInMeasure μ (fun n ω => F n ω j) atTop (fun ω => L ω j)) (i : Fin k ⊕ Fin m) :
    TendstoInMeasure μ (fun n ω => Sum.elim (V ω) (F n ω) i) atTop (fun ω => Sum.elim (V ω) (L ω) i) := by
  cases i with
  | inl i =>
    refine tendstoInMeasure_iff_norm.2 fun ε hε => ?_
    have h0 (n : ℕ) : {ω | ε ≤ ‖Sum.elim (V ω) (F n ω) (Sum.inl i) - Sum.elim (V ω) (L ω) (Sum.inl i)‖} = ∅ := by
      ext ω; simp [not_le_of_gt hε]
    simp_rw [h0, measure_empty]; exact tendsto_const_nhds
  | inr j => exact hc j

private lemma pair_map_eq_of_seq_tendstoInMeasure
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {k m : ℕ} (V : Ω → Fin k → ℝ) (V' : Ω' → Fin k → ℝ)
    (F : ℕ → Ω → Fin m → ℝ) (F' : ℕ → Ω' → Fin m → ℝ)
    (L : Ω → Fin m → ℝ) (L' : Ω' → Fin m → ℝ)
    (hV : Measurable V) (hV' : Measurable V')
    (hF : ∀ n j, AEMeasurable (fun ω => F n ω j) P)
    (hF' : ∀ n j, AEMeasurable (fun ω => F' n ω j) P')
    (hL : ∀ j, AEMeasurable (fun ω => L ω j) P)
    (hL' : ∀ j, AEMeasurable (fun ω => L' ω j) P')
    (hlaw : ∀ n, Measure.map (fun ω => (V ω, F n ω)) P = Measure.map (fun ω => (V' ω, F' n ω)) P')
    (hconv : ∀ j, TendstoInMeasure P (fun n ω => F n ω j) atTop (fun ω => L ω j))
    (hconv' : ∀ j, TendstoInMeasure P' (fun n ω => F' n ω j) atTop (fun ω => L' ω j)) :
    Measure.map (fun ω => (V ω, L ω)) P = Measure.map (fun ω => (V' ω, L' ω)) P' := by
  classical
  let pack : ((Fin k → ℝ) × (Fin m → ℝ)) → Fin k ⊕ Fin m → ℝ := fun q => Sum.elim q.1 q.2
  let unpack : (Fin k ⊕ Fin m → ℝ) → (Fin k → ℝ) × (Fin m → ℝ) :=
    fun q => (fun i => q (Sum.inl i), fun j => q (Sum.inr j))
  have hpack : Measurable pack := measurable_pi_iff.2 fun i => by
    cases i <;> [exact (measurable_pi_apply _).comp measurable_fst; exact (measurable_pi_apply _).comp measurable_snd]
  have hunpack : Measurable unpack := by fun_prop
  have hpX (n : ℕ) : AEMeasurable (fun ω => (V ω, F n ω)) P := hV.aemeasurable.prodMk (AEMeasurable.of_eval (hF n))
  have hpY (n : ℕ) : AEMeasurable (fun ω => (V' ω, F' n ω)) P' := hV'.aemeasurable.prodMk (AEMeasurable.of_eval (hF' n))
  have hlX : AEMeasurable (fun ω => (V ω, L ω)) P := hV.aemeasurable.prodMk (AEMeasurable.of_eval hL)
  have hlY : AEMeasurable (fun ω => (V' ω, L' ω)) P' := hV'.aemeasurable.prodMk (AEMeasurable.of_eval hL')
  have hU := map_eq_of_seq_map_eq_of_tendstoInMeasure
    (fun n => pack ∘ fun ω => (V ω, F n ω)) (fun n => pack ∘ fun ω => (V' ω, F' n ω))
    (pack ∘ fun ω => (V ω, L ω)) (pack ∘ fun ω => (V' ω, L' ω))
    (fun n => hpack.aemeasurable.comp_aemeasurable (hpX n))
    (fun n => hpack.aemeasurable.comp_aemeasurable (hpY n))
    (hpack.aemeasurable.comp_aemeasurable hlX) (hpack.aemeasurable.comp_aemeasurable hlY)
    (fun n => by
      rw [← AEMeasurable.map_map_of_aemeasurable hpack.aemeasurable (hpX n), hlaw n,
        AEMeasurable.map_map_of_aemeasurable hpack.aemeasurable (hpY n)])
    (tendstoInMeasure_pi_finite P _ _ (pack_tendstoInMeasure_coord V F L hconv))
    (tendstoInMeasure_pi_finite P' _ _ (pack_tendstoInMeasure_coord V' F' L' hconv'))
  calc Measure.map (fun ω => (V ω, L ω)) P
    _ = (Measure.map (pack ∘ fun ω => (V ω, L ω)) P).map unpack :=
        (AEMeasurable.map_map_of_aemeasurable hunpack.aemeasurable
          (hpack.aemeasurable.comp_aemeasurable hlX)).symm
    _ = (Measure.map (pack ∘ fun ω => (V' ω, L' ω)) P').map unpack := congrArg (Measure.map unpack) hU
    _ = Measure.map (fun ω => (V' ω, L' ω)) P' :=
        AEMeasurable.map_map_of_aemeasurable hunpack.aemeasurable
          (hpack.aemeasurable.comp_aemeasurable hlY)

private lemma regGMC_wick_ae_model
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    {k m : ℕ} (tests : Fin k → TestFn) (f : Fin m → BoundedContinuousFunction ℂ ℝ)
    (variance : ℂ → ℝ≥0) (hvar_m : Measurable variance)
    (wBCF : Fin (m + m) → BoundedContinuousFunction ℂ ℝ)
    (γ r : ℝ)
    (hsplit : ∀ j x, f j x = wBCF (Fin.castAdd m j) x - wBCF (Fin.natAdd m j) x)
    (hw_nn : ∀ i x, 0 ≤ wBCF i x)
    (hlaw : ∀ x, HasLaw (fun ω => Xc ω x r) (gaussianReal 0 (variance x)) P)
    (hveq : ∀ x, (variance x : ℝ) = gaussianVariance P (fun ω => Xc ω x r)) :
    (fun ω => (fun i => X ω (tests i), fun j => ∫ x, f j x ∂regularizedGMC P Xc γ r ω)) =ᵐ[P]
      fun ω => (fun i => X ω (tests i),
        fun j => (∫ x, wBCF (Fin.castAdd m j) x * Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * (variance x : ℝ)) ∂(refFinMeas : Measure ℂ)) -
          ∫ x, wBCF (Fin.natAdd m j) x * Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * (variance x : ℝ)) ∂(refFinMeas : Measure ℂ)) := by
  have regGMC_wick_eq (f : BoundedContinuousFunction ℂ ℝ) (ω : Ω) : (∫ x, f x ∂regularizedGMC P Xc γ r ω) =
        ∫ x, f x * Real.exp (γ * Xc ω x r - γ ^ 2 / 2 *
          gaussianVariance P (fun ω' => Xc ω' x r)) ∂gmcReferenceMeasure := by
    let V : ℂ → ℝ := fun x => ∫ ω', Xc ω' x r ^ 2 ∂P
    let D : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * V x) * normPlus x ^ (-4 : ℝ))
    let G : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (normPlus x ^ (-4 : ℝ))
    have : Measurable V := by
      convert @circleAverage_variance_measurable Ω _ P hX.1 Xc hXc.1 r using 1
      ext x; simp [V, gaussianVariance, gaussianCovariance, pow_two]
    have : Measurable fun x : ℂ => Xc ω x r := (hXc.1 r).comp (measurable_const.prodMk measurable_id)
    have : Measurable normPlus := measurable_const.max measurable_norm
    have hD : Measurable D := by fun_prop
    have hG : Measurable G := by fun_prop
    rw [regularizedGMC, show (fun x => ENNReal.ofReal (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 *
        ∫ ω', Xc ω' x r ^ 2 ∂P) * normPlus x ^ (-4 : ℝ))) = D from rfl,
      integral_withDensity_eq_integral_toReal_smul hD (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
      gmcReferenceMeasure, show (fun x => ENNReal.ofReal (normPlus x ^ (-4 : ℝ))) = G from rfl,
      integral_withDensity_eq_integral_toReal_smul hG (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only [D, G, V, smul_eq_mul]
    have hnp : 0 ≤ normPlus x ^ (-4 : ℝ) :=
      (Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (le_max_left _ _)) _).le
    rw [ENNReal.toReal_ofReal (mul_nonneg (Real.exp_nonneg _) hnp), ENNReal.toReal_ofReal hnp]
    simp only [gaussianVariance, gaussianCovariance, pow_two]; ring
  have hint_norm (i : Fin (m + m)) : Integrable (fun x => wBCF i x) (refFinMeas.normalize : Measure ℂ) :=
    (integrable_const ‖wBCF i‖).mono' (wBCF i).continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => (wBCF i).norm_coe_le_norm x)
  have hwi (i : Fin (m + m)) : ∀ᵐ ω ∂P, Integrable (fun x => wBCF i x *
      Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * (variance x : ℝ))) (refFinMeas : Measure ℂ) :=
    (ae_integrable_weighted_wick_sections (refFinMeas.normalize : Measure ℂ) (fun ω x => Xc ω x r) variance
      (fun x => wBCF i x) γ (hXc.1 r) hvar_m (wBCF i).continuous.measurable hlaw (hw_nn i) (hint_norm i)).mono
      fun ω hω => by
        rw [congrArg (fun μ : FiniteMeasure ℂ => (μ : Measure ℂ)) refFinMeas.self_eq_mass_smul_normalize]
        exact hω.smul_measure_nnreal
  filter_upwards [ae_all_iff.2 hwi] with ω hω
  refine Prod.ext rfl (funext fun j => ?_)
  dsimp only
  rw [regGMC_wick_eq (f j) ω]
  have hpt (x : ℂ) : f j x * Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * gaussianVariance P (fun ω' => Xc ω' x r)) =
      wBCF (Fin.castAdd m j) x * Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * (variance x : ℝ)) -
        wBCF (Fin.natAdd m j) x * Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * (variance x : ℝ)) := by
    rw [← hveq x, hsplit j x, sub_mul]
  simp_rw [hpt]
  exact integral_sub (hω _) (hω _)

private lemma equatorGFF_GMC_test_integral_vector_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (P' : Measure Ω') (X' : Ω' → Distr) (hX' : IsEquatorGFF P' X')
    (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (M' : Ω' → Measure ℂ) (hM' : IsGMCOf P' X' γ M')
    {k m : ℕ} (tests : Fin k → TestFn) (f : Fin m → BoundedContinuousFunction ℂ ℝ) :
    Measure.map (fun ω => (fun i => X ω (tests i), fun j => ∫ x, f j x ∂M ω)) P =
      Measure.map (fun ω => (fun i => X' ω (tests i), fun j => ∫ x, f j x ∂M' ω)) P' := by
  classical
  let _ := hX.1; let _ := hX'.1
  rcases hM.2 with ⟨Xc, hXc, hconvX⟩
  rcases hM'.2 with ⟨Xc', hXc', hconvY⟩
  have hV : Measurable fun ω : Ω => fun i => X ω (tests i) := measurable_pi_iff.2 fun i => (hX.2 (tests i)).1
  have hV' : Measurable fun ω : Ω' => fun i => X' ω (tests i) := measurable_pi_iff.2 fun i => (hX'.2 (tests i)).1
  refine pair_map_eq_of_seq_tendstoInMeasure _ _
    (fun n ω j => ∫ x, f j x ∂regularizedGMC P Xc γ (n : ℝ) ω)
    (fun n ω j => ∫ x, f j x ∂regularizedGMC P' Xc' γ (n : ℝ) ω)
    (fun ω j => ∫ x, f j x ∂M ω) (fun ω j => ∫ x, f j x ∂M' ω)
    hV hV'
    (fun n j => regGMC_test_aemeasurable P X hX Xc hXc γ n (f j))
    (fun n j => regGMC_test_aemeasurable P' X' hX' Xc' hXc' γ n (f j))
    (fun j => gmc_test_integral_aemeasurable_of_IsGMCOf P X hX γ M ⟨hM.1, ⟨Xc, hXc, hconvX⟩⟩ (f j))
    (fun j => gmc_test_integral_aemeasurable_of_IsGMCOf P' X' hX' γ M' ⟨hM'.1, ⟨Xc', hXc', hconvY⟩⟩ (f j))
    (fun n => ?_)
    (fun j => (hconvX (f j)).comp tendsto_natCast_atTop_atTop)
    (fun j => (hconvY (f j)).comp tendsto_natCast_atTop_atTop)
  let variance : ℂ → ℝ≥0 := fun x => (gaussianVariance P (fun ω => Xc ω x n)).toNNReal
  let wBCF : Fin (m + m) → BoundedContinuousFunction ℂ ℝ :=
    fun i => max (Fin.addCases f (fun j => -f j) i) 0
  let A : ((Fin k → ℝ) × (Fin (m + m) → ℝ)) → (Fin k → ℝ) × (Fin m → ℝ) :=
    fun p => (p.1, fun j => p.2 (Fin.castAdd m j) - p.2 (Fin.natAdd m j))
  have hvar_m : Measurable variance := measurable_real_toNNReal.comp
    (@circleAverage_variance_measurable Ω _ P hX.1 Xc hXc.1 n)
  have hvar_eq (x : ℂ) : gaussianVariance P (fun ω => Xc ω x n) = gaussianVariance P' (fun ω => Xc' ω x n) := by
    simpa [gaussianVariance] using (isCircleAverage_covariance P X hX Xc hXc x x n n).trans
      (isCircleAverage_covariance P' X' hX' Xc' hXc' x x n n).symm
  have hvar_r (x : ℂ) : (variance x : ℝ) = gaussianVariance P (fun ω => Xc ω x n) :=
    Real.coe_toNNReal _ (circleAverage_gaussian_law_and_variance_nonneg P X hX Xc hXc x n).2
  have hw_nn (i : Fin (m + m)) (x : ℂ) : 0 ≤ wBCF i x := le_max_right _ _
  have hw_bdd (i : Fin (m + m)) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, wBCF i x ≤ C :=
    ⟨‖wBCF i‖, norm_nonneg _, fun x => (le_abs_self _).trans (by simpa using (wBCF i).norm_coe_le_norm x)⟩
  have hFDD (s : ℕ) (xs : Fin s → ℂ) :
      Measure.map (fun ω => (fun i => X ω (tests i), fun i => Xc ω (xs i) n)) P =
        Measure.map (fun ω => (fun i => X' ω (tests i), fun i => Xc' ω (xs i) n)) P' := by
    have hUX := centeredGaussian_test_circle P X hX Xc hXc tests xs (fun _ => n)
    have hUY := centeredGaussian_test_circle P' X' hX' Xc' hXc' tests xs (fun _ => n)
    have hcov (a b : Fin k ⊕ Fin s) :
        gaussianCovariance P (fun ω => match a with | Sum.inl i => X ω (tests i) | Sum.inr j => Xc ω (xs j) n)
          (fun ω => match b with | Sum.inl i => X ω (tests i) | Sum.inr j => Xc ω (xs j) n) =
        gaussianCovariance P' (fun ω => match a with | Sum.inl i => X' ω (tests i) | Sum.inr j => Xc' ω (xs j) n)
          (fun ω => match b with | Sum.inl i => X' ω (tests i) | Sum.inr j => Xc' ω (xs j) n) := by
      cases a <;> cases b <;> dsimp only
      · rw [test_cov_eq P X hX, test_cov_eq P' X' hX']
      · rw [isCircleAverage_cross_covariance P X hX Xc hXc, isCircleAverage_cross_covariance P' X' hX' Xc' hXc']
      · rw [show gaussianCovariance P _ _ = gaussianCovariance P (fun ω => X ω (tests _)) _ from
            integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _),
          show gaussianCovariance P' _ _ = gaussianCovariance P' (fun ω => X' ω (tests _)) _ from
            integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _),
          isCircleAverage_cross_covariance P X hX Xc hXc, isCircleAverage_cross_covariance P' X' hX' Xc' hXc']
      · rw [isCircleAverage_covariance P X hX Xc hXc, isCircleAverage_covariance P' X' hX' Xc' hXc']
    have hUlaw := map_eq_of_centeredJointlyGaussian_of_covariance_eq P P' _ _ hUX hUY hcov
    let π : (Fin k ⊕ Fin s → ℝ) → (Fin k → ℝ) × (Fin s → ℝ) :=
      fun w => (fun i => w (Sum.inl i), fun j => w (Sum.inr j))
    have hπ : Measurable π := by fun_prop
    change Measure.map (π ∘ fun ω i => match i with | Sum.inl i => X ω (tests i) | Sum.inr j => Xc ω (xs j) n) P =
      Measure.map (π ∘ fun ω i => match i with | Sum.inl i => X' ω (tests i) | Sum.inr j => Xc' ω (xs j) n) P'
    rw [← AEMeasurable.map_map_of_aemeasurable hπ.aemeasurable (AEMeasurable.of_eval hUX.2.1), hUlaw,
      AEMeasurable.map_map_of_aemeasurable hπ.aemeasurable (AEMeasurable.of_eval hUY.2.1)]
  let LX : Ω → (Fin k → ℝ) × (Fin (m + m) → ℝ) := fun ω =>
    (fun i => X ω (tests i), fun i => ∫ x, wBCF i x * Real.exp (γ * Xc ω x n - γ ^ 2 / 2 * (variance x : ℝ)) ∂(refFinMeas : Measure ℂ))
  let LY : Ω' → (Fin k → ℝ) × (Fin (m + m) → ℝ) := fun ω =>
    (fun i => X' ω (tests i), fun i => ∫ x, wBCF i x * Real.exp (γ * Xc' ω x n - γ ^ 2 / 2 * (variance x : ℝ)) ∂(refFinMeas : Measure ℂ))
  have hLXm : Measurable LX := hV.prodMk (measurable_pi_iff.2 fun i =>
    (by have := hXc.1 n; fun_prop : Measurable fun p : Ω × ℂ =>
      wBCF i p.2 * Real.exp (γ * Xc p.1 p.2 n - γ ^ 2 / 2 * (variance p.2 : ℝ))).stronglyMeasurable.integral_prod_right'.measurable)
  have hLYm : Measurable LY := hV'.prodMk (measurable_pi_iff.2 fun i =>
    (by have := hXc'.1 n; fun_prop : Measurable fun p : Ω' × ℂ =>
      wBCF i p.2 * Real.exp (γ * Xc' p.1 p.2 n - γ ^ 2 / 2 * (variance p.2 : ℝ))).stronglyMeasurable.integral_prod_right'.measurable)
  have hXlaw (x : ℂ) : HasLaw (fun ω => Xc ω x n) (gaussianReal 0 (variance x)) P := by
    simpa [variance] using (circleAverage_gaussian_law_and_variance_nonneg P X hX Xc hXc x n).1
  have hYlaw (x : ℂ) : HasLaw (fun ω => Xc' ω x n) (gaussianReal 0 (variance x)) P' := by
    have hv : (gaussianVariance P' (fun ω => Xc' ω x n)).toNNReal = variance x := by dsimp [variance]; rw [hvar_eq]
    simpa [hv] using (circleAverage_gaussian_law_and_variance_nonneg P' X' hX' Xc' hXc' x n).1
  have hLaw : Measure.map LX P = Measure.map LY P' :=
    ext_of_forall_integral_eq_of_IsFiniteMeasure fun φ => by
      rw [integral_map hLXm.aemeasurable φ.continuous.measurable.aestronglyMeasurable,
        chaosLawFDD_boundedWeights refFinMeas (fun ω x => Xc ω x n) (fun ω x => Xc' ω x n) _ _
          variance (fun i x => wBCF i x) γ hV hV' (hXc.1 n) (hXc'.1 n) hvar_m (fun i => (wBCF i).continuous.measurable)
          hw_nn hw_bdd hXlaw hYlaw hFDD φ,
        ← integral_map hLYm.aemeasurable φ.continuous.measurable.aestronglyMeasurable]
  have hsplit (j : Fin m) (x : ℂ) : f j x = wBCF (Fin.castAdd m j) x - wBCF (Fin.natAdd m j) x := by
    simp only [wBCF, Fin.addCases_left, Fin.addCases_right]
    change f j x = max (f j x) 0 - max (-f j x) 0
    by_cases hx : 0 ≤ f j x <;> [simp [hx]; simp [(lt_of_not_ge hx).le]]
  have hA : Measurable A := by fun_prop
  rw [Measure.map_congr (regGMC_wick_ae_model P X hX Xc hXc tests f variance hvar_m wBCF γ n hsplit hw_nn hXlaw hvar_r),
    Measure.map_congr (regGMC_wick_ae_model P' X' hX' Xc' hXc' tests f variance hvar_m wBCF γ n hsplit hw_nn hYlaw
      fun x => (hvar_r x).trans (hvar_eq x))]
  change Measure.map (A ∘ LX) P = Measure.map (A ∘ LY) P'
  rw [← Measure.map_map hA hLXm, hLaw, Measure.map_map hA hLYm]

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

theorem gmcOpenApprox_integral_tendsto
    (μ : Measure ℂ) [IsFiniteMeasure μ] (U : Set ℂ) (hU : IsOpen U) :
    Tendsto (fun n => ∫ x, gmcOpenApprox U hU n x ∂μ) atTop (𝓝 ((μ U).toReal)) := by
  classical
  have hb (n : ℕ) (x : ℂ) : 0 ≤ gmcOpenApprox U hU n x ∧ gmcOpenApprox U hU n x ≤ 1 := by
    by_cases h : U = Set.univ
    · simp [gmcOpenApprox, h]
    · simp only [gmcOpenApprox, h]
      exact ⟨le_min zero_le_one (mul_nonneg (Nat.cast_nonneg n) Metric.infDist_nonneg), min_le_left _ _⟩
  have hpt (x : ℂ) : Tendsto (fun n => gmcOpenApprox U hU n x) atTop (𝓝 (U.indicator 1 x)) := by
    by_cases h : U = Set.univ
    · simp [gmcOpenApprox, h]
    · have hc : Uᶜ.Nonempty := Set.nonempty_compl.2 h
      by_cases hx : x ∈ U
      · have hd : 0 < Metric.infDist x Uᶜ := (hU.isClosed_compl.notMem_iff_infDist_pos hc).1 (by simpa using hx)
        obtain ⟨N, hN⟩ := exists_nat_gt (Metric.infDist x Uᶜ)⁻¹
        rw [Set.indicator_of_mem hx, Pi.one_apply]
        refine tendsto_nhds_of_eventually_eq (eventually_ge_atTop N |>.mono fun n hn => ?_)
        have hm : 1 ≤ (n : ℝ) * Metric.infDist x Uᶜ := by
          have := mul_lt_mul_of_pos_right (hN.trans_le (Nat.cast_le.2 hn)) hd
          rw [inv_mul_cancel₀ hd.ne'] at this
          exact this.le
        simp [gmcOpenApprox, h, min_eq_left hm]
      · rw [Set.indicator_of_notMem hx]
        exact tendsto_nhds_of_eventually_eq (Eventually.of_forall fun n => by
          simp [gmcOpenApprox, h, Metric.infDist_zero_of_mem (show x ∈ Uᶜ from hx)])
  simpa [integral_indicator_one hU.measurableSet, measureReal_def] using
    tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun n => (gmcOpenApprox U hU n).continuous.aestronglyMeasurable) (integrable_const 1)
      (fun n => Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hb n x).1]; exact (hb n x).2)
      (Eventually.of_forall hpt)

private lemma open_mass_toReal_aemeasurable
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) {U : Set ℂ} (hU : IsOpen U) :
    AEMeasurable (fun ω => (M ω U).toReal) P :=
  aemeasurable_of_tendsto_metrizable_ae atTop
    (fun n => gmc_test_integral_aemeasurable_of_IsGMCOf P X hX γ M hM (gmcOpenApprox U hU n))
    (Eventually.of_forall fun ω => @gmcOpenApprox_integral_tendsto (M ω) (hM.1 ω) U hU)

theorem equatorGFF_GMC_open_mass_test_vector_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (P' : Measure Ω') (X' : Ω' → Distr) (hX' : IsEquatorGFF P' X')
    (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (M' : Ω' → Measure ℂ) (hM' : IsGMCOf P' X' γ M')
    {k m : ℕ} (tests : Fin k → TestFn) (U : Fin m → Set ℂ) (hU : ∀ j, IsOpen (U j)) :
    Measure.map (fun ω => (fun i => X ω (tests i), fun j => M ω (U j))) P =
      Measure.map (fun ω => (fun i => X' ω (tests i), fun j => M' ω (U j))) P' := by
  let _ := hX.1; let _ := hX'.1
  have hrealLaw := pair_map_eq_of_seq_tendstoInMeasure
    (fun ω i => X ω (tests i)) (fun ω i => X' ω (tests i))
    (fun n ω j => ∫ x, gmcOpenApprox (U j) (hU j) n x ∂M ω)
    (fun n ω j => ∫ x, gmcOpenApprox (U j) (hU j) n x ∂M' ω)
    (fun ω j => (M ω (U j)).toReal) (fun ω j => (M' ω (U j)).toReal)
    (measurable_pi_iff.2 fun i => (hX.2 (tests i)).1)
    (measurable_pi_iff.2 fun i => (hX'.2 (tests i)).1)
    (fun n j => gmc_test_integral_aemeasurable_of_IsGMCOf P X hX γ M hM (gmcOpenApprox (U j) (hU j) n))
    (fun n j => gmc_test_integral_aemeasurable_of_IsGMCOf P' X' hX' γ M' hM' (gmcOpenApprox (U j) (hU j) n))
    (fun j => open_mass_toReal_aemeasurable P X hX γ M hM (hU j))
    (fun j => open_mass_toReal_aemeasurable P' X' hX' γ M' hM' (hU j))
    (fun n => equatorGFF_GMC_test_integral_vector_law P X hX P' X' hX' γ M hM M' hM'
      tests fun j => gmcOpenApprox (U j) (hU j) n)
    (fun j => tendstoInMeasure_of_tendsto_ae
      (fun n => (gmc_test_integral_aemeasurable_of_IsGMCOf P X hX γ M hM (gmcOpenApprox (U j) (hU j) n)).aestronglyMeasurable)
      (Eventually.of_forall fun ω => @gmcOpenApprox_integral_tendsto (M ω) (hM.1 ω) (U j) (hU j)))
    (fun j => tendstoInMeasure_of_tendsto_ae
      (fun n => (gmc_test_integral_aemeasurable_of_IsGMCOf P' X' hX' γ M' hM' (gmcOpenApprox (U j) (hU j) n)).aestronglyMeasurable)
      (Eventually.of_forall fun ω => @gmcOpenApprox_integral_tendsto (M' ω) (hM'.1 ω) (U j) (hU j)))
  let toMass : ((Fin k → ℝ) × (Fin m → ℝ)) → (Fin k → ℝ) × (Fin m → ℝ≥0∞) :=
    fun q => (q.1, fun j => ENNReal.ofReal (q.2 j))
  have htoMass : Measurable toMass := by fun_prop
  have hlX : AEMeasurable (fun ω => (fun i => X ω (tests i), fun j => (M ω (U j)).toReal)) P :=
    (measurable_pi_iff.2 fun i => (hX.2 (tests i)).1).aemeasurable.prodMk
      (AEMeasurable.of_eval fun j => open_mass_toReal_aemeasurable P X hX γ M hM (hU j))
  have hlY : AEMeasurable (fun ω => (fun i => X' ω (tests i), fun j => (M' ω (U j)).toReal)) P' :=
    (measurable_pi_iff.2 fun i => (hX'.2 (tests i)).1).aemeasurable.prodMk
      (AEMeasurable.of_eval fun j => open_mass_toReal_aemeasurable P' X' hX' γ M' hM' (hU j))
  have hXeq : (fun ω => (fun i => X ω (tests i), fun j => M ω (U j))) =
      toMass ∘ fun ω => (fun i => X ω (tests i), fun j => (M ω (U j)).toReal) := by
    ext ω : 1; refine Prod.ext rfl (funext fun j => ?_)
    let _ := hM.1 ω; exact (ENNReal.ofReal_toReal (measure_ne_top (M ω) (U j))).symm
  have hYeq : (fun ω => (fun i => X' ω (tests i), fun j => M' ω (U j))) =
      toMass ∘ fun ω => (fun i => X' ω (tests i), fun j => (M' ω (U j)).toReal) := by
    ext ω : 1; refine Prod.ext rfl (funext fun j => ?_)
    let _ := hM'.1 ω; exact (ENNReal.ofReal_toReal (measure_ne_top (M' ω) (U j))).symm
  rw [hXeq, hYeq, ← AEMeasurable.map_map_of_aemeasurable htoMass.aemeasurable hlX, hrealLaw,
    AEMeasurable.map_map_of_aemeasurable htoMass.aemeasurable hlY]

end DOZZ.Proofs
