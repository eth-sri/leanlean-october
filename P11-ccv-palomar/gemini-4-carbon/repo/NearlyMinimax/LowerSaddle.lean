module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Data.Finset.Powerset
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.Probability.Kernel.MeasurableIntegral
public import NearlyMinimax.BoundedHyperplaneField
public import NearlyMinimax.Chebyshev
public import NearlyMinimax.DesignCounts
public import NearlyMinimax.FinePairScoreBounds
public import NearlyMinimax.PathRisk
public import NearlyMinimax.Rates
public import NearlyMinimax.Risk
public import NearlyMinimax.SaddleAsymptotics
public import NearlyMinimax.TernaryMeasure

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Function
open scoped BigOperators ENNReal Topology
namespace NearlyMinimax

-- ============================================================================
-- 1. Path Risk, Clipping, Mixture Risk, Frame Bounds, and Marginal Likelihood
-- ============================================================================

section RiskAndLikelihood
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

theorem probability_absolutelyContinuous_score_path_risk_lower_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : ℝ → Measure Ω) (T : Ω → ℝ) (R : ℝ → Ω → ℝ) (V : ℝ → ℝ)
    (δ r risk D ε : ℝ) (hδ : 0 ≤ δ) (hr : 0 ≤ r)
    (hprob : ∀ t ∈ Icc 0 δ, IsProbabilityMeasure (P t))
    (hT : ∀ t ∈ Icc 0 δ, MemLp T 2 (P t))
    (hR : ∀ᵐ t ∂volume, t ∈ Icc 0 δ → MemLp (R t) 2 (P t))
    (hcenter : ∀ᵐ t ∂volume, t ∈ Icc 0 δ → (∫ x, R t x ∂P t) = 0)
    (hAC : AbsolutelyContinuousOnInterval (fun t => ∫ x, T x ∂P t) 0 δ)
    (hderiv : ∀ᵐ t ∂volume, t ∈ Icc 0 δ →
      HasDerivAt (fun u => ∫ x, T x ∂P u) (∫ x, T x * R t x ∂P t) t)
    (hrisk : ∀ t ∈ Icc 0 δ, (∫ x, (T x - V t) ^ 2 ∂P t) ≤ r ^ 2)
    (hscoreInt : IntervalIntegrable
      (fun t => Real.sqrt (∫ x, (R t x) ^ 2 ∂P t)) volume 0 δ)
    (hriskEq : r ^ 2 = risk + D ^ 2 * ε) :
    (V δ - V 0) ^ 2 /
      (2 + ∫ t in (0 : ℝ)..δ, Real.sqrt (∫ x, (R t x) ^ 2 ∂P t)) ^ 2
      - D ^ 2 * ε ≤ risk := by
  let m (t : ℝ) := ∫ x, T x ∂P t
  let score (t : ℝ) := Real.sqrt (∫ x, (R t x) ^ 2 ∂P t)
  have hchange : |m δ - m 0| ≤ r * ∫ t in (0 : ℝ)..δ, score t := by
    rw [← hAC.integral_deriv_eq_sub, ← intervalIntegral.integral_const_mul]
    refine (show ‖∫ t in (0 : ℝ)..δ, deriv m t‖ ≤ _ from
      intervalIntegral.norm_integral_le_of_norm_le hδ ?_ (hscoreInt.const_mul r))
    filter_upwards [hR, hcenter, hderiv] with t hRt hct hdt hmem
    have ht : t ∈ Icc 0 δ := ⟨hmem.1.le, hmem.2⟩
    let _ := hprob t ht
    rw [(hdt ht).deriv]
    exact probability_score_bound (P t) T (R t) (V t) r (hT t ht) (hRt ht) hr (hct ht) (hrisk t ht)
  have hfirst : |m 0 - V 0| ≤ r := by
    let _ := hprob 0 ⟨le_rfl, hδ⟩
    exact probability_mean_error_le (P 0) T (V 0) r (hT 0 ⟨le_rfl, hδ⟩) hr (hrisk 0 ⟨le_rfl, hδ⟩)
  have hlast : |m δ - V δ| ≤ r := by
    let _ := hprob δ ⟨hδ, le_rfl⟩
    exact probability_mean_error_le (P δ) T (V δ) r (hT δ ⟨hδ, le_rfl⟩) hr (hrisk δ ⟨hδ, le_rfl⟩)
  have hsep : |V δ - V 0| ≤ (2 + ∫ t in (0 : ℝ)..δ, score t) * r :=
    calc
      |V δ - V 0| = |(V δ - m δ) + (m δ - m 0) + (m 0 - V 0)| := by congr 1; ring
      _ ≤ |V δ - m δ| + |m δ - m 0| + |m 0 - V 0| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ r + (r * ∫ t in (0 : ℝ)..δ, score t) + r := by
        rw [abs_sub_comm (V δ) (m δ)]; exact add_le_add (add_le_add hlast hchange) hfirst
      _ = _ := by ring
  simpa only [sq_abs] using
    path_risk_lower_bound (intervalIntegral.integral_nonneg_of_forall hδ fun _ => Real.sqrt_nonneg _)
      hr (abs_nonneg (V δ - V 0)) hsep hriskEq

def effectiveVarianceUpper {d : ℕ} (C : ModelConstants d) : ℝ :=
  min C.varianceUpper (Real.sqrt C.fourthBound)

abbrev BoundedEstimator {d : ℕ} (C : ModelConstants d) (n : ℕ) :=
  {T : Estimator d n // ∀ z, T.val z ∈ Icc C.varianceLower (effectiveVarianceUpper C)}

theorem minimaxRisk_eq_inf_bounded {d : ℕ} (C : ModelConstants d) (n : ℕ) :
    minimaxRisk C n = ⨅ T : BoundedEstimator C n, worstCaseRisk C T.val := by
  refine le_antisymm (le_iInf fun T => minimaxRisk_le_worstCaseRisk C T.val) (le_iInf fun T => ?_)
  let Tc : Estimator d n := ⟨fun z => clip C.varianceLower (effectiveVarianceUpper C) (T.val z),
    (clip_lipschitz _ _).continuous.measurable.comp T.property⟩
  refine (iInf_le (fun B : BoundedEstimator C n => worstCaseRisk C B.val)
    ⟨Tc, fun _ => clip_mem_Icc (effective_variance_interval_nondegenerate C).le⟩).trans
    (iSup_le fun θ => (?_ : meanSquaredRisk Tc θ.val ≤ meanSquaredRisk T θ.val).trans
      (le_iSup (fun θ : {θ // Admissible C θ} => meanSquaredRisk T θ.val) θ))
  have hV := admissible_variance_effective_interval C θ.val θ.property
  refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
  have h := clip_error_le hV.1 hV.2 (x := T.val z)
  change |Tc.val z - θ.val.variance| ≤ |T.val z - θ.val.variance| at h
  change (Tc.val z - θ.val.variance) ^ 2 ≤ _
  nlinarith [sq_abs (Tc.val z - θ.val.variance), sq_abs (T.val z - θ.val.variance),
    abs_nonneg (T.val z - θ.val.variance), abs_nonneg (Tc.val z - θ.val.variance)]

theorem boundedEstimator_memLp {d n : ℕ} (C : ModelConstants d)
    (T : BoundedEstimator C n) (μ : Measure (Fin n → Observation d))
    [IsFiniteMeasure μ] (p : ℝ≥0∞) : MemLp T.val.val p μ := by
  apply MemLp.of_bound T.val.property.aestronglyMeasurable (effectiveVarianceUpper C)
  exact Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (C.varianceLower_pos.le.trans (T.property z).1)]
    exact (T.property z).2

theorem probability_kernel_integral {Α Ω : Type*} [MeasurableSpace Α] [MeasurableSpace Ω]
    (μ : Measure Α) [IsProbabilityMeasure μ] (K : Kernel Α Ω) [IsMarkovKernel K]
    (f : Ω → ℝ) (hf : Integrable f (K ∘ₘ μ)) :
    (∫ x, f x ∂(K ∘ₘ μ)) = ∫ a, ∫ x, f x ∂K a ∂μ := by
  simpa only [Kernel.const_apply, ← Measure.comp_eq_comp_const_apply] using
    Kernel.integral_comp (κ := Kernel.const Unit μ) (η := K) (a := ()) (f := f)
      (by simpa only [← Measure.comp_eq_comp_const_apply] using hf)

theorem boundedEstimator_worstCaseRisk_finite {d n : ℕ} (C : ModelConstants d)
    (T : BoundedEstimator C n) : worstCaseRisk C T.val < ∞ := by
  refine (iSup_le fun θ => ?_ : worstCaseRisk C T.val ≤
      ENNReal.ofReal ((effectiveVarianceUpper C - C.varianceLower) ^ 2)).trans_lt ENNReal.ofReal_lt_top
  let _ := sampleLaw_isProbability C θ.val θ.property n
  have hV := admissible_variance_effective_interval C θ.val θ.property
  change θ.val.variance ∈ Icc C.varianceLower (effectiveVarianceUpper C) at hV
  refine (lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_ :
    meanSquaredRisk T.val θ.val ≤ ∫⁻ _, ENNReal.ofReal ((effectiveVarianceUpper C - C.varianceLower) ^ 2) ∂sampleLaw θ.val n).trans_eq (by simp)
  have hT := T.property z
  have habs : |T.val.val z - θ.val.variance| ≤ effectiveVarianceUpper C - C.varianceLower :=
    abs_le.mpr ⟨by linarith [hV.1, hV.2, hT.1, hT.2], by linarith [hV.1, hV.2, hT.1, hT.2]⟩
  nlinarith [sq_abs (T.val.val z - θ.val.variance), abs_nonneg (T.val.val z - θ.val.variance)]

theorem boundedEstimator_mixture_risk_le_of_exceptional_set {Α : Type*} [MeasurableSpace Α]
    {d n : ℕ} (C : ModelConstants d) (T : BoundedEstimator C n)
    (σ : Measure Α) [IsProbabilityMeasure σ]
    (L : Kernel Α (Fin n → Observation d)) [IsMarkovKernel L]
    (θ : Α → RegressionParameter d) (V ε : ℝ)
    (hL : ∀ a, L a = sampleLaw (θ a) n) (hVθ : ∀ a, (θ a).variance = V)
    (hV : V ∈ Icc C.varianceLower (effectiveVarianceUpper C))
    (bad : Set Α) (hbad : MeasurableSet bad)
    (hlegal : ∀ a ∉ bad, Admissible C (θ a))
    (hmass : σ.real bad ≤ ε) :
    (∫ x, (T.val.val x - V) ^ 2 ∂(L ∘ₘ σ)) ≤
      (worstCaseRisk C T.val).toReal + (effectiveVarianceUpper C - C.varianceLower) ^ 2 * ε := by
  let D := effectiveVarianceUpper C - C.varianceLower
  let f (x : Fin n → Observation d) := (T.val.val x - V) ^ 2
  have hfmeas : Measurable f := (T.val.property.sub_const V).pow_const (2 : ℕ)
  have hf0 (x : Fin n → Observation d) : 0 ≤ f x := sq_nonneg _
  have hcap (x : Fin n → Observation d) : f x ≤ D ^ 2 := by
    have ht := T.property x
    have hh : |T.val.val x - V| ≤ D := abs_le.mpr
      ⟨by dsimp only [D]; linarith only [ht.1, ht.2, hV.1, hV.2],
       by dsimp only [D]; linarith only [ht.1, ht.2, hV.1, hV.2]⟩
    simpa only [f, D, effectiveVarianceUpper, sq_abs] using
      (sq_le_sq₀ (abs_nonneg _) (sub_nonneg.mpr (effective_variance_interval_nondegenerate C).le)).mpr hh
  have hfi (μ : Measure (Fin n → Observation d)) [IsProbabilityMeasure μ] : Integrable f μ :=
    (integrable_const (D ^ 2)).mono' hfmeas.aestronglyMeasurable <| Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]; exact hcap x
  let e (a : Α) := ∫ x, f x ∂L a
  have he0 (a : Α) : 0 ≤ e a := integral_nonneg hf0
  have hecap (a : Α) : e a ≤ D ^ 2 := by
    simpa only [integral_const, probReal_univ, one_smul] using integral_mono (hfi (L a)) (integrable_const (D ^ 2)) hcap
  have hei : Integrable e σ :=
    (integrable_const (D ^ 2)).mono' hfmeas.stronglyMeasurable.integral_kernel.measurable.aestronglyMeasurable <|
      Filter.Eventually.of_forall fun a => by rw [Real.norm_eq_abs, abs_of_nonneg (he0 a)]; exact hecap a
  have hgood (a : Α) (ha : Admissible C (θ a)) : e a ≤ (worstCaseRisk C T.val).toReal := by
    have heq : ENNReal.ofReal (e a) = meanSquaredRisk T.val (θ a) := by
      rw [meanSquaredRisk, ← hL a, hVθ a]
      exact ofReal_integral_eq_lintegral_ofReal (hfi (L a)) (Filter.Eventually.of_forall hf0)
    have h := ENNReal.toReal_mono (boundedEstimator_worstCaseRisk_finite C T).ne
      (meanSquaredRisk_le_worstCaseRisk C T.val (θ a) ha)
    rwa [← heq, ENNReal.toReal_ofReal (he0 a)] at h
  rw [probability_kernel_integral σ L f (hfi (L ∘ₘ σ))]
  exact probability_mixture_exceptional_risk_bound σ e bad hbad
    (worstCaseRisk C T.val).toReal D ε hei ENNReal.toReal_nonneg
    (Filter.Eventually.of_forall fun a ha => hgood a (hlegal a ha))
    (Filter.Eventually.of_forall fun a _ => hecap a) hmass

theorem highFrameProfile_abs_le_one {d F : ℕ} (C : ℝ) (hC : 1 ≤ C)
    (x : Covariate d) (hx : ∀ i, |x i| ≤ 2) (v : HighFrameIndex d F → ℝ)
    (hv : ∑ γ, |v γ| ≤ C⁻¹) :
    |∑ γ, highFrameFeature x γ * v γ| ≤ 1 := by
  refine ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun γ _ => ?_)).trans
    (hv.trans (inv_le_one_of_one_le₀ hC))
  rw [abs_mul]
  refine (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)).trans_eq (one_mul _)
  unfold highFrameFeature; rw [Finset.abs_prod]
  refine Finset.prod_le_one₀ (fun _ _ => abs_nonneg _) fun i _ => ?_
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (by
    rw [abs_div, show |(8 : ℝ)| = 8 by norm_num]
    exact (div_le_one (by norm_num : (0 : ℝ) < 8)).mpr ((hx i).trans (by norm_num)))

theorem highFrameCoefficientRegression_abs_le {d n F : ℕ}
    (C η ρ : ℝ) (hC : 1 ≤ C) (hη : 0 ≤ η) (hηρ : η ≤ ρ/2)
    (U : Fin n → Covariate d) (hU : ∀ i l, |U i l| ≤ 2)
    (g w : Fin n → ℝ) (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (c : HighFrameIndex d F → ℝ) (hc : ∑ γ, |c γ| ≤ C⁻¹) (i : Fin n) :
    |coefficientRegression η g w (fun i => highFrameFeature (U i)) c i| ≤ ρ := by
  have hprof := highFrameProfile_abs_le_one C hC (U i) (hU i) c hc
  have hwη : |η*w i| ≤ η := by
    rw [abs_mul, abs_of_nonneg hη]
    exact (mul_le_mul_of_nonneg_left (hw i) hη).trans_eq (mul_one _)
  have hterm : |η*w i*(∑ γ, highFrameFeature (U i) γ * c γ)| ≤ η := by
    rw [abs_mul]
    exact (mul_le_mul hwη hprof (abs_nonneg _) hη).trans_eq (mul_one _)
  unfold coefficientRegression
  exact (abs_add_le _ _).trans (by linarith only [hg i, hterm, hηρ])

def highHistoryLikelihoodDerivative {J E : Type*} [Fintype J] [LinearOrder J]
    [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (π : Measure E) (activation : E → ℝ) (n : ℕ) (a V η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (ω : HistoryMarked dependent E) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) : ℝ :=
  (∑ j, highAppendLikelihoodAction dependent hsymm π activation n a V p F j ω z) -
    η^2 * highRawSampleVarianceDerivative n a V (p ω) (F ω) z

def highHistoryLikelihoodScore {J E : Type*} [Fintype J] [LinearOrder J]
    [MeasurableSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (π : Measure E) (activation : E → ℝ) (n : ℕ) (a V η : ℝ)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (ω : HistoryMarked dependent E) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) : ℝ :=
  highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F ω z /
    highRawSampleLikelihood n a V (p ω) (F ω) z

theorem highHistoryLikelihoodDerivative_measurable {J E : Type*} [Fintype J] [LinearOrder J]
    [MeasurableSpace E] [StandardBorelSpace E] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (π : Measure E) [SFinite π] (activation : E → ℝ) (ham : Measurable activation)
    (n : ℕ) (a V η : ℝ) (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F)) :
    Measurable fun z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)) =>
      highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2 :=
  (Finset.measurable_sum _ fun j _ =>
    highAppendLikelihoodAction_measurable dependent hsymm π activation ham n a V p F hp hF j).sub
      ((highRawSampleVarianceDerivative_joint_measurable n a V p F hp hF).const_mul (η^2))

theorem highRawSampleLikelihood_pos {Ω : Type*} {d : ℕ} (n : ℕ) (a V : ℝ)
    (p F : Ω → Covariate d → ℝ) (hp : ∀ ω x, 0 < p ω x)
    (hq : ∀ ω x y, 0 < ternaryMass a (F ω x) V y)
    (ω : Ω) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    0 < highRawSampleLikelihood n a V (p ω) (F ω) z :=
  Finset.prod_pos fun _ _ => mul_pos (hp ω _) (hq ω _ _)

theorem highHistoryLikelihoodDerivative_observable {J E : Type*} [Fintype J] [LinearOrder J]
    [MeasurableSpace E] [StandardBorelSpace E] (π : Measure E) [IsProbabilityMeasure π] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (ν : Measure (HistoryMarked dependent E)) [IsProbabilityMeasure ν]
    (activation : E → ℝ) (ham : Measurable activation)
    (Ba : ℝ) (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a V η P B : ℝ) (hP : 0 ≤ P) (hB : 0 ≤ B) (ha : 0 < a)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hp : Measurable (Function.uncurry p)) (hF : Measurable (Function.uncurry F))
    (hpb : ∀ ω x, |p ω x| ≤ P) (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
    (H : (Fin n → Observation d) → ℝ) (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B) :
    (∫ z : HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3)),
      H (encodeDesignResponse a z.2) *
        highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F z.1 z.2
      ∂ν.prod (highSampleReference d n)) =
      (-η^2 * ∫ ω, highRawObservableVarianceDerivative n a V (p ω) (F ω) H ∂ν) +
        ∑ j, ∫ z : HistoryMarked dependent E × E,
          highRawObservable n a V (p (historyMarkedAppend dependent hsymm j z))
            (F (historyMarkedAppend dependent hsymm j z)) H * activation z.2 ∂ν.prod π := by
  let Q := HistoryMarked dependent E × ((Fin n → Covariate d) × (Fin n → Fin 3))
  let μ : Measure Q := ν.prod (highSampleReference d n)
  let test : Q → ℝ := fun z => H (encodeDesignResponse a z.2)
  let A : J → Q → ℝ := fun j z =>
    highAppendLikelihoodAction dependent hsymm π activation n a V p F j z.1 z.2
  let D : Q → ℝ := fun z => highRawSampleVarianceDerivative n a V (p z.1) (F z.1) z.2
  have htest : Measurable test := (hH.comp (encodeDesignResponse_measurable a)).comp measurable_snd
  have hiA (j : J) : Integrable (fun z => test z * A j z) μ :=
    Integrable.of_bound (htest.mul
      (highAppendLikelihoodAction_measurable dependent hsymm π activation ham n a V p F hp hF j)).aestronglyMeasurable
      (B * (Ba * P^n)) <| Eventually.of_forall fun z => by
        change ‖H (encodeDesignResponse a z.2) *
          highAppendLikelihoodAction dependent hsymm π activation n a V p F j z.1 z.2‖ ≤ _
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hHb _) (highAppendLikelihoodAction_abs_le π dependent hsymm activation Ba hBa
          habound n a V P hP ha.ne' p F hpb hq j z.1 z.2) (abs_nonneg _) hB
  have hiD : Integrable (fun z => test z * D z) μ :=
    Integrable.of_bound (htest.mul
      (highRawSampleVarianceDerivative_joint_measurable n a V p F hp hF)).aestronglyMeasurable
      (B * (P^n * ((n : ℝ)/a^2))) <| Eventually.of_forall fun z => by
        change ‖H (encodeDesignResponse a z.2) * highRawSampleVarianceDerivative n a V (p z.1) (F z.1) z.2‖ ≤ _
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hHb _) (highRawSampleVarianceDerivative_abs_le n a V P ha hP _ _ (hpb _) (hq _) z.2)
          (abs_nonneg _) hB
  calc
    _ = ∫ z, ((∑ j, test z * A j z) - η^2 * (test z * D z)) ∂μ :=
      integral_congr_ae <| Eventually.of_forall fun z => by
        dsimp only [highHistoryLikelihoodDerivative, test, A, D]; rw [mul_sub, Finset.mul_sum]; ring
    _ = (∑ j, ∫ z, test z * A j z ∂μ) - η^2 * ∫ z, test z * D z ∂μ := by
      rw [integral_sub (integrable_finsetSum _ fun j _ => hiA j) (hiD.const_mul _),
        integral_finsetSum _ fun j _ => hiA j, integral_const_mul]
    _ = _ := by
      rw [show (∫ z, test z * D z ∂μ) = ∫ ω, highRawObservableVarianceDerivative n a V (p ω) (F ω) H ∂ν from
        MeasureTheory.integral_prod _ hiD,
        show (∑ j, ∫ z, test z * A j z ∂μ) = ∑ j, ∫ z : HistoryMarked dependent E × E,
          highRawObservable n a V (p (historyMarkedAppend dependent hsymm j z))
            (F (historyMarkedAppend dependent hsymm j z)) H * activation z.2 ∂ν.prod π from
          Finset.sum_congr rfl fun j _ => (highAppendLikelihoodAction_prior_observable π dependent hsymm ν
            activation ham Ba hBa habound n a V P B hP hB ha.ne' p F hp hF hpb hq H hH hHb j).symm]
      ring

theorem highHistoryLikelihoodDerivative_abs_le {J E : Type*} [Fintype J] [LinearOrder J]
    [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π] {d : ℕ}
    (dependent : J → J → Prop) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (activation : E → ℝ) (Ba : ℝ) (hBa : 0 ≤ Ba) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a V η P : ℝ) (hP : 0 ≤ P) (ha : 0 < a)
    (p F : HistoryMarked dependent E → Covariate d → ℝ)
    (hpb : ∀ ω x, |p ω x| ≤ P) (hq : ∀ ω x y, 0 ≤ ternaryMass a (F ω x) V y)
    (ω : HistoryMarked dependent E) (z : (Fin n → Covariate d) × (Fin n → Fin 3)) :
    |highHistoryLikelihoodDerivative dependent hsymm π activation n a V η p F ω z| ≤
      (Fintype.card J : ℝ) * (Ba * P^n) + η^2 * (P^n * ((n : ℝ)/a^2)) := by
  unfold highHistoryLikelihoodDerivative
  have hsub : |∑ j, highAppendLikelihoodAction dependent hsymm π activation n a V p F j ω z -
      η^2 * highRawSampleVarianceDerivative n a V (p ω) (F ω) z| ≤
      |∑ j, highAppendLikelihoodAction dependent hsymm π activation n a V p F j ω z| +
        |η^2 * highRawSampleVarianceDerivative n a V (p ω) (F ω) z| := by
    simpa only [sub_zero, zero_sub, abs_neg] using
      abs_sub_le (∑ j, highAppendLikelihoodAction dependent hsymm π activation n a V p F j ω z)
        (0 : ℝ) (η^2 * highRawSampleVarianceDerivative n a V (p ω) (F ω) z)
  refine hsub.trans (add_le_add ?_ ?_)
  · exact (Finset.abs_sum_le_sum_abs _ _).trans
      ((Finset.sum_le_sum fun j _ => highAppendLikelihoodAction_abs_le π dependent hsymm activation Ba hBa
        habound n a V P hP ha.ne' p F hpb hq j ω z).trans_eq (by simp))
  · rw [abs_mul, abs_of_nonneg (sq_nonneg η)]
    exact mul_le_mul_of_nonneg_left
      (highRawSampleVarianceDerivative_abs_le n a V P ha hP (p ω) (F ω) (hpb ω) (hq ω) z) (sq_nonneg η)

theorem map_snd_prod_withDensity_ofReal {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (μ : Measure Z) [SFinite μ] (f : Ω × Z → ℝ) (hf : Measurable f)
    (C : ℝ) (_hC : 0 ≤ C) (hbound : ∀ z, 0 ≤ f z ∧ f z ≤ C) :
    ((ν.prod μ).withDensity fun z => ENNReal.ofReal (f z)).map Prod.snd =
      μ.withDensity fun z => ENNReal.ofReal (∫ ω, f (ω, z) ∂ν) := by
  have he : ((ν.prod μ).withDensity fun z => ENNReal.ofReal (f z)).map Prod.snd =
      μ.withDensity fun z => ∫⁻ ω, ENNReal.ofReal (f (ω, z)) ∂ν := by
    apply Measure.ext_of_lintegral; intro G hG
    have hfE := hf.ennreal_ofReal
    have hGm : Measurable fun z : Ω × Z => G z.2 := hG.comp measurable_snd
    rw [lintegral_map hG measurable_snd, lintegral_withDensity_eq_lintegral_mul _ hfE hGm,
      lintegral_prod_symm' _ (hfE.mul hGm),
      lintegral_withDensity_eq_lintegral_mul _ hfE.lintegral_prod_left' hG]
    exact lintegral_congr fun z => lintegral_mul_const (G z) (hfE.comp (measurable_id.prodMk measurable_const))
  rw [he]; congr 1; funext z
  have hi : Integrable (fun ω => f (ω, z)) ν :=
    Integrable.of_bound (hf.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable C
      (Eventually.of_forall fun ω => by
        change ‖f (ω, z)‖ ≤ C
        rw [Real.norm_eq_abs, abs_of_nonneg (hbound _).1]; exact (hbound _).2)
  exact (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun ω => (hbound _).1)).symm

theorem integral_likelihood_pos {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (f : Ω → ℝ) (hf : Measurable f) (C : ℝ) (hpos : ∀ ω, 0 < f ω)
    (hbound : ∀ ω, f ω ≤ C) : 0 < ∫ ω, f ω ∂ν := by
  have hi : Integrable f ν :=
    Integrable.of_bound hf.aestronglyMeasurable C <| Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hpos ω).le]; exact hbound ω
  rw [integral_pos_iff_support_of_nonneg (fun ω => (hpos ω).le) hi,
    show Function.support f = univ by ext ω; simp [(hpos ω).ne']]
  simp

end RiskAndLikelihood

-- ============================================================================
-- 2. Normalized Counts, Local Field Score, and IID Factorial Energy Series
-- ============================================================================

section FieldScoreAndSeries
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

def highNormalizedDesignLaw {d : ℕ} (p : Covariate d → ℝ) : Measure (Covariate d) :=
  (cubeVolume d).withDensity fun x => ENNReal.ofReal (highNormalizedDensity p x)

theorem high_normalized_design_probability {d : ℕ} (p : Covariate d → ℝ)
    (hp : Measurable p) (a b : ℝ) (ha : 0 < a)
    (hb : ∀ᵐ x ∂cubeVolume d, a ≤ p x ∧ p x ≤ b) : IsProbabilityMeasure (highNormalizedDesignLaw p) :=
  normalizedDensityTernaryParameter_design_probability p hp a b ha hb

def highFixedScoreDenominator (pMinus cMass : ℝ) : ℝ := (pMinus ^ 2 * cMass)⁻¹

theorem high_fixed_score_denominator_pos {pMinus cMass : ℝ} (hp : 0 < pMinus) (hc : 0 < cMass) :
    0 < highFixedScoreDenominator pMinus cMass := by
  unfold highFixedScoreDenominator; positivity

def highFrameMarkedScore {E : Type*} [MeasurableSpace E] (d k D n : ℕ) [NeZero k]
    (π : HighWindowLabels d k → Measure E)
    (activation : HighWindowLabels d k → E → ℝ) (a V η : ℝ) (p : Fin n → ℝ)
    (pReset : HighWindowLabels d k → E → Fin n → ℝ)
    (cReset : HighWindowLabels d k → E → HighFrameIndex d D → ℝ)
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ) (x : Fin n → Covariate d)
    (j : HighWindowLabels d k) (y : Fin n → Fin 3) : ℝ :=
  highMarkedLocalScore (π j) (activation j) a V η p (pReset j) (cReset j)
    (fun i => highLocalFieldWithout d k D η c j (x i))
    (fun i => highPeriodicTensor d k j (x i))
    (fun i => highLocalFrameFeature k j (x i)) (c j) y

theorem highFrameMarkedScore_energy_bound {E : Type*} [MeasurableSpace E]
    (d k D n : ℕ) [NeZero k] (hk : 4 ≤ k)
    (π : HighWindowLabels d k → Measure E)
    (activation : HighWindowLabels d k → E → ℝ) (hAct : ∀ j, Integrable (activation j) (π j))
    (a V η pPlus : ℝ) (ha : a ≠ 0) (hpPlus : 0 ≤ pPlus) (p : Fin n → ℝ)
    (pReset : HighWindowLabels d k → E → Fin n → ℝ)
    (hReset : ∀ j i, Measurable fun e => pReset j e i)
    (hBound : ∀ j e i, |pReset j e i| ≤ pPlus)
    (cReset : HighWindowLabels d k → E → HighFrameIndex d D → ℝ)
    (hcReset : ∀ j γ, Measurable fun e => cReset j e γ)
    (c : HighWindowLabels d k → HighFrameIndex d D → ℝ) (x : Fin n → Covariate d)
    (hpd : ∀ i, p i ≠ 0)
    (hp : ∀ i b, 0 < ternaryMass a
      (highFrameField d k η (fun l => highFramePolynomial (c l)) (x i)) V b)
    (hpReset : ∀ j e i b, 0 ≤ ternaryMass a
      (coefficientRegression η (fun i => highLocalFieldWithout d k D η c j (x i))
        (fun i => highPeriodicTensor d k j (x i))
        (fun i => highLocalFrameFeature k j (x i)) (cReset j e) i) V b)
    (hDensity : ∀ j, (∫ e, activation j e * ∏ i, pReset j e i ∂π j) = 0) :
    (∫ y, (∑ j, highFrameMarkedScore d k D n π activation a V η p pReset cReset c x j y)^2
      ∂Measure.pi (fun i => ternaryIndexMeasure a
        (highFrameField d k η (fun l => highFramePolynomial (c l)) (x i)) V
        ha fun b => (hp i b).le)) ≤
      (3^d : ℕ) * ∑ j, ∫ y,
        (highFrameMarkedScore d k D n π activation a V η p pReset cReset c x j y)^2
        ∂Measure.pi (fun i => ternaryIndexMeasure a
          (highFrameField d k η (fun l => highFramePolynomial (c l)) (x i)) V
          ha fun b => (hp i b).le) := by
  let f (i : Fin n) := highFrameField d k η (fun l => highFramePolynomial (c l)) (x i)
  let μ (i : Fin n) := ternaryIndexMeasure a (f i) V ha fun b => (hp i b).le
  have hreg (j) := highFrameField_coefficientRegression d k D n hk η c j x
  have hp' (j) (i : Fin n) (b : Fin 3) :
      0 < ternaryMass a (coefficientRegression η (fun i => highLocalFieldWithout d k D η c j (x i))
        (fun i => highPeriodicTensor d k j (x i)) (fun i => highLocalFrameFeature k j (x i)) (c j) i) V b := by
    rw [hreg j]; exact hp i b
  refine finite_overlap_variance_bound _
    (highFrameMarkedScore d k D n π activation a V η p pReset cReset c x)
    (fun j l => l ∈ highNeighborLabels d k j) (3^d)
    (fun j l => ⟨highNeighborLabels_symmetric d k j l, highNeighborLabels_symmetric d k l j⟩)
    (fun j => by convert highNeighborLabels_card_le d k j using 1; congr 1; ext l; simp)
    fun j l hjl => ?_
  refine local_response_scores_orthogonal μ _ _
    (highPatchSampleIndices d k n j x) (highPatchSampleIndices d k n l x)
    (highPatchSampleIndices_disjoint d k n x j l hjl)
    (fun y y' hyy => highMarkedLocalScore_depends_on_support (π j) (activation j) a V η p
      (pReset j) (cReset j) _ _ _ (c j) _
      (highPeriodicTensor_sample_zero_outside_patch d k n j x) y y' hyy hpd (hp' j))
    (fun y y' hyy => highMarkedLocalScore_depends_on_support (π l) (activation l) a V η p
      (pReset l) (cReset l) _ _ _ (c l) _
      (highPeriodicTensor_sample_zero_outside_patch d k n l x) y y' hyy hpd (hp' l)) ?_
  simpa only [highFrameMarkedScore, μ, f, hreg j] using highMarkedLocalScore_centered (π j) (activation j) a V η ha p
    (pReset j) (cReset j) _ _ _ (c j) hpd (hp' j)
    (fun y => highMarkedResponseAction_integrable (π j) (activation j) (hAct j)
      a V η ha pPlus hpPlus (pReset j) (hReset j) (hBound j) (cReset j) (hcReset j) _ _ _ (hpReset j) y)
    (hDensity j)

theorem iid_local_energy_le_factorial_spatial_series {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (n : ℕ) (A : Set α) (hA : MeasurableSet A)
    (E : (Fin n → α) → ℝ) (hE : Integrable E (Measure.pi fun _ : Fin n => μ))
    (H : (S : Finset (Fin n)) → (S → α) → ℝ)
    (hH : ∀ S, Integrable (H S) (Measure.pi fun _ : S => μ.restrict A))
    (hHn : ∀ S z, 0 ≤ H S z)
    (hdom : ∀ S x, x ∈ designMembershipCell n A S → E x ≤ H S fun i : S => x i.val)
    (ψ : ℝ) (hψ : 0 ≤ ψ) (J : ℕ → ℝ) (hJ : ∀ r, 0 ≤ J r)
    (hspatial : ∀ S : Finset (Fin n), (∫ z, H S z ∂Measure.pi fun _ : S => μ.restrict A) ≤ ψ ^ S.card * J S.card) :
    (∫ x, E x ∂Measure.pi fun _ : Fin n => μ) ≤
      ∑ r ∈ Finset.range (n + 1), ((n : ℝ) * ψ) ^ r / (r.factorial : ℝ) * J r := by
  have hcover : (⋃ S : Finset (Fin n), designMembershipCell n A S) = univ :=
    Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr
      ⟨Finset.univ.filter fun i => x i ∈ A, (design_membership_cell_iff n A _ x).mpr fun i => by simp⟩
  have hpart : (∫ x, E x ∂Measure.pi fun _ : Fin n => μ) =
      ∑ S : Finset (Fin n), ∫ x in designMembershipCell n A S, E x ∂Measure.pi fun _ : Fin n => μ := by
    rw [← setIntegral_univ, ← hcover]
    exact integral_iUnion_fintype (design_membership_cell_measurable n A hA)
      (design_membership_cells_disjoint n A) fun _ => hE.integrableOn
  have hcell (S : Finset (Fin n)) :
      (∫ x in designMembershipCell n A S, E x ∂Measure.pi fun _ : Fin n => μ) ≤
        ψ ^ S.card * J S.card := by
    let μi : Fin n → Measure α := fun i => μ.restrict (if i ∈ S then A else Aᶜ)
    have hm : (Measure.pi fun _ : Fin n => μ).restrict (designMembershipCell n A S) = Measure.pi μi :=
      Measure.restrict_pi_pi _ _
    have hs := measurePreserving_piEquivPiSubtypeProd μi fun i : Fin n => i ∈ S
    have hι : (Subtype.fintype (fun i : Fin n => i ∈ S) : Fintype S) = Finset.Subtype.fintype S := Subsingleton.elim _ _
    rw [hι] at hs
    have hin : (fun i : S => μi i.val) = fun _ : S => μ.restrict A := funext fun i => by simp [μi, ite_eq_left i.property]
    have hout : (fun i : {i : Fin n // i ∉ S} => μi i.val) = fun _ => μ.restrict Aᶜ :=
      funext fun i => by simp [μi, ite_eq_right i.property]
    have hp : Integrable (fun z : (S → α) × ({i : Fin n // i ∉ S} → α) => H S z.1)
        ((Measure.pi fun _ : S => μ.restrict A).prod (Measure.pi fun _ : {i : Fin n // i ∉ S} => μ.restrict Aᶜ)) := by
      simpa only [mul_one] using (hH S).mul_prod
        (integrable_const (1 : ℝ) (μ := Measure.pi fun _ : {i : Fin n // i ∉ S} => μ.restrict Aᶜ))
    have hselected : Integrable (fun x : Fin n → α => H S fun i : S => x i.val)
        ((Measure.pi fun _ : Fin n => μ).restrict (designMembershipCell n A S)) := by
      rw [hm]; rw [hin, hout] at hs
      exact (hs.integrable_comp_emb
        (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => α) fun i => i ∈ S).measurableEmbedding).mpr hp
    have he := hs.integral_comp' fun z => H S z.1
    change (∫ x, H S (fun i : S => x i.val) ∂Measure.pi μi) = _ at he
    have hint := integral_prod_mul (μ := Measure.pi fun _ : S => μ.restrict A)
      (ν := Measure.pi fun _ : {i : Fin n // i ∉ S} => μ.restrict Aᶜ) (H S) fun _ => (1 : ℝ)
    simp only [mul_one] at hint
    have hcard : Fintype.card {i : Fin n // i ∉ S} = n - S.card := by rw [Fintype.card_subtype_compl]; simp
    calc
      _ ≤ ∫ x in designMembershipCell n A S, H S (fun i : S => x i.val) ∂Measure.pi fun _ : Fin n => μ := by
        refine integral_mono_ae hE.integrableOn hselected ?_
        filter_upwards [ae_restrict_mem (design_membership_cell_measurable n A hA S)] with x hx
        exact hdom S x hx
      _ = (μ.real Aᶜ) ^ (n - S.card) * ∫ z, H S z ∂Measure.pi fun _ : S => μ.restrict A := by
        rw [hm, he, hin, hout, hint, integral_const, smul_eq_mul, mul_one]
        simp only [Measure.real, Measure.pi_univ, Measure.restrict_apply_univ,
          Finset.prod_const, Finset.card_univ, ENNReal.toReal_pow, hcard]; ring
      _ ≤ ∫ z, H S z ∂Measure.pi fun _ : S => μ.restrict A :=
        (mul_le_mul_of_nonneg_right (pow_le_one₀ measureReal_nonneg measureReal_le_one)
          (integral_nonneg (hHn S))).trans_eq (one_mul _)
      _ ≤ _ := hspatial S
  rw [hpart]
  refine (Finset.sum_le_sum fun S _ => hcell S).trans ?_
  have hcard_sum : (∑ S : Finset (Fin n), ψ ^ S.card * J S.card) =
      ∑ r ∈ Finset.range (n + 1), (n.choose r : ℝ) * (ψ ^ r * J r) := by
    have h := Finset.sum_powerset (Finset.univ : Finset (Fin n)) fun S => ψ ^ S.card * J S.card
    simp only [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] at h
    rw [h]
    refine Finset.sum_congr rfl fun r _ => ?_
    simpa only [Finset.sum_powersetCard, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using
      Finset.sum_powersetCard r (Finset.univ : Finset (Fin n)) fun r => ψ ^ r * J r
  rw [hcard_sum]
  refine Finset.sum_le_sum fun r _ => ?_
  calc
    (n.choose r : ℝ) * (ψ ^ r * J r) ≤ ((n : ℝ) ^ r / (r.factorial : ℝ)) * ψ ^ r * J r := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div r n) (pow_nonneg hψ r)) (hJ r)
    _ = _ := by rw [mul_pow]; ring

end FieldScoreAndSeries

-- ============================================================================
-- 3. Spatial Subset Energy, Higher-Field Moment L2, and Fine-Pair All-Counts
-- ============================================================================

section SpatialAndFineFieldL2
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem finite_pi_reindex_integrable {I J E : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ] (e : I ≃ J) (f : (J → E) → ℝ)
    (hf : Integrable f (Measure.pi fun _ : J => μ)) :
    Integrable (fun U : I → E => f fun j => U (e.symm j)) (Measure.pi fun _ : I => μ) := by
  have he (U : I → E) : (Equiv.piCongrLeft (fun _ : J => E) e) U = fun j => U (e.symm j) :=
    funext fun _ => by simp only [Equiv.piCongrLeft_apply_eq_cast, cast_eq]
  simpa only [Function.comp_def, MeasurableEquiv.coe_piCongrLeft, he] using
    (measurePreserving_piCongrLeft (fun _ : J => μ) e).integrable_comp_of_integrable hf

theorem spatial_subset_square_integrable_enumerated {d k : ℕ} (s : Finset (Fin k))
    (f : (Fin s.card → Covariate d) → ℝ)
    (hf : Integrable (fun V => f V ^ 2) (fullSpatialPatchDesign d s.card)) :
    Integrable (fun U : Fin k → Covariate d => f (spatialSubsetConfiguration s U) ^ 2)
      (fullSpatialPatchDesign d k) := by
  let e : s ≃ Fin s.card := (Fintype.equivFin s).trans (finCongr (Fintype.card_coe s))
  exact finite_pi_subset_integrable (volume.restrict (spatialPatchBox d)) s
    (fun V : s → Covariate d => f (fun j => V (e.symm j)) ^ 2)
    (finite_pi_reindex_integrable (volume.restrict (spatialPatchBox d)) e (fun V => f V ^ 2) hf)

theorem finite_sum_square_integral_le {I X : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset I) (f : I → X → ℝ) (K : ℝ)
    (hm : ∀ i ∈ s, Measurable (f i))
    (hi : ∀ i ∈ s, Integrable (fun x => f i x ^ 2) μ)
    (hK : ∀ i ∈ s, (∫ x, f i x ^ 2 ∂μ) ≤ K) :
    (∫ x, (∑ i ∈ s, f i x) ^ 2 ∂μ) ≤ (s.card : ℝ) ^ 2 * K := by
  have hb (x : X) : (∑ i ∈ s, f i x) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, f i x ^ 2 := by
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq s (fun _ : I => (1 : ℝ)) fun i => f i x
  have hu : Integrable (fun x => (s.card : ℝ) * ∑ i ∈ s, f i x ^ 2) μ :=
    (integrable_finsetSum s hi).const_mul _
  have hl : Integrable (fun x => (∑ i ∈ s, f i x) ^ 2) μ :=
    hu.mono' ((Finset.measurable_fun_sum s hm).pow_const 2).aestronglyMeasurable <|
      Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_sq]; exact hb x
  have h := integral_mono hl hu hb
  rw [integral_const_mul, integral_finsetSum _ hi] at h
  exact h.trans (by simpa only [Finset.sum_const, nsmul_eq_mul, sq, ← mul_assoc] using
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum hK) (Nat.cast_nonneg s.card))

theorem spatial_subset_sum_square_integral_le {d k r : ℕ}
    (f : (s : Finset (Fin k)) → (Fin s.card → Covariate d) → ℝ) (K : ℝ)
    (hm : ∀ s ∈ (Finset.univ : Finset (Fin k)).powersetCard r, Measurable (f s))
    (hi : ∀ s ∈ (Finset.univ : Finset (Fin k)).powersetCard r,
      Integrable (fun V => f s V ^ 2) (fullSpatialPatchDesign d s.card))
    (hK : ∀ s ∈ (Finset.univ : Finset (Fin k)).powersetCard r,
      (∫ V, f s V ^ 2 ∂fullSpatialPatchDesign d s.card) ≤ K) :
    (∫ U, (∑ s ∈ (Finset.univ : Finset (Fin k)).powersetCard r,
      f s (spatialSubsetConfiguration s U)) ^ 2 ∂fullSpatialPatchDesign d k) ≤
      (k.choose r : ℝ) ^ 2 * (2 : ℝ) ^ (d * (k - r)) * K := by
  classical
  simpa only [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, ← mul_assoc] using
    finite_sum_square_integral_le (fullSpatialPatchDesign d k)
      ((Finset.univ : Finset (Fin k)).powersetCard r)
      (fun s U => f s (spatialSubsetConfiguration s U)) ((2 : ℝ) ^ (d * (k - r)) * K)
      (fun s hs => (hm s hs).comp (spatialSubsetConfiguration_measurable s))
      (fun s hs => spatial_subset_square_integrable_enumerated s (f s) (hi s hs))
      fun s hs => by
        rw [spatial_subset_square_integral_enumerated]
        have hv : (2 : ℝ) ^ (d * (k - s.card)) = (2 : ℝ) ^ (d * (k - r)) := by
          rw [(Finset.mem_powersetCard.mp hs).2]
        rw [hv]
        exact mul_le_mul_of_nonneg_left (hK s hs) (by positivity)

def boundedHyperplaneSpatialMoment (d : ℕ) (T : ℝ) (j : ℕ)
    (U : Fin j → Covariate d) : ℝ :=
  ∫ z, ∏ l, boundedHyperplaneFieldValue z (U l) ∂boundedHyperplaneFieldLaw d T

lemma boundedHyperplaneSpatialMoment_measurable (d : ℕ) [NeZero d] (T : ℝ) (j : ℕ) :
    Measurable (boundedHyperplaneSpatialMoment d T j) := by
  have hm : Measurable fun Uz : (Fin j → Covariate d) × partitionFieldMark (Covariate d × ℝ) =>
      ∏ l, boundedHyperplaneFieldValue Uz.2 (Uz.1 l) :=
    Finset.measurable_prod _ fun l _ =>
      (boundedHyperplaneFieldValue_measurable d).comp
        (measurable_snd.prodMk ((measurable_pi_apply l).comp measurable_fst))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma boundedHyperplaneSpatialMoment_abs_le_one (d : ℕ) [NeZero d]
    (T : ℝ) (j : ℕ) (U : Fin j → Covariate d) :
    |boundedHyperplaneSpatialMoment d T j U| ≤ 1 := by
  unfold boundedHyperplaneSpatialMoment
  exact abs_integral_le_integral_abs.trans_eq (by
    simp only [Finset.abs_prod, boundedHyperplaneFieldValue_abs,
      Finset.prod_const_one, integral_const, probReal_univ, smul_eq_mul, one_mul])

def hyperplaneSpatialMomentConstant (d : ℕ) : ℝ :=
  (2 : ℝ)^d * (1 + spatialExponentialConstant d)

theorem hyperplaneSpatialMomentConstant_positive (d : ℕ) :
    0 < hyperplaneSpatialMomentConstant d := by
  unfold hyperplaneSpatialMomentConstant
  have := spatialExponentialConstant_nonneg d; positivity

lemma boundedHyperplaneSpatialMoment_squared_cube_integral_le
    (d : ℕ) [NeZero d] (T : ℝ) (hT : 0 < T) (j : ℕ) (hj : 4 ≤ j) :
    (∫ U : Fin j → Covariate d, (boundedHyperplaneSpatialMoment d T j U)^2
      ∂Measure.pi fun _ : Fin j => volume.restrict (spatialPatchBox d)) ≤
      (hyperplaneSpatialMomentConstant d ^ j * (j : ℝ)^4 / T^d)^2 := by
  let π := spatialPatchProbability d
  let μ := Measure.pi fun _ : Fin j => π
  let a : ℝ := Fintype.card (CellMomentQuadruple j)
  let qDist (q : CellMomentQuadruple j) (U : Fin j → Covariate d) : ℝ :=
    exactEuclideanDistance (U (q.val 0)) (U (q.val 1)) +
      exactEuclideanDistance (U (q.val 2)) (U (q.val 3))
  let E (q : CellMomentQuadruple j) (U : Fin j → Covariate d) : ℝ :=
    Real.exp (-(T * qDist q U))
  have hqCont (q : CellMomentQuadruple j) : Continuous (qDist q) := by
    have hm01 : Continuous fun U : Fin j → Covariate d => (U (q.val 0), U (q.val 1)) :=
      (continuous_apply (q.val 0)).prodMk (continuous_apply (q.val 1))
    have hm23 : Continuous fun U : Fin j → Covariate d => (U (q.val 2), U (q.val 3)) :=
      (continuous_apply (q.val 2)).prodMk (continuous_apply (q.val 3))
    have h01 : Continuous fun U : Fin j → Covariate d => exactEuclideanDistance (U (q.val 0)) (U (q.val 1)) := by
      simpa only [Function.comp_def] using (exactEuclideanDistance_continuous (d := d)).comp hm01
    have h23 : Continuous fun U : Fin j → Covariate d => exactEuclideanDistance (U (q.val 2)) (U (q.val 3)) := by
      simpa only [Function.comp_def] using (exactEuclideanDistance_continuous (d := d)).comp hm23
    exact h01.add h23
  have hei (q : CellMomentQuadruple j) : Integrable (E q) μ :=
    Integrable.of_bound ((hqCont q).const_mul T |>.neg |>.rexp).measurable.aestronglyMeasurable 1 <|
      Filter.Eventually.of_forall fun U => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hT.le
          (add_nonneg (exactEuclideanDistance_nonneg _ _) (exactEuclideanDistance_nonneg _ _))))
  have hmi : Integrable (fun U => (boundedHyperplaneSpatialMoment d T j U)^2) μ :=
    Integrable.of_bound ((boundedHyperplaneSpatialMoment_measurable d T j).pow_const 2).aestronglyMeasurable 1 <|
      Filter.Eventually.of_forall fun U => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [boundedHyperplaneSpatialMoment_abs_le_one d T j U,
          abs_nonneg (boundedHyperplaneSpatialMoment d T j U), sq_abs (boundedHyperplaneSpatialMoment d T j U)]
  have hae : ∀ᵐ U ∂μ, ∀ l, U l ∈ hyperplaneCube d := by
    refine ae_all_iff.mpr fun l =>
      (measurePreserving_eval (fun _ : Fin j => π) l).quasiMeasurePreserving.tendsto_ae.eventually ?_
    have hbox : spatialPatchBox d = hyperplaneCube d := by
      ext x; simp only [spatialPatchBox, mem_Icc, Pi.le_def, hyperplaneCube, mem_ofPred_eq, abs_le]
      exact ⟨fun h r => ⟨h.1 r, h.2 r⟩, fun h => ⟨fun r => (h r).1, fun r => (h r).2⟩⟩
    rw [show π = spatialPatchProbability d from rfl, spatialPatchProbability, ← hbox]
    exact (ae_restrict_mem measurableSet_Icc).filter_mono (Measure.ae_smul_measure_le _)
  have hpoint : ∀ᵐ U ∂μ, (boundedHyperplaneSpatialMoment d T j U)^2 ≤ a * ∑ q, E q U := by
    filter_upwards [hae] with U hU
    have hb := boundedHyperplaneField_higher_moment_envelope d T hT.le j hj U hU
    simp_rw [← exactEuclideanDistance_eq_euclideanNorm] at hb
    change |boundedHyperplaneSpatialMoment d T j U| ≤
      ∑ q : CellMomentQuadruple j, Real.exp (-T / 2 * qDist q U) at hb
    have hsum : 0 ≤ ∑ q : CellMomentQuadruple j, Real.exp (-T / 2 * qDist q U) :=
      Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
    have hsq : (boundedHyperplaneSpatialMoment d T j U)^2 ≤
        (∑ q : CellMomentQuadruple j, Real.exp (-T / 2 * qDist q U))^2 := by
      nlinarith [sq_abs (boundedHyperplaneSpatialMoment d T j U), abs_nonneg (boundedHyperplaneSpatialMoment d T j U)]
    have heq (q : CellMomentQuadruple j) : Real.exp (-T / 2 * qDist q U)^2 = E q U := by
      rw [← Real.exp_nat_mul]; exact congrArg Real.exp (by dsimp [E]; ring)
    have hs := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun q : CellMomentQuadruple j => Real.exp (-T / 2 * qDist q U))
    exact hsq.trans (by simpa only [Finset.card_univ, heq, a] using hs)
  have hpair (q : CellMomentQuadruple j) : (∫ U, E q U ∂μ) ≤ (spatialExponentialConstant d / T^d)^2 := by
    rw [show (∫ U, E q U ∂μ) =
        (∫ xy : Covariate d × Covariate d, Real.exp (-(T*exactEuclideanDistance xy.1 xy.2)) ∂π.prod π)^2 from
      spatialPi_two_pairs_integral_factor π ⟨q.val, q.property⟩ T]
    have hb := spatial_probability_pair_exponential_integral_le (NeZero.pos d) π (spatialPatchProbability_le_volume d) hT
    have h0 : 0 ≤ ∫ xy : Covariate d × Covariate d, Real.exp (-(T*exactEuclideanDistance xy.1 xy.2)) ∂π.prod π :=
      integral_nonneg fun _ => (Real.exp_pos _).le
    nlinarith
  have ha0 : 0 ≤ a := Nat.cast_nonneg _
  have hac : a ≤ (j : ℝ)^4 := by dsimp only [a]; exact_mod_cast cellMomentQuadruple_card_le j
  have hprob_int : (∫ U, (boundedHyperplaneSpatialMoment d T j U)^2 ∂μ) ≤
      (j : ℝ)^8 * (spatialExponentialConstant d / T^d)^2 :=
    calc
      _ ≤ ∫ U, a * ∑ q, E q U ∂μ :=
        integral_mono_ae hmi ((integrable_finsetSum _ fun q _ => hei q).const_mul a) hpoint
      _ = a * ∑ q, ∫ U, E q U ∂μ := by rw [integral_const_mul, integral_finsetSum _ fun q _ => hei q]
      _ ≤ a * ∑ _q : CellMomentQuadruple j, (spatialExponentialConstant d / T^d)^2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q _ => hpair q) ha0
      _ = a^2 * (spatialExponentialConstant d / T^d)^2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, a]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by simpa only [← pow_mul] using pow_le_pow_left₀ ha0 hac 2) (sq_nonneg _)
  have hsmul : volume.restrict (spatialPatchBox d) = (2 : ℝ≥0∞)^d • π := by
    rw [show π = spatialPatchProbability d from rfl, spatialPatchProbability, smul_smul,
      ENNReal.mul_inv_cancel (by positivity) (by finiteness), one_smul]
  let : IsFiniteMeasure ((2 : ℝ≥0∞)^d • π) := by rw [← hsmul]; infer_instance
  have he : Measure.pi (fun _ : Fin j => volume.restrict (spatialPatchBox d)) =
      ((2 : ℝ≥0∞)^d)^j • μ := by
    simp only [hsmul, μ]
    simpa only [Fintype.card_fin] using spatialPi_const_smul (J := Fin j) π ((2 : ℝ≥0∞)^d)
  rw [he, integral_smul_measure]
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofNat, smul_eq_mul, ← pow_mul]
  let C := spatialExponentialConstant d
  have hC : 0 ≤ C := spatialExponentialConstant_nonneg d
  have hV : (2 : ℝ)^(d*j) ≤ ((2 : ℝ)^d)^(2*j) := by
    rw [pow_mul]; exact pow_le_pow_right₀ (one_le_pow₀ (by norm_num)) (by omega)
  have hCp : C^2 ≤ (1+C)^(2*j) :=
    (pow_le_pow_left₀ hC (by linarith) 2).trans (pow_le_pow_right₀ (by linarith) (by omega))
  have hconst : (2 : ℝ)^(d*j) * C^2 ≤ (hyperplaneSpatialMomentConstant d)^(2*j) := by
    unfold hyperplaneSpatialMomentConstant; rw [mul_pow]
    exact mul_le_mul hV hCp (sq_nonneg C) (by positivity)
  refine (mul_le_mul_of_nonneg_left hprob_int (by positivity : 0 ≤ (2 : ℝ)^(d*j))).trans ?_
  have ht := mul_le_mul_of_nonneg_right hconst (show 0 ≤ (j : ℝ)^8 / (T^d)^2 by positivity)
  convert ht using 1 <;> simp only [C, div_pow, mul_pow, ← pow_mul] <;> ring

def finePairTimeSubsetMoment {d n : ℕ} (lo hi : ℝ) (U : Fin n → Covariate d)
    (S : Finset (Fin n)) : ℝ :=
  ∫ e : ℝ × FinePairFieldMark d,
    e.1 * (∏ i ∈ S, finePairTimeFieldValue e (U i)) ∂finePairTimeFieldMeasure d lo hi

def finePairPairAliasAction {d n F : ℕ} (ad bd T0 N : ℝ) (M q : ℕ) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ)
    (Φ : (HighFrameIndex d F → ℝ) → ℝ) : ℝ :=
  ∑ W ∈ (Finset.univ : Finset (Fin n)).powerset,
    finePairCountCoefficient ad bd M n W.card * (∏ i ∈ W, p i) * (if W.card = 2 then 1 else 0) *
      finePairTimeSubsetMoment T0 N U W * responseMatrixAction q C (finePairDistanceMatrix d F) c Φ

def finePairEvenFieldAction {d n F : ℕ} (ad bd T0 N : ℝ) (M q : ℕ) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ)
    (Φ : (HighFrameIndex d F → ℝ) → ℝ) : ℝ :=
  ∑ W ∈ (Finset.univ : Finset (Fin n)).powerset,
    finePairCountCoefficient ad bd M n W.card * (∏ i ∈ W, p i) *
      (if 4 ≤ W.card ∧ Even W.card then 1 else 0) *
        finePairTimeSubsetMoment T0 N U W * responseMatrixAction q C (finePairDistanceMatrix d F) c Φ

theorem finePairFineFirstAction_alias_even_field {d n F : ℕ} [NeZero d]
    (ad bd T0 N : ℝ) (ha : 0 < ad) (hab : ad < bd) (M q : ℕ) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd)
    (c : HighFrameIndex d F → ℝ) (Φ : (HighFrameIndex d F → ℝ) → ℝ) :
    finePairFineFirstAction ad bd T0 N M q C U p c Φ =
      finePairPairAliasAction ad bd T0 N M q C U p c Φ +
        finePairEvenFieldAction ad bd T0 N M q C U p c Φ := by
  let σ := finePairTimeFieldMeasure d T0 N
  let A := finePairTimeMatrix d (finePairDistanceMatrix d F)
  let ψ (ζ : ℝ × FinePairFieldMark d) (i : Fin n) := finePairTimeFieldValue ζ (U i)
  have hmψ (i : Fin n) : Measurable fun ζ => ψ ζ i :=
    (boundedHyperplaneFieldValue_section_measurable d (U i)).comp measurable_snd
  have hbψ (ζ) (i : Fin n) : |ψ ζ i| ≤ 1 := (finePairTimeFieldValue_abs ζ (U i)).le
  let sel (j : ℕ) : ℝ := if j = 0 then 0 else if Even j then 1 else 0
  have hsplit (j : ℕ) : sel j = (if j = 2 then 1 else 0) + (if 4 ≤ j ∧ Even j then 1 else 0) := by
    by_cases hj0 : j = 0
    · simp [sel, hj0]
    by_cases hj2 : j = 2
    · simp [sel, hj2]
    by_cases hj : Even j
    · have hj4 : 4 ≤ j := by rcases hj with ⟨l, hl⟩; omega
      simp [sel, hj0, hj2, hj, hj4]
    · simp [sel, hj0, hj2, hj]
  rw [finePairFineFirstAction, finePairPacketSignedMeasure_factor_integral σ ad bd M q C A
    (finePairTimeMatrix_measurable d _) (finePairTimeMatrix_cost_integrable d T0 N _) c
    (fun ζ z eps => ∏ i, finePairDensityReset ad bd z eps p (ψ ζ) i)
    (fun z eps => Finset.measurable_fun_prod _ fun i _ => measurable_const.add ((hmψ i).const_mul _))
    (bd^n) (pow_nonneg (ha.trans hab).le n)
    (fun ζ e => finite_density_product_abs_bound _ bd (ha.trans hab).le fun i =>
      finePairFieldReset_abs_le ad bd ha hab M p hp ψ hbψ (ζ, e) i)
    Φ (finePairResponseAtomBound q C c Φ) (finePairResponseAtomBound_le q C c Φ)]
  have hiRsp : Integrable (fun ζ => responseMatrixAction q C (A ζ) c Φ) σ :=
    responseMatrixAction_integrable σ q C A
      (separatedMatrix_entry_integrable σ A (finePairTimeMatrix_measurable d _)
        (finePairTimeMatrix_cost_integrable d T0 N _)) c Φ
  have hi (W : Finset (Fin n)) :
      Integrable (fun ζ => (∏ i ∈ W, ψ ζ i) * responseMatrixAction q C (A ζ) c Φ) σ :=
    hiRsp.bdd_mul (c := 1) (Finset.measurable_fun_prod W fun i _ => hmψ i).aestronglyMeasurable <|
      Filter.Eventually.of_forall fun ζ => by
        rw [Real.norm_eq_abs, Finset.abs_prod]
        exact (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i _ => hbψ ζ i).trans_eq Finset.prod_const_one
  have hsubset (ζ) :
      (∫ᵛ e, (∏ i, finePairDensityReset ad bd e.1 e.2 p (ψ ζ) i) ∂<•finePairDensitySignedRule ad bd M) =
      ∑ W ∈ (Finset.univ : Finset (Fin n)).powerset,
        finePairCountCoefficient ad bd M n W.card * ((∏ i ∈ W, p i) * ∏ i ∈ W, ψ ζ i) * sel W.card := by
    simpa only [Finset.card_univ, Fintype.card_fin, Finset.prod_mul_distrib, sel] using
      finePairDensitySignedRule_product_expansion ad bd M Finset.univ p (ψ ζ)
  simp_rw [hsubset, Finset.sum_mul, show ∀ (W : Finset (Fin n)) ζ,
    finePairCountCoefficient ad bd M n W.card * ((∏ i ∈ W, p i) * ∏ i ∈ W, ψ ζ i) *
      sel W.card * responseMatrixAction q C (A ζ) c Φ =
    (finePairCountCoefficient ad bd M n W.card * (∏ i ∈ W, p i) * sel W.card) *
      ((∏ i ∈ W, ψ ζ i) * responseMatrixAction q C (A ζ) c Φ) from fun _ _ => by ring]
  rw [integral_finsetSum _ fun W _ => (hi W).const_mul _]
  simp only [integral_const_mul]
  have hterm (W : Finset (Fin n)) :
      (∫ e : ℝ × FinePairFieldMark d, (∏ i ∈ W, ψ e i) * responseMatrixAction q C (A e) c Φ ∂σ) =
        finePairTimeSubsetMoment T0 N U W * responseMatrixAction q C (finePairDistanceMatrix d F) c Φ := by
    change (∫ e : ℝ × FinePairFieldMark d, (∏ i ∈ W, finePairTimeFieldValue e (U i)) *
      responseMatrixAction q C (fun i j => e.1 * finePairDistanceMatrix d F i j) c Φ ∂σ) = _
    simp_rw [responseMatrixAction_scalar_matrix, show ∀ e : ℝ × FinePairFieldMark d,
      (∏ i ∈ W, finePairTimeFieldValue e (U i)) * (e.1 * responseMatrixAction q C (finePairDistanceMatrix d F) c Φ) =
      (e.1 * ∏ i ∈ W, finePairTimeFieldValue e (U i)) * responseMatrixAction q C (finePairDistanceMatrix d F) c Φ
      from fun _ => by ring]
    rw [integral_mul_const]; rfl
  simp_rw [hterm, hsplit, finePairPairAliasAction, finePairEvenFieldAction,
    mul_add, add_mul, Finset.sum_add_distrib, mul_assoc]

theorem finePairPairAliasAction_zero_selected_count {d n F : ℕ}
    (ad bd T0 N : ℝ) (ha : 0 < ad) (hab : ad < bd) (M q : ℕ)
    (hn : 3 ≤ n) (hM : n ≤ M) (C : ℝ)
    (U : Fin n → Covariate d) (p : Fin n → ℝ) (c : HighFrameIndex d F → ℝ)
    (Φ : (HighFrameIndex d F → ℝ) → ℝ) :
    finePairPairAliasAction ad bd T0 N M q C U p c Φ = 0 := by
  unfold finePairPairAliasAction
  refine Finset.sum_eq_zero fun W _ => ?_
  by_cases hW : W.card = 2
  · rw [hW, finePairCountCoefficient_two_exact ad bd ha hab M n (by omega) hM]
    simp [show n ≠ 2 by omega]
  · simp [hW]

def finePairResponseActionBudget (d q : ℕ) (C a ρ : ℝ) : ℝ :=
  (512 * d * C^2) * (∑ j : Fin (2*q+2), |responseWeight q j|) * highSeparatedDerivativeBudget a ρ

theorem finePairDistance_response_all_count_bound {d n F : ℕ} (q : ℕ) (hn : 1 ≤ n)
    (C a V η ρ : ℝ) (hC : 0 < C) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hηρ : η ≤ ρ/2) (U : Fin n → Covariate d) (g w : Fin n → ℝ)
    (c : HighFrameIndex d F → ℝ) (y : Fin n → Fin 3)
    (hc : ∑ γ, |c γ| ≤ C⁻¹) (hg : ∀ i, |g i| ≤ ρ/2) (hw : ∀ i, |w i| ≤ 1)
    (hφ : ∀ v : HighFrameIndex d F → ℝ, (∑ γ, |v γ|) ≤ C⁻¹ →
      ∀ i, |∑ γ, highFrameFeature (U i) γ * v γ| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y) :
    |responseMatrixAction q C (finePairDistanceMatrix d F) c
      (fun v => highResponseProduct a V η g w (fun i => highFrameFeature (U i)) v y)| ≤
        finePairResponseActionBudget d q C a ρ * (n : ℝ)^2 * η^2 := by
  have hh := high_response_matrix_all_count_bound q hn C a V η ρ hC ha hη hρ hηρ
    (finePairDistanceMatrix d F) g w (fun i => highFrameFeature (U i)) c y hc hg hw hφ hp
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (finePairDistanceMatrix_l1_le d F) (by positivity : (0 : ℝ) ≤ 2*C^2))
    (by positivity : 0 ≤ (∑ j : Fin (2*q+2), |responseWeight q j|) *
      (4 * (((2*ρ+a)/a^2)^2 + 2/a^2) * (n : ℝ)^2 * η^2))
  exact (hh.trans hmul).trans_eq (by unfold finePairResponseActionBudget highSeparatedDerivativeBudget; ring)

def finePairDensityCoefficientBudget (ad bd : ℝ) (M n : ℕ) : ℝ :=
  |finePairDensityPrefactor ad bd| * bd^n *
    Real.cosh ((M+2 : ℕ) * exteriorTau ((ad+bd)/(bd-ad)))

theorem finePairDensityCoefficientBudget_nonneg (ad bd : ℝ) (hbd : 0 ≤ bd) (M n : ℕ) :
    0 ≤ finePairDensityCoefficientBudget ad bd M n := by
  unfold finePairDensityCoefficientBudget
  exact mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg hbd _)) (Real.cosh_pos _).le

theorem finePairCountCoefficient_product_bound {n : ℕ}
    (ad bd : ℝ) (ha : 0 < ad) (hab : ad < bd) (M : ℕ)
    (p : Fin n → ℝ) (hp : ∀ i, p i ∈ Icc ad bd) (S : Finset (Fin n)) :
    |finePairCountCoefficient ad bd M n S.card * (∏ i ∈ S, p i)| ≤
      finePairDensityCoefficientBudget ad bd M n := by
  have hb : 0 < bd := ha.trans hab
  have hcard : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hprod : |∏ i ∈ S, p i| ≤ bd^S.card := by
    rw [Finset.abs_prod]
    exact (Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun i _ => by
      rw [abs_of_pos (ha.trans_le (hp i).1)]; exact (hp i).2).trans_eq (Finset.prod_const _)
  have hrpow : ((bd-ad)/(4*bd))^S.card ≤ 1 :=
    pow_le_one₀ (div_nonneg (sub_nonneg.mpr hab.le) (by positivity))
      ((div_le_one (by positivity : (0 : ℝ) < 4*bd)).mpr (by linarith only [ha, hb]))
  rw [abs_mul]
  refine (mul_le_mul (finePairCountCoefficient_abs_bound ad bd ha hab M n S.card) hprod
    (abs_nonneg _) (by positivity)).trans ?_
  rw [show |finePairDensityPrefactor ad bd| * (bd^(n-S.card) * ((bd-ad)/(4*bd))^S.card) *
      Real.cosh ((M+2 : ℕ)*exteriorTau ((ad+bd)/(bd-ad))) * bd^S.card =
      finePairDensityCoefficientBudget ad bd M n * ((bd-ad)/(4*bd))^S.card by
    unfold finePairDensityCoefficientBudget
    calc _ = |finePairDensityPrefactor ad bd| * (bd^(n-S.card)*bd^S.card) *
            Real.cosh ((M+2 : ℕ)*exteriorTau ((ad+bd)/(bd-ad))) * ((bd-ad)/(4*bd))^S.card := by ring
      _ = _ := by rw [← pow_add, Nat.sub_add_cancel hcard]]
  exact (mul_le_mul_of_nonneg_left hrpow
    (finePairDensityCoefficientBudget_nonneg ad bd hb.le M n)).trans_eq (mul_one _)

lemma weighted_scale_square_energy_le {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu] (d : ℕ) {lo hi K : ℝ}
    (hlo : 0 < lo) (_hK : 0 ≤ K) (F : ℝ × X → ℝ) (hF : Measurable F)
    (hFb : ∀ z, |F z| ≤ 1)
    (hE : ∀ T ∈ Icc lo hi, (∫ x, F (T, x) ^ 2 ∂mu) ≤ K ^ 2 / (T ^ d) ^ 2) :
    Integrable (fun x => (∫ T in Icc lo hi, T * F (T, x)) ^ 2) mu ∧
      (∫ x, (∫ T in Icc lo hi, T * F (T, x)) ^ 2 ∂mu) ≤
        K ^ 2 * (∫ T in Icc lo hi, T / T ^ d) ^ 2 := by
  let nu : Measure ℝ := volume.restrict (Icc lo hi)
  let wt (T : ℝ) := T / T ^ d
  let W : ℝ := ∫ T, wt T ∂nu
  let f : ℝ × X → ℝ := fun z => z.1 * F z
  let g : ℝ × X → ℝ := fun z => z.1 * z.1 ^ d * F z ^ 2
  have hw : Integrable wt nu :=
    (continuousOn_id.div (continuous_pow d).continuousOn fun T hT =>
      (pow_pos (hlo.trans_le hT.1) d).ne').integrableOn_compact isCompact_Icc
  have hW : 0 ≤ W := integral_nonneg_of_ae <| by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
    exact div_nonneg (hlo.le.trans hT.1) (pow_nonneg (hlo.le.trans hT.1) _)
  have hfm : Measurable f := measurable_fst.mul hF
  have hfi : Integrable f (nu.prod mu) :=
    ((continuous_id.continuousOn.integrableOn_compact isCompact_Icc).comp_fst mu).mul_bdd
      hF.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hFb z)
  have hgi : Integrable g (nu.prod mu) :=
    (((continuous_id.mul (continuous_pow d)).continuousOn.integrableOn_compact isCompact_Icc).comp_fst mu).mul_bdd
      (c := 1) (hF.pow_const 2).aestronglyMeasurable <| Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, abs_sq]; nlinarith only [hFb z, sq_abs (F z), abs_nonneg (F z)]
  have hcs : ∀ᵐ x ∂mu, (∫ T, f (T, x) ∂nu) ^ 2 ≤ W * ∫ T, g (T, x) ∂nu := by
    filter_upwards [hfi.prod_left_ae, hgi.prod_left_ae] with x hfx hgx
    refine integral_square_le_weight_mass_mul nu (fun T => f (T, x)) wt (fun T => g (T, x)) hfx hw hgx ?_ ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
      exact div_nonneg (hlo.le.trans hT.1) (pow_nonneg (hlo.le.trans hT.1) _)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
      exact mul_nonneg (mul_nonneg (hlo.le.trans hT.1) (pow_nonneg (hlo.le.trans hT.1) _)) (sq_nonneg _)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
      have hp : T ^ d ≠ 0 := (pow_pos (hlo.trans_le hT.1) d).ne'
      dsimp [f, g, wt]; field_simp; exact le_refl _
  have hsi : Integrable (fun x => (∫ T, f (T, x) ∂nu) ^ 2) mu :=
    (hgi.integral_prod_right.const_mul W).mono'
      (hfm.stronglyMeasurable.integral_prod_left'.measurable.pow_const 2).aestronglyMeasurable <|
      hcs.mono fun x hx => by rw [Real.norm_eq_abs, abs_sq]; exact hx
  have hbound := integral_mono_ae hsi (hgi.integral_prod_right.const_mul W) hcs
  rw [integral_const_mul, (integral_integral_swap hgi).symm] at hbound
  have hi : (∫ T, ∫ x, g (T, x) ∂mu ∂nu) ≤ K ^ 2 * W := by
    refine (integral_mono_ae hgi.integral_prod_left (hw.const_mul (K ^ 2)) ?_).trans_eq (integral_const_mul _ _)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
    dsimp [g]; rw [integral_const_mul]
    have hp : 0 < T := hlo.trans_le hT.1
    exact (mul_le_mul_of_nonneg_left (hE T hT)
      (mul_nonneg hp.le (pow_nonneg hp.le d))).trans_eq (by dsimp [wt]; field_simp)
  refine ⟨hsi, ?_⟩
  convert hbound.trans (mul_le_mul_of_nonneg_left hi hW) using 1 <;> dsimp [f, W, nu, wt] <;> ring

lemma finePairTimeSubsetMoment_univ_eq {d j : ℕ} [NeZero d]
    (lo hi : ℝ) (U : Fin j → Covariate d) :
    finePairTimeSubsetMoment lo hi U Finset.univ =
      ∫ T in Icc lo hi, T * boundedHyperplaneSpatialMoment d T j U := by
  have hint : Integrable (fun e : ℝ × FinePairFieldMark d =>
      e.1 * (∏ i ∈ Finset.univ, finePairTimeFieldValue e (U i))) (finePairTimeFieldMeasure d lo hi) :=
    (finePairTimeFieldMeasure_fst_integrable d lo hi).mul_bdd (c := 1)
      (Finset.measurable_fun_prod _ fun i _ =>
        (boundedHyperplaneFieldValue_section_measurable d (U i)).comp measurable_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall fun e => by
        rw [Real.norm_eq_abs, Finset.abs_prod]
        simp only [finePairTimeFieldValue_abs, Finset.prod_const_one, le_rfl])
  rw [finePairTimeSubsetMoment, finePairTimeFieldMeasure_integral d lo hi _ hint]
  simp only [finePairTimeFieldValue, integral_const_mul]; rfl

lemma finePairTimeSubsetMoment_univ_square_integrable_and_le {d j : ℕ} [NeZero d]
    (hd : 3 ≤ d) (hj : 4 ≤ j) {lo hi : ℝ} (hlo : 0 < lo) :
    Integrable (fun U : Fin j → Covariate d =>
      finePairTimeSubsetMoment lo hi U Finset.univ ^ 2) (fullSpatialPatchDesign d j) ∧
    (∫ U : Fin j → Covariate d,
      finePairTimeSubsetMoment lo hi U Finset.univ ^ 2 ∂fullSpatialPatchDesign d j) ≤
      (hyperplaneSpatialMomentConstant d ^ j * (j : ℝ) ^ 4 * lo ^ (2 - (d : ℝ))) ^ 2 := by
  let K : ℝ := hyperplaneSpatialMomentConstant d ^ j * (j : ℝ) ^ 4
  have hK : 0 ≤ K := by positivity [hyperplaneSpatialMomentConstant_positive d]
  let κ : Kernel (ℝ × (Fin j → Covariate d)) (FinePairFieldMark d) :=
    (finePairFieldKernel d).comap (Prod.fst : ℝ × (Fin j → Covariate d) → ℝ) measurable_fst
  have hm : Measurable fun z : (ℝ × (Fin j → Covariate d)) × FinePairFieldMark d =>
      ∏ l, boundedHyperplaneFieldValue z.2 (z.1.2 l) :=
    Finset.measurable_prod _ fun l _ => (boundedHyperplaneFieldValue_measurable d).comp
      (measurable_snd.prodMk ((measurable_pi_apply l).comp (measurable_snd.comp measurable_fst)))
  have hjMeas : Measurable fun z : ℝ × (Fin j → Covariate d) => boundedHyperplaneSpatialMoment d z.1 j z.2 :=
    (hm.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable
  have hh := weighted_scale_square_energy_le (fullSpatialPatchDesign d j) d (lo := lo) (hi := hi) (K := K) hlo hK
    (fun z => boundedHyperplaneSpatialMoment d z.1 j z.2) hjMeas
    (fun z => boundedHyperplaneSpatialMoment_abs_le_one d z.1 j z.2) fun T hT => by
      simpa only [K, div_pow, fullSpatialPatchDesign] using
        boundedHyperplaneSpatialMoment_squared_cube_integral_le d T (hlo.trans_le hT.1) j hj
  simp_rw [finePairTimeSubsetMoment_univ_eq]
  refine ⟨hh.1, (hh.2.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ?_ ?_ 2) (sq_nonneg K))).trans_eq (mul_pow _ _ 2).symm⟩
  · refine integral_nonneg_of_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with T hT
    exact div_nonneg (hlo.le.trans hT.1) (pow_nonneg (hlo.le.trans hT.1) _)
  · have hdR : (3 : ℝ) ≤ d := by exact_mod_cast hd
    have hdec : (1 : ℝ) - d < -1 := by linarith only [hdR]
    have htail : IntegrableOn (fun T : ℝ => T ^ (1 - (d : ℝ))) (Ici lo) := by
      change Integrable (fun T : ℝ => T ^ (1 - (d : ℝ))) (volume.restrict (Ici lo))
      rw [← Measure.restrict_congr_set Ioi_ae_eq_Ici]
      exact integrableOn_Ioi_rpow_of_lt hdec hlo
    have hW : (∫ T in Icc lo hi, T / T ^ d) ≤ lo ^ (2 - (d : ℝ)) / (d - 2 : ℝ) := by
      rw [setIntegral_congr_fun (g := fun T => T ^ (1 - (d : ℝ))) measurableSet_Icc fun T hT => by
        dsimp only; rw [Real.rpow_sub (hlo.trans_le hT.1), Real.rpow_one, Real.rpow_natCast]]
      refine (integral_mono_measure (Measure.restrict_mono_set volume Icc_subset_Ici_self)
        (by filter_upwards [ae_restrict_mem measurableSet_Ici] with T hT; exact Real.rpow_nonneg (hlo.le.trans hT) _) htail).trans_eq ?_
      rw [integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt hdec hlo,
        show (1 - (d : ℝ)) + 1 = 2 - (d : ℝ) by ring, show (2 : ℝ) - d = -(d - 2 : ℝ) by ring]
      simp only [div_neg]; ring
    exact hW.trans (div_le_self (Real.rpow_nonneg hlo.le _) (by linarith only [hdR]))

theorem finePairTimeSubsetMoment_reindex {d k : ℕ} (lo hi : ℝ)
    (U : Fin k → Covariate d) (S : Finset (Fin k)) :
    finePairTimeSubsetMoment lo hi U S =
      finePairTimeSubsetMoment lo hi (spatialSubsetConfiguration S U) Finset.univ := by
  classical
  unfold finePairTimeSubsetMoment
  refine integral_congr_ae <| Filter.Eventually.of_forall fun e => ?_
  let eqv : S ≃ Fin S.card := (Fintype.equivFin S).trans (finCongr (Fintype.card_coe S))
  change e.1 * (∏ i ∈ S, finePairTimeFieldValue e (U i)) =
    e.1 * (∏ j : Fin S.card, finePairTimeFieldValue e (spatialSubsetConfiguration S U j))
  refine congrArg (e.1 * ·) ?_
  rw [← Finset.prod_coe_sort S fun i => finePairTimeFieldValue e (U i)]
  exact (eqv.symm.prod_comp fun i : S => finePairTimeFieldValue e (U i.val)).symm

theorem finePairTimeSubsetMoment_measurable {d k : ℕ} [NeZero d] (lo hi : ℝ)
    (S : Finset (Fin k)) :
    Measurable fun U : Fin k → Covariate d => finePairTimeSubsetMoment lo hi U S := by
  simp_rw [finePairTimeSubsetMoment_reindex (S := S), finePairTimeSubsetMoment_univ_eq]
  let κ : Kernel (ℝ × (Fin S.card → Covariate d)) (FinePairFieldMark d) :=
    (finePairFieldKernel d).comap (Prod.fst : ℝ × (Fin S.card → Covariate d) → ℝ) measurable_fst
  have hm : Measurable fun z : (ℝ × (Fin S.card → Covariate d)) × FinePairFieldMark d =>
      ∏ l, boundedHyperplaneFieldValue z.2 (z.1.2 l) :=
    Finset.measurable_prod _ fun l _ => (boundedHyperplaneFieldValue_measurable d).comp
      (measurable_snd.prodMk ((measurable_pi_apply l).comp (measurable_snd.comp measurable_fst)))
  have hjMeas : Measurable fun z : ℝ × (Fin S.card → Covariate d) =>
      boundedHyperplaneSpatialMoment d z.1 S.card z.2 :=
    (hm.stronglyMeasurable.integral_kernel_prod_right' (κ := κ)).measurable
  exact (measurable_fst.mul hjMeas).stronglyMeasurable.integral_prod_left'.measurable.comp
    (spatialSubsetConfiguration_measurable S)

theorem finePairTimeSubsetMoment_square_integrable {d k : ℕ} [NeZero d]
    (hd : 3 ≤ d) {lo hi : ℝ} (hlo : 0 < lo) (S : Finset (Fin k)) (hS : 4 ≤ S.card) :
    Integrable (fun U : Fin k → Covariate d => finePairTimeSubsetMoment lo hi U S ^ 2)
      (fullSpatialPatchDesign d k) := by
  simp_rw [finePairTimeSubsetMoment_reindex (S := S)]
  exact spatial_subset_square_integrable_enumerated S
    (fun V => finePairTimeSubsetMoment lo hi V Finset.univ)
    (finePairTimeSubsetMoment_univ_square_integrable_and_le hd hS hlo).1

theorem finePairTimeSubsetMoment_square_integral_reindex {d k : ℕ}
    (lo hi : ℝ) (S : Finset (Fin k)) :
    (∫ U : Fin k → Covariate d, finePairTimeSubsetMoment lo hi U S ^ 2
      ∂fullSpatialPatchDesign d k) = (2 : ℝ) ^ (d * (k - S.card)) *
        ∫ V : Fin S.card → Covariate d, finePairTimeSubsetMoment lo hi V Finset.univ ^ 2
          ∂fullSpatialPatchDesign d S.card := by
  simp_rw [finePairTimeSubsetMoment_reindex (S := S)]
  exact spatial_subset_square_integral_enumerated (d := d) S
    fun V => finePairTimeSubsetMoment lo hi V Finset.univ

theorem finePairTimeSubsetMoment_square_integral_le {d k : ℕ} [NeZero d]
    (hd : 3 ≤ d) {lo hi : ℝ} (hlo : 0 < lo) (S : Finset (Fin k)) (hS : 4 ≤ S.card) :
    (∫ U : Fin k → Covariate d, finePairTimeSubsetMoment lo hi U S ^ 2
      ∂fullSpatialPatchDesign d k) ≤
      (2 : ℝ) ^ (d * (k - S.card)) *
        (hyperplaneSpatialMomentConstant d ^ S.card * (S.card : ℝ) ^ 4 * lo ^ (2 - (d : ℝ))) ^ 2 := by
  rw [finePairTimeSubsetMoment_square_integral_reindex]
  exact mul_le_mul_of_nonneg_left
    (finePairTimeSubsetMoment_univ_square_integrable_and_le hd hS (hi := hi) hlo).2 (by positivity)

end SpatialAndFineFieldL2

-- ============================================================================
-- 4. Row Annihilation, Source Row Families, Union Source, and Invariant Mass
-- ============================================================================

section SourceRowsAndInvariantMass
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable

lemma responseTensor_density_observable_zero {Z J ι : Type*}
    [MeasurableSpace Z] [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    [Fintype ι] [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (σ : Measure Z) [IsFiniteMeasure σ] (q : ℕ) (C : ℝ) (w : J → ℝ)
    (A : Z → ι → ι → ℝ)
    (hm : Measurable fun e : Z × (J × HighResponseMarkIndex ι q) => w e.2.1 * highResponseMarkWeight C q (A e.1) e.2.2)
    (hiW : Integrable (fun e : Z × (J × HighResponseMarkIndex ι q) => w e.2.1 * highResponseMarkWeight C q (A e.1) e.2.2)
      (σ.prod Measure.count))
    (hpos : 0 < signedMarkMass (σ.prod Measure.count)
      fun e : Z × (J × HighResponseMarkIndex ι q) => w e.2.1 * highResponseMarkWeight C q (A e.1) e.2.2)
    (F : Z × J → ℝ) (hF : Measurable F) (L : ℝ) (hbound : ∀ e, ‖F e‖ ≤ L) :
    (∫ e, absoluteActivation (σ.prod Measure.count)
      (fun e : Z × (J × HighResponseMarkIndex ι q) => w e.2.1 * highResponseMarkWeight C q (A e.1) e.2.2) e * F (e.1, e.2.1)
      ∂absoluteMarkLaw (σ.prod Measure.count)
        fun e : Z × (J × HighResponseMarkIndex ι q) => w e.2.1 * highResponseMarkWeight C q (A e.1) e.2.2) = 0 := by
  have hmF : Measurable fun e : Z × (J × HighResponseMarkIndex ι q) => F (e.1, e.2.1) :=
    hF.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hi := hiW.mul_bdd hmF.aestronglyMeasurable (Filter.Eventually.of_forall fun e => hbound (e.1, e.2.1))
  rw [absoluteMarkLaw_activation_integral _ _ hm hpos, integral_prod _ hi]
  simp only [integral_count]
  have he (ζ : Z) : (∑ h : J × HighResponseMarkIndex ι q,
      (w h.1 * highResponseMarkWeight C q (A ζ) h.2) * F (ζ, h.1)) = 0 := by
    have hz : (∑ r : HighResponseMarkIndex ι q, highResponseMarkWeight C q (A ζ) r) = 0 := by
      simpa only [mul_one, responseMatrixAction_zero_mass] using
        highResponseMark_action q C (A ζ) (fun _ => 0) (fun _ => 1)
    rw [Fintype.sum_prod_type]
    refine Finset.sum_eq_zero fun j _ => ?_
    simp only [show ∀ r : HighResponseMarkIndex ι q,
      w j * highResponseMarkWeight C q (A ζ) r * F (ζ, j) = (w j * F (ζ, j)) * highResponseMarkWeight C q (A ζ) r
      from fun _ => by ring, ← Finset.mul_sum, hz, mul_zero]
  simp only [he, integral_zero]

theorem highPacketAbsoluteLaw_density_observable_zero {Z ι : Type*}
    [MeasurableSpace Z] [Fintype ι] [DecidableEq ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (σ : Measure Z) [IsFiniteMeasure σ] (a b : ℝ) (m r D q : ℕ) (C : ℝ) (A : Z → ι → ι → ℝ)
    (hA : ∀ i j, Measurable fun ζ => A ζ i j) (hcost : Integrable (separatedMatrixCost A) σ)
    (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
    (F : Z × HighDensityMarkIndex m r D → ℝ) (hF : Measurable F)
    (L : ℝ) (hbound : ∀ e, ‖F e‖ ≤ L) :
    (∫ e, highPacketActivation σ a b m r D q C A e * F (e.1, e.2.1)
      ∂highPacketAbsoluteLaw σ a b m r D q C A) = 0 :=
  responseTensor_density_observable_zero σ q C (densityPacketWeight a b m r D) A
    (highPacketMarkWeight_measurable a b m r D q C A hA)
    (highPacketMarkWeight_integrable σ a b m r D q C A hA hcost) hpos F hF L hbound

theorem finePairRowMass_positive (d : ℕ) [NeZero d] (D : ℕ) (hD : 3 ≤ D)
    (M q : ℕ) (hq : 1 ≤ q) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (C : ℝ) (hC : 0 < C) (T₀ N : ℝ) (hT₀ : 0 < T₀) (hTN : T₀ < N)
    (i : FinePairRowTag) : 0 < finePairRowMass d D M q a b C T₀ N i := by
  have hr := lt_of_lt_of_le zero_lt_one (response_absolute_cost_ge_one q hq)
  have hc : 0 < 2*C^2 := mul_pos (by norm_num) (pow_pos hC _)
  have ho := ordinary_density_absolute_cost_pos a b ha hab D
  have hA₁ := finePairDistanceMatrix_l1_pos d D hD
  cases i
  · rw [finePairRowMass_unit]
    exact mul_pos (mul_pos (mul_pos ho hr) hc) (finePairUnitMatrix_l1_pos d D)
  · rw [finePairRowMass_coarse d D M q a b C T₀ N hT₀.le]
    exact mul_pos (mul_pos (mul_pos ho hr) hc) (mul_pos hA₁ (by positivity))
  · rw [finePairRowMass_fine d D M q a b C T₀ N hT₀.le hTN.le]
    exact mul_pos (mul_pos (mul_pos (fine_density_absolute_cost_pos a b ha hab M) hr) hc)
      (mul_pos hA₁ (by nlinarith))

abbrev SingletonRowMark (d D q : ℕ) := Unit × HighPacketMarkIndex (HighFrameIndex d D) D 1 D q

def singletonRowMass (d D q : ℕ) (a b C : ℝ) : ℝ :=
  highPacketMarkMass (Measure.dirac ()) a b D 1 D q C fun _ => finePairUnitMatrix d D

def singletonRowData (d k D q : ℕ) (a b C : ℝ) :
    HighUnionRowData d k D Unit fun _ => SingletonRowMark d D q where
  rowLaw := fun _ => highPacketAbsoluteLaw (Measure.dirac ()) a b D 1 D q C fun _ => finePairUnitMatrix d D
  rowMass := fun _ => singletonRowMass d D q a b C
  rowActivation := fun _ => highPacketActivation (Measure.dirac ()) a b D 1 D q C fun _ => finePairUnitMatrix d D
  rowIntercept := fun _ => highPacketIntercept a b D 1 D q
  rowSlope := fun _ _ e _ => highPacketSlope a b D 1 D q (fun _ _ => 1) e
  rowVector := fun _ e => (highResponseMarkAtom C q e.2.2).2
  rowTime := fun _ e => (highResponseMarkAtom 0 q e.2.2).1

theorem singletonRowMass_positive (d D q : ℕ) (hq : 1 ≤ q)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (C : ℝ) (hC : 0 < C) :
    0 < singletonRowMass d D q a b C := by
  rw [singletonRowMass, highPacketMarkMass_eq_variation (Measure.dirac ()) a b D 1 D q C
      (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _),
    highPacketSignedMeasure_totalVariation (Measure.dirac ()) a b D 1 D q C
      (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _)]
  simp only [separatedMatrixCost, integral_dirac]
  rw [densityPacketWeight_variation a b ha hab D 1 D (by norm_num)]
  have hp : densityPacketPrefactor a b 1 ≠ 0 := by
    simp only [densityPacketPrefactor, Nat.factorial_one, Nat.cast_one, one_div, inv_one, pow_one, one_mul]
    exact div_ne_zero (ha.trans hab).ne' (densityMargin_zero_ne a b ha hab)
  have hn : 0 < (derivativeOrder D : ℝ) := by exact_mod_cast (show 0 < derivativeOrder D by unfold derivativeOrder; omega)
  exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (abs_pos.mpr hp) (Real.cosh_pos _)) (pow_pos hn _))
    (lt_of_lt_of_le zero_lt_one (response_absolute_cost_ge_one q hq)))
    (mul_pos (by norm_num) (pow_pos hC _))) (finePairUnitMatrix_l1_pos d D)

theorem singletonRow_probability (d k D q : ℕ) (hq : 1 ≤ q)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (C : ℝ) (hC : 0 < C) :
    IsProbabilityMeasure ((singletonRowData d k D q a b C).rowLaw ()) :=
  highPacketAbsoluteLaw_probability (Measure.dirac ()) a b D 1 D q C (fun _ => finePairUnitMatrix d D)
    (fun _ _ => measurable_const) (integrable_const _) (singletonRowMass_positive d D q hq a b ha hab C hC)

theorem singletonRowMass_exponential_bound (d D q : ℕ) (hD : 1 ≤ D)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (C : ℝ) :
    singletonRowMass d D q a b C ≤
      (Real.exp (1+exteriorTau ((a+b)/(b-a))) * |b/densityMargin a b 0|) * D *
      Real.exp ((D : ℝ)*exteriorTau ((a+b)/(b-a))) *
      (∑ h : Fin (2*q+2), |responseWeight q h|) * (2*C^2) := by
  rw [singletonRowMass, highPacketMarkMass_eq_variation (Measure.dirac ()) a b D 1 D q C
    (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _)]
  have h := highPacketSignedMeasure_exponential_cost (Measure.dirac ()) a b ha hab D 1 D q
    (by norm_num) hD C (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _)
  simp only [pow_one, separatedMatrixCost, integral_dirac] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (finePairUnitMatrix_l1_le d D) (by positivity)).trans_eq (mul_one _))

def higherBandTargetScale (d r : ℕ) (N μ : ℝ) : ℝ :=
  N * (μ * (1 + Real.log N))^(((r : ℝ)-2)/(d : ℝ))

def higherBandFamilyTarget {D : ℕ} (i : Fin (D-2) × Bool) : ℕ := i.1.val + 3
def higherBandFamilyGuardDegree {D : ℕ} (M : ℕ) (i : Fin (D-2) × Bool) : ℕ :=
  if i.2 then M else D
def higherBandFamilyUpper (d : ℕ) {D : ℕ} (ℓ N μ : ℝ) (i : Fin (D-2) × Bool) : ℝ :=
  if i.2 then higherBandTargetScale d (higherBandFamilyTarget i) N μ
  else min ℓ (higherBandTargetScale d (higherBandFamilyTarget i) N μ)

def HigherBandFamilySelected (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) (i : Fin (D-2) × Bool) : Prop :=
  1 ≤ higherBandFamilyUpper d ℓ N μ i ∧
  (i.2 = true → ℓ < higherBandTargetScale d (higherBandFamilyTarget i) N μ) ∧
  higherBandFamilyTarget i ≤ higherBandFamilyGuardDegree M i ∧
  0 < higherBandRowMass d (higherBandFamilyTarget i) (higherBandFamilyGuardDegree M i) D q
    a b C lam ℓ (higherBandFamilyUpper d ℓ N μ i) i.2

abbrev HigherBandFamilyIndex (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) :=
  {i : Fin (D-2) × Bool // HigherBandFamilySelected d D M q a b C lam ℓ N μ i}

instance higherBandFamilyIndex_fintype (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    Fintype (HigherBandFamilyIndex d D M q a b C lam ℓ N μ) := by infer_instance

def HigherBandFamilyMark (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : HigherBandFamilyIndex d D M q a b C lam ℓ N μ) : Type :=
  HigherBandRowMark d (higherBandFamilyTarget i.val) (higherBandFamilyGuardDegree M i.val) D q i.val.2

instance higherBandFamilyMark_measurable (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : HigherBandFamilyIndex d D M q a b C lam ℓ N μ) :
    MeasurableSpace (HigherBandFamilyMark d D M q a b C lam ℓ N μ i) := by
  dsimp [HigherBandFamilyMark]; infer_instance

instance higherBandFamilyMark_standardBorel (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : HigherBandFamilyIndex d D M q a b C lam ℓ N μ) :
    StandardBorelSpace (HigherBandFamilyMark d D M q a b C lam ℓ N μ i) := by
  letI : StandardBorelSpace (HigherBandCarrier d (higherBandFamilyTarget i.val) i.val.2) :=
    higherBandCarrier_standardBorel _ _ _
  letI : StandardBorelSpace (HighPacketMarkIndex (HighFrameIndex d D)
      (higherBandFamilyGuardDegree M i.val) (higherBandFamilyTarget i.val) D q) := by infer_instance
  dsimp [HigherBandFamilyMark, higherBandFamilyMark_measurable]; infer_instance

def higherBandFamilyComponent (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : HigherBandFamilyIndex d D M q a b C lam ℓ N μ) :
    HighUnionRowData d k D Unit fun _ => HigherBandFamilyMark d D M q a b C lam ℓ N μ i :=
  higherBandRowData d k (higherBandFamilyTarget i.val) (higherBandFamilyGuardDegree M i.val) D q
    a b C lam ℓ (higherBandFamilyUpper d ℓ N μ i.val) i.val.2

def higherBandFamilyData (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    HighUnionRowData d k D (HigherBandFamilyIndex d D M q a b C lam ℓ N μ)
      (HigherBandFamilyMark d D M q a b C lam ℓ N μ) where
  rowLaw := fun i => (higherBandFamilyComponent d k D M q a b C lam ℓ N μ i).rowLaw ()
  rowMass := fun i => (higherBandFamilyComponent d k D M q a b C lam ℓ N μ i).rowMass ()
  rowActivation := fun i => (higherBandFamilyComponent d k D M q a b C lam ℓ N μ i).rowActivation ()
  rowIntercept := fun i => (higherBandFamilyComponent d k D M q a b C lam ℓ N μ i).rowIntercept ()
  rowSlope := fun j i => (higherBandFamilyComponent d k D M q a b C lam ℓ N μ i).rowSlope j ()
  rowVector := fun i => (higherBandFamilyComponent d k D M q a b C lam ℓ N μ i).rowVector ()
  rowTime := fun i => (higherBandFamilyComponent d k D M q a b C lam ℓ N μ i).rowTime ()

theorem higherBandFamily_target_bounds (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : HigherBandFamilyIndex d D M q a b C lam ℓ N μ) :
    3 ≤ higherBandFamilyTarget i.val ∧ higherBandFamilyTarget i.val ≤ D := by
  have hi := i.val.1.isLt; dsimp [higherBandFamilyTarget]; omega

theorem higherBandFamily_mass_positive (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : HigherBandFamilyIndex d D M q a b C lam ℓ N μ) :
    0 < (higherBandFamilyData d k D M q a b C lam ℓ N μ).rowMass i := i.property.2.2.2

theorem higherBand_zero_mass_signed_zero (d r m D q : ℕ) (a b C lam L T : ℝ)
    (hT : 1 ≤ T) (fine : Bool) (hz : higherBandRowMass d r m D q a b C lam L T fine = 0) :
    higherBandSignedRow d r m D q a b C lam L T fine = 0 := by
  letI := higherBandCarrierMeasure_finite d r L T hT fine
  rw [higherBandRowMass_eq_variation d r m D q a b C lam L T hT fine] at hz
  have hi := highPacketMarkWeight_integrable (higherBandCarrierMeasure d r L T fine) a b m r D q C
    (higherBandCarrierAmplitude d r D lam fine)
    (higherBandCarrierAmplitude_measurable d r D lam fine)
    (higherBandCarrierAmplitude_cost_integrable d r D lam L T hT fine)
  have hv : (higherBandSignedRow d r m D q a b C lam L T fine).variation univ ≠ ⊤ := by
    rw [higherBandSignedRow, highPacketSignedMeasure, Measure.variation_withDensityᵥ hi,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact ne_of_lt hi.hasFiniteIntegral
  exact VectorMeasure.variation_eq_zero.mp
    (Measure.measure_univ_eq_zero.mp ((ENNReal.toReal_eq_zero_iff _).mp hz |>.resolve_right hv))

def highUnionRowRestrict {d k D : ℕ} {I : Type*} {E : I → Type*} [∀ i, MeasurableSpace (E i)]
    (R : HighUnionRowData d k D I E) (i : I) : HighUnionRowData d k D Unit fun _ => E i where
  rowLaw := fun _ => R.rowLaw i
  rowMass := fun _ => R.rowMass i
  rowActivation := fun _ => R.rowActivation i
  rowIntercept := fun _ => R.rowIntercept i
  rowSlope := fun j _ => R.rowSlope j i
  rowVector := fun _ => R.rowVector i
  rowTime := fun _ => R.rowTime i

abbrev SourceRowIndex (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) :=
  FinePairRowTag ⊕ (Unit ⊕ HigherBandFamilyIndex d D M q a b C lam ℓ N μ)

def SourceRowMark (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    SourceRowIndex d D M q a b C lam ℓ N μ → Type
  | .inl p => FinePairRowMark d D M q p
  | .inr (.inl _) => SingletonRowMark d D q
  | .inr (.inr i) => HigherBandFamilyMark d D M q a b C lam ℓ N μ i

instance sourceRowMark_measurable (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) :
    MeasurableSpace (SourceRowMark d D M q a b C lam ℓ N μ i) := by
  cases i with
  | inl p => exact finePairRowMark_measurable d D M q p
  | inr i => cases i <;> dsimp [SourceRowMark] <;> infer_instance

instance sourceRowMark_standardBorel (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) :
    StandardBorelSpace (SourceRowMark d D M q a b C lam ℓ N μ i) := by
  cases i with
  | inl p => exact finePairRowMark_standardBorel d D M q p
  | inr i => cases i <;> dsimp [SourceRowMark, sourceRowMark_measurable] <;> infer_instance

def sourceRowComponent (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) →
      HighUnionRowData d k D Unit fun _ => SourceRowMark d D M q a b C lam ℓ N μ i
  | .inl p => highUnionRowRestrict (finePairRowData d k D M q a b C ℓ N) p
  | .inr (.inl _) => singletonRowData d k D q a b C
  | .inr (.inr i) => higherBandFamilyComponent d k D M q a b C lam ℓ N μ i

def sourceRowData (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    HighUnionRowData d k D (SourceRowIndex d D M q a b C lam ℓ N μ)
      (SourceRowMark d D M q a b C lam ℓ N μ) where
  rowLaw := fun i => (sourceRowComponent d k D M q a b C lam ℓ N μ i).rowLaw ()
  rowMass := fun i => (sourceRowComponent d k D M q a b C lam ℓ N μ i).rowMass ()
  rowActivation := fun i => (sourceRowComponent d k D M q a b C lam ℓ N μ i).rowActivation ()
  rowIntercept := fun i => (sourceRowComponent d k D M q a b C lam ℓ N μ i).rowIntercept ()
  rowSlope := fun j i => (sourceRowComponent d k D M q a b C lam ℓ N μ i).rowSlope j ()
  rowVector := fun i => (sourceRowComponent d k D M q a b C lam ℓ N μ i).rowVector ()
  rowTime := fun i => (sourceRowComponent d k D M q a b C lam ℓ N μ i).rowTime ()

theorem sourceRowTotalMass_positive (d k D M q : ℕ) (hq : 1 ≤ q)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (C : ℝ) (hC : 0 < C) (lam ℓ N μ : ℝ) :
    0 < highRowTotalMass (sourceRowData d k D M q a b C lam ℓ N μ).rowMass := by
  unfold highRowTotalMass
  refine (singletonRowMass_positive d D q hq a b ha hab C hC).trans_le
    (Finset.single_le_sum (f := (sourceRowData d k D M q a b C lam ℓ N μ).rowMass)
      (fun i _ => ?_) (Finset.mem_univ (Sum.inr (Sum.inl ()))))
  cases i with
  | inl p => exact finePairRowMass_nonneg d D M q a b C ℓ N p
  | inr i =>
    cases i with
    | inl _ => exact signedMarkMass_nonneg _ _
    | inr i => exact (higherBandFamily_mass_positive d k D M q a b C lam ℓ N μ i).le

structure HighUnionSourceGuards {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] (C : ModelConstants d) (M Cfr : ℝ)
    (R : HighUnionRowData d k F I E) : Prop where
  resolution : highCenterResolutionThreshold C ≤ M
  frame : 1 ≤ Cfr
  row_probability : ∀ i, IsProbabilityMeasure (R.rowLaw i)
  mass_nonneg : ∀ i, 0 ≤ R.rowMass i
  total_positive : 0 < highRowTotalMass R.rowMass
  activation_measurable : ∀ i, Measurable (R.rowActivation i)
  activation_bound : ∀ i e, |R.rowActivation i e| ≤ R.rowMass i
  activation_centered : ∀ i, (∫ e, R.rowActivation i e ∂(R.rowLaw i)) = 0
  slope_measurable : ∀ j i, Measurable fun ex : E i × Covariate d => R.rowSlope j i ex.1 ex.2
  slope_integrable : ∀ j x i, Integrable (fun e => R.rowSlope j i e x) (R.rowLaw i)
  slope_centered : ∀ j x i, (∫ e, R.rowSlope j i e x ∂(R.rowLaw i)) = 0
  intercept_measurable : ∀ i, Measurable (R.rowIntercept i)
  intercept_interval : ∀ i e, R.rowIntercept i e ∈
    Icc (C.densityLower + 1/M) (C.densityUpper - 1/M)
  row_reset_interval : ∀ j i e x v, v ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M) →
    R.rowSlope j i e x * v + R.rowIntercept i e ∈
      Icc (C.densityLower+1/M) (C.densityUpper-1/M)
  vector_measurable : ∀ i γ, Measurable fun e => R.rowVector i e γ
  time_measurable : ∀ i, Measurable (R.rowTime i)
  vector_ball : ∀ i e, (∑ γ, |R.rowVector i e γ|) ≤ Cfr⁻¹
  time_interval : ∀ i e, R.rowTime i e ∈ Icc (0 : ℝ) 1

section UnionSource
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)] [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (C : ModelConstants d) (R : HighUnionRowData d k F I E)

def highUnionVacuum : HighRawState d k F := ((fun _ => 1), 0)

def highUnionSourceState
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E)) :
    HighRawState d k F :=
  highUnionMarkedState R (fun i j => j ∈ highNeighborLabels d k i) (highCenterMix C)
    highUnionVacuum h

def highUnionSourceDensity
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (x : Covariate d) : ℝ := (highUnionSourceState C R h).1 x

def highUnionSourceMass
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E)) : ℝ :=
  ∫ x, highUnionSourceDensity C R h x ∂cubeVolume d

variable {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
include G

theorem highUnionSourceLaw_probability : IsProbabilityMeasure (highUnionLaw R (highCenterMix C)) := by
  letI := G.row_probability
  exact highUnionLaw_probability R G.mass_nonneg G.total_positive _
    (highCenterMix_mem C).1.le (highCenterMix_mem C).2.le

lemma highUnionSource_reset_interval (j : HighWindowLabels d k) (e : HighUnionMark E)
    (x : Covariate d) (v : ℝ) (hv : v ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M)) :
    highUnionSlope R j e x * v + highUnionIntercept R (highCenterMix C) e ∈
      Icc (C.densityLower+1/M) (C.densityUpper-1/M) := by
  letI := G.row_probability
  exact highCenteredRowUnion_reset_source_legal C R.rowLaw R.rowMass
    G.mass_nonneg G.total_positive (fun i e => R.rowSlope j i e x) R.rowIntercept
    G.intercept_measurable M G.resolution G.intercept_interval
    (fun i e v hv => G.row_reset_interval j i e x v hv) e v hv

lemma highUnionSource_vacuum_interval :
    (1 : ℝ) ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M) := by
  have hm := highCenterResolution_guards C M G.resolution
  have hr := highCenterRadius_le_margins C
  exact ⟨by linarith [highCenterRadius_pos C], by linarith [highCenterRadius_pos C]⟩

theorem highUnionSourceDensity_interval
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E)) (x : Covariate d) :
    highUnionSourceDensity C R h x ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M) :=
  highUnionHistory_density_interval R (highCenterMix C) _ _
    (highUnionSource_reset_interval C R G) (historyShapeLength _ h.1)
    (historyShapeCanonicalLabels _ h.1) highUnionVacuum
    (fun _ => highUnionSource_vacuum_interval C R G) h.2 x

theorem highUnionSourceState_coefficient_ball
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E)) :
    ∀ j, (∑ γ, |(highUnionSourceState C R h).2 j γ|) ≤ Cfr⁻¹ :=
  highUnionHistory_coefficient_ball R (highCenterMix C) Cfr
    (by linarith [G.frame]) G.vector_ball G.time_interval (historyShapeLength _ h.1)
    (historyShapeCanonicalLabels _ h.1) highUnionVacuum
    (fun _ => by simpa [highUnionVacuum] using inv_nonneg.mpr (by linarith [G.frame] : 0 ≤ Cfr)) h.2

theorem highUnionSourceDensity_joint_measurable [∀ i, StandardBorelSpace (E i)] :
    Measurable fun hx : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i)
      (HighUnionMark E) × Covariate d => highUnionSourceDensity C R hx.1 hx.2 :=
  highUnionMarkedDensity_joint_measurable R (fun i j => j ∈ highNeighborLabels d k i)
    G.slope_measurable G.intercept_measurable (highCenterMix C) highUnionVacuum measurable_const

theorem highUnionSourceMass_measurable [∀ i, StandardBorelSpace (E i)] :
    Measurable (highUnionSourceMass C R) :=
  highUnionMarkedMass_measurable R (fun i j => j ∈ highNeighborLabels d k i)
    G.slope_measurable G.intercept_measurable (highCenterMix C) highUnionVacuum measurable_const

theorem highUnionSourceMass_interval [∀ i, StandardBorelSpace (E i)]
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E)) :
    highUnionSourceMass C R h ∈ Icc (C.densityLower+1/M) (C.densityUpper-1/M) := by
  letI := cubeVolume_isProbability d
  exact boundedIntercept_mean_mem (cubeVolume d) (highUnionSourceDensity C R h)
    ((highUnionSourceDensity_joint_measurable C R G).comp (measurable_const.prodMk measurable_id))
    _ _ (highUnionSourceDensity_interval C R G h)

theorem highUnionSourceMass_fiber_mean_one [∀ i, StandardBorelSpace (E i)]
    (g : HistoryShape fun i j : HighWindowLabels d k => j ∉ highNeighborLabels d k i) :
    (∫ marks, highUnionSourceMass C R ⟨g, marks⟩
      ∂Measure.pi fun _ : Fin (historyShapeLength _ g) => highUnionLaw R (highCenterMix C)) = 1 := by
  letI := highUnionSourceLaw_probability C R G
  letI := cubeVolume_isProbability d
  letI := G.row_probability
  let f := fun mx : (Fin (historyShapeLength _ g) → HighUnionMark E) × Covariate d =>
    highUnionSourceDensity C R ⟨g, mx.1⟩ mx.2
  have hm : Measurable f := highUnionHistory_density_joint_measurable R G.slope_measurable
    G.intercept_measurable (highCenterMix C) (historyShapeLength _ g)
    (historyShapeCanonicalLabels _ g) highUnionVacuum measurable_const
  have hM0 : 0 < M := by linarith [(highCenterResolution_guards C M G.resolution).1]
  have hi : Integrable f ((Measure.pi fun _ : Fin (historyShapeLength _ g) =>
      highUnionLaw R (highCenterMix C)).prod (cubeVolume d)) :=
    (integrable_const C.densityUpper).mono' hm.aestronglyMeasurable <|
      Filter.Eventually.of_forall fun mx => by
        have hb := highUnionSourceDensity_interval C R G ⟨g, mx.1⟩ mx.2
        change ‖f mx‖ ≤ C.densityUpper
        rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [f]; linarith [hb.1, C.densityLower_pos, one_div_pos.mpr hM0])]
        exact hb.2.trans (by linarith [one_div_pos.mpr hM0])
  change (∫ marks, ∫ x, f (marks, x) ∂cubeVolume d
    ∂Measure.pi fun _ : Fin (historyShapeLength _ g) => highUnionLaw R (highCenterMix C)) = 1
  rw [integral_integral_swap hi]
  simp_rw [show ∀ x : Covariate d, (∫ marks, f (marks, x)
    ∂Measure.pi fun _ : Fin (historyShapeLength _ g) => highUnionLaw R (highCenterMix C)) = 1 from fun x =>
    highUnionHistory_density_mean_one R G.mass_nonneg G.total_positive
      (fun j x i => (G.slope_measurable j i).comp (measurable_id.prodMk measurable_const))
      G.slope_integrable G.slope_centered G.intercept_measurable _ _ G.intercept_interval
      (highCenterMix C) (highCenterMix_mem C).1.le (highCenterMix_mem C).2
      (historyShapeLength _ g) (historyShapeCanonicalLabels _ g) highUnionVacuum (fun _ => rfl) x]
  simp

theorem highUnionSourceMass_block_oscillation [∀ i, StandardBorelSpace (E i)] (hk : 2 ≤ k)
    (g : HistoryShape fun i j : HighWindowLabels d k => j ∉ highNeighborLabels d k i)
    (marks marks' : Fin (historyShapeLength _ g) → HighUnionMark E) (j : HighWindowLabels d k)
    (hMarks : ∀ i, historyShapeCanonicalLabels _ g i ≠ j → marks i = marks' i) :
    |highUnionSourceMass C R ⟨g, marks⟩ - highUnionSourceMass C R ⟨g, marks'⟩| ≤
      (2 / (k : ℝ))^d * (C.densityUpper-C.densityLower) := by
  have hM0 : 0 < M := by linarith [(highCenterResolution_guards C M G.resolution).1]
  refine (highAffineMarkedMass_block_oscillation d k hk
    (fun i j => j ∈ highNeighborLabels d k i) (highUnionSlope R)
    (fun _ e _ => highUnionIntercept R (highCenterMix C) e)
    (fun j e => (highUnionSlope_joint_measurable R G.slope_measurable j).comp
      (measurable_const.prodMk measurable_id)) (fun _ _ => measurable_const)
    (fun _ => highUnionResponseReset R) (C.densityLower+1/M) (C.densityUpper-1/M)
    (by linarith [(highUnionSource_vacuum_interval C R G).1, (highUnionSource_vacuum_interval C R G).2])
    (highUnionSource_reset_interval C R G) highUnionVacuum measurable_const
    (fun _ => highUnionSource_vacuum_interval C R G) g marks marks' j hMarks).trans ?_
  exact mul_le_mul_of_nonneg_left (by linarith [one_div_pos.mpr hM0]) (by positivity)

end UnionSource

theorem highUnionSourceState_append {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (R : HighUnionRowData d k F I E) (C : ModelConstants d)
    (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (e : HighUnionMark E) :
    highUnionSourceState C R (historyMarkedAppend
      (fun i j => j ∈ highNeighborLabels d k i)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h, e)) =
    highUnionRawUpdate R (highCenterMix C) j e (highUnionSourceState C R h) :=
  highUnionMarkedState_append R _ highUnionVacuum j h e

theorem highUnionSourceDensity_append_of_not_mem {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (R : HighUnionRowData d k F I E) (C : ModelConstants d)
    (j : HighWindowLabels d k)
    (h : HistoryMarked (fun i j => j ∈ highNeighborLabels d k i) (HighUnionMark E))
    (e : HighUnionMark E) (x : Covariate d) (hx : x ∉ highTorusPatch d k j) :
    highUnionSourceDensity C R (historyMarkedAppend
      (fun i j => j ∈ highNeighborLabels d k i)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h, e)) x =
    highUnionSourceDensity C R h x := by
  change (highUnionSourceState C R _).1 x = _
  rw [highUnionSourceState_append R C j h e]
  simp only [highUnionRawUpdate, rawPatchUpdate, affinePatchUpdate, ite_eq_right hx]; rfl

theorem finePairSourceRows_guards {d : ℕ} (C : ModelConstants d) [NeZero d]
    (k D M q : ℕ) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr : ℝ) (hCfr : 1 ≤ Cfr) (T₀ N : ℝ) (hT₀ : 0 < T₀) (hTN : T₀ < N) :
    HighUnionSourceGuards C (M : ℝ) Cfr
      (finePairRowData d k D M q (C.densityLower+1/(M : ℝ))
        (C.densityUpper-1/(M : ℝ)) Cfr T₀ N) := by
  let a := C.densityLower+1/(M : ℝ)
  let b := C.densityUpper-1/(M : ℝ)
  have hg := highCenterResolution_guards C (M : ℝ) hM
  have hM0 : (0 : ℝ) < M := by linarith [hg.1]
  have hr := highCenterRadius_pos C
  have hmargin := highCenterRadius_le_margins C
  have ha : 0 < a := by dsimp [a]; linarith [C.densityLower_pos, one_div_pos.mpr hM0]
  have hab : a < b := by dsimp [a, b]; linarith [hg.2]
  have hCf : 0 < Cfr := by linarith
  have hpos := finePairRowMass_positive d D hD M q hq a b ha hab Cfr hCf T₀ N hT₀ hTN
  exact {
    resolution := hM
    frame := hCfr
    row_probability := finePairRowLaw_probability d D M q a b Cfr T₀ N hpos
    mass_nonneg := finePairRowMass_nonneg d D M q a b Cfr T₀ N
    total_positive := Finset.sum_pos' (fun i _ => (hpos i).le) ⟨.unit, Finset.mem_univ _, hpos .unit⟩
    activation_measurable := finePairRowActivation_measurable d D M q a b Cfr T₀ N hpos
    activation_bound := finePairRowActivation_bound d D M q a b Cfr T₀ N
    activation_centered := finePairRowActivation_centered d D M q a b Cfr T₀ N hpos
    slope_measurable := finePairRowSlope_joint_measurable d k D M q a b
    slope_integrable := finePairRowSlope_integrable d k D M q a b Cfr T₀ N hpos ha hab
    slope_centered := finePairRowSlope_centered d k D M q a b Cfr T₀ N hpos ha hab
    intercept_measurable := finePairRowIntercept_measurable d D M q a b
    intercept_interval := finePairRowIntercept_mem d D M q a b hab.le
    row_reset_interval := finePairRow_reset_interval d k D M q a b ha hab
    vector_measurable := finePairRowVector_measurable d D M q Cfr
    time_measurable := finePairRowTime_measurable d D M q
    vector_ball := finePairRowVector_ball d D M q Cfr hCf
    time_interval := finePairRowTime_unit d D M q }

theorem higherBandSourceRow_guards {d : ℕ} (C : ModelConstants d)
    (k r m D q : ℕ) (hr : 1 ≤ r) (M Cfr lam L T : ℝ) (fine : Bool)
    (hM : highCenterResolutionThreshold C ≤ M) (hCfr : 1 ≤ Cfr) (hT : 1 ≤ T)
    (hpos : 0 < higherBandRowMass d r m D q (C.densityLower+1/M)
      (C.densityUpper-1/M) Cfr lam L T fine) :
    HighUnionSourceGuards C M Cfr
      (higherBandRowData d k r m D q (C.densityLower+1/M) (C.densityUpper-1/M) Cfr lam L T fine) := by
  let a := C.densityLower+1/M
  let b := C.densityUpper-1/M
  let σ := higherBandCarrierMeasure d r L T fine
  let A := higherBandCarrierAmplitude d r D lam fine
  let B := fun (j : HighWindowLabels d k) ζ (x : Covariate d) l =>
    higherBandCarrierFactor d r lam fine ζ l (highLocalCoordinates d k j x)
  letI := higherBandCarrierMeasure_finite d r L T hT fine
  have hA := higherBandCarrierAmplitude_measurable d r D lam fine
  have hc := higherBandCarrierAmplitude_cost_integrable d r D lam L T hT fine
  have hg := highCenterResolution_guards C M hM
  have hM0 : 0 < M := by linarith [hg.1]
  have ha : 0 < a := by dsimp [a]; linarith [C.densityLower_pos, one_div_pos.mpr hM0]
  have hab : a < b := by
    dsimp [a, b]
    linarith [hg.2, highCenterRadius_pos C, (highCenterRadius_le_margins C).1, (highCenterRadius_le_margins C).2]
  have hCf : 0 < Cfr := by linarith
  have hB (j) (l : Fin r) : Measurable fun ζx : HigherBandCarrier d r fine × Covariate d =>
      B j ζx.1 ζx.2 l :=
    (higherBandCarrierFactor_joint_measurable d r lam fine l).comp
      (measurable_fst.prodMk ((highLocalCoordinates_measurable d k j).comp measurable_snd))
  have hBb (j) (ζ : HigherBandCarrier d r fine) (x : Covariate d) (l : Fin r) : |B j ζ x l| ≤ 1 :=
    higherBandCarrierFactor_bound d r lam fine ζ l _ fun i =>
      (highLocalCoordinates_abs_le_one d k j x i).trans (by norm_num)
  have hBm (j) (x : Covariate d) (l : Fin r) : Measurable fun ζ => B j ζ x l :=
    (hB j l).comp (measurable_id.prodMk measurable_const)
  refine {
    resolution := hM
    frame := hCfr
    row_probability := fun _ => highPacketAbsoluteLaw_probability σ a b m r D q Cfr A hA hc hpos
    mass_nonneg := fun _ => hpos.le
    total_positive := by simpa [highRowTotalMass, higherBandRowData] using hpos
    activation_measurable := fun _ => absoluteActivation_measurable _ _
      (highPacketMarkWeight_measurable a b m r D q Cfr A hA)
    activation_bound := fun _ => higherBandRowActivation_bound d r m D q a b Cfr lam L T fine
    activation_centered := fun _ => highPacketActivation_centered σ a b m r D q Cfr A hA hc hpos
    slope_measurable := fun j _ =>
      ((measurable_of_countable fun h : HighPacketMarkIndex (HighFrameIndex d D) m r D q =>
        densityMargin a b (densityPacketAtom a b m r D h.1).1 / ((r : ℝ)*b)).comp
          (measurable_snd.comp measurable_fst)).mul
        (Finset.measurable_fun_sum _ fun l _ =>
          ((measurable_of_countable fun h : HighPacketMarkIndex (HighFrameIndex d D) m r D q =>
            (densityPacketAtom a b m r D h.1).2 l).comp (measurable_snd.comp measurable_fst)).mul
            ((hB j l).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
    slope_integrable := fun j x _ => highPacketSlope_integrable σ a b ha hab m r D q hr Cfr A hA hc hpos
      (fun ζ l => B j ζ x l) (hBm j x) fun ζ l => hBb j ζ x l
    slope_centered := fun j x _ => highPacketAbsoluteLaw_slope_integral_zero σ a b ha hab m r D q hr Cfr A hA hc hpos
      (fun ζ l => B j ζ x l) (hBm j x) fun ζ l => hBb j ζ x l
    intercept_measurable := fun _ => highPacketIntercept_measurable a b m r D q
    intercept_interval := fun _ e => (densityPacketAtom_mem a b hab.le m r D e.2.1).1
    row_reset_interval := fun j _ e x v hv => by
      have hh := localDensityReset_mem_interval a b ha hab r hr
        (densityPacketAtom a b m r D e.2.1).1 (densityPacketAtom_mem a b hab.le m r D e.2.1).1
        (densityPacketAtom a b m r D e.2.1).2 (densityPacketAtom_mem a b hab.le m r D e.2.1).2
        (fun _ : Unit => v) (fun _ l => B j e.1 x l) () hv fun l => hBb j e.1 x l
      convert hh using 1 <;>
        dsimp [higherBandRowData, highPacketSlope, highPacketIntercept, localDensityReset] <;> ring
    vector_measurable := fun _ γ =>
      (measurable_of_countable fun h : HighPacketMarkIndex (HighFrameIndex d D) m r D q =>
        (highResponseMarkAtom Cfr q h.2).2 γ).comp measurable_snd
    time_measurable := fun _ =>
      (measurable_of_countable fun h : HighPacketMarkIndex (HighFrameIndex d D) m r D q =>
        (highResponseMarkAtom (ι := HighFrameIndex d D) 0 q h.2).1).comp measurable_snd
    vector_ball := fun _ _ => covarianceAtom_mem_ball Cfr hCf _ _ _ _
    time_interval := fun _ _ => responseNode_mem_unit q _ }

theorem higherBandRow_density_observable_zero (d r m D q : ℕ)
    (a b Cfr lam L T : ℝ) (fine : Bool) (hT : 1 ≤ T)
    (hpos : 0 < higherBandRowMass d r m D q a b Cfr lam L T fine)
    (H : HigherBandCarrier d r fine × HighDensityMarkIndex m r D → ℝ)
    (hH : Measurable H) (B : ℝ) (hB : ∀ z, ‖H z‖ ≤ B) :
    (∫ e, higherBandRowActivation d r m D q a b Cfr lam L T fine e * H (e.1, e.2.1)
      ∂higherBandRowLaw d r m D q a b Cfr lam L T fine) = 0 := by
  letI := higherBandCarrierMeasure_finite d r L T hT fine
  exact highPacketAbsoluteLaw_density_observable_zero _ a b m r D q Cfr _
    (higherBandCarrierAmplitude_measurable d r D lam fine)
    (higherBandCarrierAmplitude_cost_integrable d r D lam L T hT fine) hpos H hH B hB

abbrev FinePairRowDensityMark (d D M : ℕ) : FinePairRowTag → Type
  | .unit => Unit × HighDensityMarkIndex D 2 D
  | .coarse => (ℝ × FinePairFieldMark d) × HighDensityMarkIndex D 2 D
  | .fine => (ℝ × FinePairFieldMark d) × FinePairDensityIndex M

instance (d D M : ℕ) (i : FinePairRowTag) : MeasurableSpace (FinePairRowDensityMark d D M i) := by
  cases i <;> dsimp only [FinePairRowDensityMark] <;> infer_instance

def finePairRowDensityProj (d D M q : ℕ) (i : FinePairRowTag) :
    FinePairRowMark d D M q i → FinePairRowDensityMark d D M i := by
  cases i <;> exact fun e => (e.1, e.2.1)

def finePairRowWithResponse (d D M q : ℕ) (i : FinePairRowTag)
    (r : HighResponseMarkIndex (HighFrameIndex d D) q) :
    FinePairRowDensityMark d D M i → FinePairRowMark d D M q i := by
  cases i <;> exact fun e => (e.1, (e.2, r))

theorem finePairRowWithResponse_measurable (d D M q : ℕ) (i : FinePairRowTag)
    (r : HighResponseMarkIndex (HighFrameIndex d D) q) :
    Measurable (finePairRowWithResponse d D M q i r) := by
  cases i <;> exact measurable_fst.prodMk (measurable_snd.prodMk measurable_const)

theorem finePairRow_density_observable_zero (d : ℕ) [NeZero d] (D M q : ℕ)
    (a b C T₀ N : ℝ) (hpos : ∀ i, 0 < finePairRowMass d D M q a b C T₀ N i)
    (i : FinePairRowTag) (F : FinePairRowDensityMark d D M i → ℝ) (hF : Measurable F)
    (L : ℝ) (hL : ∀ e, ‖F e‖ ≤ L) :
    (∫ e, finePairRowActivation d D M q a b C T₀ N i e *
      F (finePairRowDensityProj d D M q i e) ∂finePairRowLaw d D M q a b C T₀ N i) = 0 := by
  cases i
  · exact highPacketAbsoluteLaw_density_observable_zero (Measure.dirac ()) a b D 2 D q C
      (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _)
      (hpos .unit) F hF L hL
  · exact highPacketAbsoluteLaw_density_observable_zero (finePairTimeFieldMeasure d 0 T₀)
      a b D 2 D q C _ (finePairTimeMatrix_measurable d _)
      (finePairTimeMatrix_cost_integrable d 0 T₀ _) (hpos .coarse) F hF L hL
  · exact responseTensor_density_observable_zero (finePairTimeFieldMeasure d T₀ N)
      q C (finePairDensityWeight a b M) (finePairTimeMatrix d (finePairDistanceMatrix d D))
      (finePairPacketWeight_measurable a b M q C _ (finePairTimeMatrix_measurable d _))
      (finePairPacketWeight_integrable _ a b M q C _ (finePairTimeMatrix_measurable d _)
        (finePairTimeMatrix_cost_integrable d T₀ N _))
      (hpos .fine) F hF L hL

theorem highUnionSource_bounded_action {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] (C : ModelConstants d)
    (R : HighUnionRowData d k F I E) {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
    (hpos : ∀ i, 0 < R.rowMass i)
    (Fobs : HighUnionMark E → ℝ) (hF : Measurable Fobs)
    (L : ℝ) (hL : ∀ e, ‖Fobs e‖ ≤ L) :
    (∫ e, highUnionActivation R (highCenterMix C) e * Fobs e
      ∂highUnionLaw R (highCenterMix C)) =
      ∑ i, ∫ e, R.rowActivation i e * Fobs (Sum.inl ⟨i, e⟩) ∂(R.rowLaw i) := by
  letI := G.row_probability
  have hi (i : I) : Integrable (R.rowActivation i) (R.rowLaw i) :=
    (integrable_const (R.rowMass i)).mono' (G.activation_measurable i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using G.activation_bound i e)
  have hUi := highRowUnionActivation_integrable R.rowLaw R.rowMass R.rowActivation G.activation_measurable hi
  have hUFi := hUi.mul_bdd (hF.comp measurable_inl).aestronglyMeasurable
    (Filter.Eventually.of_forall fun e => hL (Sum.inl e))
  rw [highUnionActivation, highUnionLaw, highCenteredRowUnionActivation, highCenteredRowUnionLaw,
    balancedActivation_integral _ _ (highCenterMix_mem C).1 (highCenterMix_mem C).2.le _
      (highRowUnionActivation_measurable _ _ G.activation_measurable) Fobs hF hUFi]
  exact highRowUnionActivation_action R.rowLaw R.rowMass hpos G.total_positive
    R.rowActivation G.activation_measurable (fun e => Fobs (Sum.inl e))
    (hF.comp measurable_inl) fun i => (hi i).mul_bdd
      (hF.comp (measurable_inl.comp (rowSigmaMk_measurable i))).aestronglyMeasurable
        (Filter.Eventually.of_forall fun e => hL (Sum.inl ⟨i, e⟩))

theorem historyMarkedPrior_invariant_law {J : Type*} [Fintype J] [LinearOrder J]
    (dependent : J → J → Prop)
    (hrefl : ∀ j, dependent j j) (hsymm : ∀ ⦃i j⦄, dependent i j → dependent j i)
    (Δ : ℕ) (hΔ : 1 ≤ Δ) (hlabels : ∀ j, (dependentLabelFinset dependent j).card ≤ Δ)
    (T B : ℝ) (hT : 0 ≤ T) (hB : 0 ≤ B)
    {E X : Type*} [MeasurableSpace E] [StandardBorelSpace E] [MeasurableSpace X]
    (π : Measure E) [IsProbabilityMeasure π] (a : E → ℝ) (ha : Measurable a)
    (hcenter : ∫ e, a e ∂π = 0) (habound : ∀ e, |a e| ≤ B)
    (hsmall : T * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2))
    (f : HistoryMarked dependent E → X) (hf : Measurable f)
    (hkill : ∀ j h S, MeasurableSet S →
      ∫ e, (S.indicator fun _ : X => (1 : ℝ))
        (f (historyMarkedAppend dependent hsymm j (h, e))) * a e ∂π = 0)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    Measure.map f (historyMarkedPrior dependent Δ t π a) =
      Measure.map f (historyMarkedReference dependent Δ π) := by
  have hi : Integrable a π := Integrable.of_bound ha.aestronglyMeasurable B
    (Eventually.of_forall fun e => by simpa only [Real.norm_eq_abs] using habound e)
  have hs : t * B / historyReferenceRho Δ ≤ 1 / (2 + 8 * (Δ : ℝ) ^ 2) :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht.2 hB) (historyReferenceRho_pos Δ).le).trans hsmall
  let := historyMarkedPrior_probability dependent hrefl hsymm Δ hΔ hlabels t B ht.1 hB π a hi hcenter habound hs
  let := historyMarkedReference_probability dependent hrefl hsymm Δ hΔ hlabels π
  ext S hS
  rw [Measure.map_apply hf hS, Measure.map_apply hf hS]
  refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 ?_
  let F := (f ⁻¹' S).indicator fun _ : HistoryMarked dependent E => (1 : ℝ)
  have he := historyMarkedPrior_invariant_observable dependent hrefl hsymm Δ hΔ hlabels T B hT hB
    π a ha habound hsmall F ((measurable_const : Measurable fun _ : HistoryMarked dependent E => (1 : ℝ)).indicator (hf hS))
    1 zero_le_one (fun h => by by_cases hh : f h ∈ S <;> simp [F, hh])
    (fun j h => by
      simp_rw [show ∀ h : HistoryMarked dependent E, F h = S.indicator (fun _ : X => (1 : ℝ)) (f h) from
        fun h => by by_cases hh : f h ∈ S <;> simp [F, hh]]
      exact hkill j h S hS) t ht
  change (∫ h, (f ⁻¹' S).indicator (1 : HistoryMarked dependent E → ℝ) h ∂historyMarkedPrior dependent Δ t π a) =
      ∫ h, (f ⁻¹' S).indicator (1 : HistoryMarked dependent E → ℝ) h ∂historyMarkedReference dependent Δ π at he
  rwa [integral_indicator_one (hf hS), integral_indicator_one (hf hS)] at he

def highHistoryMassParameter (d k : ℕ) (a b : ℝ) : ℝ :=
  (k : ℝ)^d * ((2 / (k : ℝ))^d * (b-a))^2 / 8

theorem highHistoryMassParameter_pos (d k : ℕ) (a b : ℝ) (hk : 0 < k) (hab : a < b) :
    0 < highHistoryMassParameter d k a b := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  unfold highHistoryMassParameter; positivity

theorem highHistoryMassParameter_eq (d k : ℕ) (a b : ℝ) (hk : 0 < k) :
    highHistoryMassParameter d k a b = (2 : ℝ)^(2*d) * (b-a)^2 / (8 * (k : ℝ)^d) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hp : (k : ℝ)^d ≠ 0 := ne_of_gt (pow_pos hkR d)
  unfold highHistoryMassParameter
  rw [div_pow, mul_pow, Nat.mul_comm 2 d, pow_mul]; field_simp

theorem highNeighbor_dependency_card (d k : ℕ) [NeZero k] (j : HighWindowLabels d k) :
    (dependentLabelFinset (fun i j => j ∈ highNeighborLabels d k i) j).card ≤ 3^d := by
  rw [show dependentLabelFinset (fun i j => j ∈ highNeighborLabels d k i) j = highNeighborLabels d k j by
    ext i; simp [dependentLabelFinset]]
  exact highNeighborLabels_card_le d k j

theorem massPowerTilt_abs_event_eq_of_massLaw {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) (m : Ω → ℝ) (hm : Measurable m) (n : ℕ)
    (hlaw : μ.map m = ν.map m) (ε : ℝ) :
    (massPowerTilt μ m n).real {ω | ε < |m ω - 1|} =
      (massPowerTilt ν m n).real {ω | ε < |m ω - 1|} := by
  have hS : MeasurableSet {z : ℝ | ε < |z - 1|} :=
    measurableSet_lt measurable_const (measurable_id.sub measurable_const).abs
  have he := congrArg (fun μ' : Measure ℝ => μ' {z : ℝ | ε < |z - 1|})
    (massPowerTilt_massLaw_eq μ ν m hm n hlaw)
  rw [Measure.map_apply hm hS, Measure.map_apply hm hS] at he
  exact congrArg ENNReal.toReal he

end SourceRowsAndInvariantMass

-- ============================================================================
-- 5. Lower Endpoint and Rounded Lower Saddle Allocation
-- ============================================================================

section LowerEndpointAndSaddle

def densityIntervalExponent (a b : ℝ) : ℝ :=
  Real.log ((Real.sqrt b + Real.sqrt a) / (Real.sqrt b - Real.sqrt a))

def shrunkDensityExponent (a b : ℝ) (M : ℕ) : ℝ :=
  densityIntervalExponent (a + (M : ℝ)⁻¹) (b - (M : ℝ)⁻¹)

theorem densityIntervalExponent_pos {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < densityIntervalExponent a b := by
  have hsa := Real.sqrt_pos.2 ha
  exact Real.log_pos ((one_lt_div (sub_pos.2 (Real.sqrt_lt_sqrt ha.le hab))).2 (by linarith))

def LowerExponentControl (τM : ℕ → ℝ) (τ Cτ : ℝ) : Prop :=
  ∀ᶠ M : ℕ in atTop, τ ≤ τM M ∧ (τM M - τ) * (M : ℝ) ≤ Cτ

theorem exists_actual_lowerExponentControl {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ Cτ : ℝ, 0 ≤ Cτ ∧ LowerExponentControl (shrunkDensityExponent a b)
      (densityIntervalExponent a b) Cτ := by
  have hb : 0 < b := ha.trans hab
  have hden : Real.sqrt b - Real.sqrt a ≠ 0 := (sub_pos.2 (Real.sqrt_lt_sqrt ha.le hab)).ne'
  have hf : DifferentiableAt ℝ (fun t : ℝ => densityIntervalExponent (a + t) (b - t)) 0 := by
    unfold densityIntervalExponent
    refine DifferentiableAt.log (DifferentiableAt.div ?_ ?_ (by simpa using hden))
      (by simpa using (by positivity : (Real.sqrt b + Real.sqrt a) / (Real.sqrt b - Real.sqrt a) ≠ 0))
    · exact (((differentiableAt_const b).sub differentiableAt_id).sqrt (by simpa using hb.ne')).add
        (((differentiableAt_const a).add differentiableAt_id).sqrt (by simpa using ha.ne'))
    · exact (((differentiableAt_const b).sub differentiableAt_id).sqrt (by simpa using hb.ne')).sub
        (((differentiableAt_const a).add differentiableAt_id).sqrt (by simpa using ha.ne'))
  obtain ⟨K, hK⟩ := hf.isBigO_sub.bound
  have ht : Tendsto (fun M : ℕ => (M : ℝ)⁻¹) atTop (𝓝 0) := tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  filter_upwards [ht.eventually hK, ht.eventually (gt_mem_nhds (by linarith : 0 < (b - a) / 2)),
    eventually_ge_atTop (1 : ℕ)] with M hbound hMsmall hM
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hM
  have hMinv : 0 ≤ (M : ℝ)⁻¹ := inv_nonneg.2 hMpos.le
  have hsh : a + (M : ℝ)⁻¹ < b - (M : ℝ)⁻¹ := by linarith
  have hmono : densityIntervalExponent a b ≤ shrunkDensityExponent a b M := by
    have hsa := Real.sqrt_pos.2 ha
    have hden0 := sub_pos.2 (Real.sqrt_lt_sqrt ha.le hab)
    have hAA : Real.sqrt a ≤ Real.sqrt (a + (M : ℝ)⁻¹) := Real.sqrt_le_sqrt (by linarith)
    have hBB : Real.sqrt (b - (M : ℝ)⁻¹) ≤ Real.sqrt b := Real.sqrt_le_sqrt (by linarith)
    unfold shrunkDensityExponent densityIntervalExponent
    refine Real.log_le_log (by positivity) ((div_le_div_iff₀ hden0
      (sub_pos.2 (Real.sqrt_lt_sqrt (by linarith) hsh))).2 ?_)
    nlinarith [mul_le_mul hAA hBB (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
  refine ⟨hmono, ?_⟩
  simp only [Real.norm_eq_abs, sub_zero, add_zero, abs_of_nonneg hMinv] at hbound
  change |shrunkDensityExponent a b M - densityIntervalExponent a b| ≤ K * (M : ℝ)⁻¹ at hbound
  rw [abs_of_nonneg (sub_nonneg.2 hmono)] at hbound
  have hmul := mul_le_mul_of_nonneg_right hbound hMpos.le
  rw [mul_assoc, inv_mul_cancel₀ hMpos.ne', mul_one] at hmul
  exact hmul.trans (le_max_left _ _)

def lowerSaddleM (m x : ℝ) : ℕ := Nat.ceil (m * Real.sqrt (Real.log x))
def lowerSaddleD (d m x : ℝ) : ℕ := Nat.ceil ((d + 8) / 4 * lowerSaddleM m x)
def lowerSaddleOmegaZero (m θ C x : ℝ) : ℝ :=
  θ * lowerSaddleM m x - Real.log (lowerSaddleM m x) + C
def lowerSaddleGridBase (d m θ C x : ℝ) : ℝ :=
  Real.exp ((Real.log x + lowerSaddleOmegaZero m θ C x) / d)
def lowerSaddleGrid (d m θ C x : ℝ) : ℕ := Nat.ceil (lowerSaddleGridBase d m θ C x)
def lowerSaddleH (d m θ C x : ℝ) : ℝ := (lowerSaddleGrid d m θ C x : ℝ)⁻¹
def lowerSaddleMu (d m θ C x : ℝ) : ℝ := x * (lowerSaddleH d m θ C x) ^ d
def lowerSaddleOmega (d m θ C x : ℝ) : ℝ :=
  d * Real.log (lowerSaddleGrid d m θ C x) - Real.log x

lemma lowerSaddleM_rounding {m x : ℝ} (hm : 0 ≤ m) :
    m * Real.sqrt (Real.log x) ≤ (lowerSaddleM m x : ℝ) ∧
      (lowerSaddleM m x : ℝ) < m * Real.sqrt (Real.log x) + 1 :=
  ⟨Nat.le_ceil _, Nat.ceil_lt_add_one (mul_nonneg hm (Real.sqrt_nonneg _))⟩

theorem lowerSaddleM_tendsto_atTop {m : ℝ} (hm : 0 < m) :
    Tendsto (fun x : ℝ => (lowerSaddleM m x : ℝ)) atTop atTop :=
  tendsto_atTop_mono (fun _ => (lowerSaddleM_rounding hm.le).1) (tendsto_sqrt_log_atTop.const_mul_atTop hm)

theorem lowerSaddleM_nat_tendsto_atTop {m : ℝ} (hm : 0 < m) :
    Tendsto (lowerSaddleM m) atTop atTop :=
  tendsto_natCast_atTop_iff.1 (lowerSaddleM_tendsto_atTop hm)

lemma lowerSaddleM_div_sqrt_log_limit {m : ℝ} (hm : 0 < m) :
    Tendsto (fun x : ℝ => (lowerSaddleM m x : ℝ) / Real.sqrt (Real.log x)) atTop (𝓝 m) := by
  have hu : Tendsto (fun x : ℝ => 1 / Real.sqrt (Real.log x)) atTop (𝓝 0) := by
    simpa only [one_div] using! tendsto_sqrt_log_atTop.inv_tendsto_atTop
  have herr : Tendsto (fun x : ℝ => ((lowerSaddleM m x : ℝ) - m * Real.sqrt (Real.log x)) /
      Real.sqrt (Real.log x)) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hu
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x _
      exact div_nonneg (sub_nonneg.2 (lowerSaddleM_rounding hm.le).1) (Real.sqrt_nonneg _)
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x _
      exact div_le_div_of_nonneg_right (by linarith [(lowerSaddleM_rounding (x := x) hm.le).2]) (Real.sqrt_nonneg _)
  have hh := (tendsto_const_nhds (x := m)).add herr
  simp only [add_zero] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hz : Real.sqrt (Real.log x) ≠ 0 := (Real.sqrt_pos.2 (Real.log_pos hx)).ne'
  field_simp; ring

lemma lowerSaddleM_sq_div_log_limit {m : ℝ} (hm : 0 < m) :
    Tendsto (fun x : ℝ => (lowerSaddleM m x : ℝ) ^ 2 / Real.log x) atTop (𝓝 (m ^ 2)) := by
  refine ((lowerSaddleM_div_sqrt_log_limit hm).pow 2).congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  simp only [div_pow, Real.sq_sqrt (Real.log_pos hx).le]

lemma lowerSaddleOmegaZero_div_M_limit {m : ℝ} (hm : 0 < m) (θ C : ℝ) :
    Tendsto (fun x : ℝ => lowerSaddleOmegaZero m θ C x / lowerSaddleM m x) atTop (𝓝 θ) := by
  have ht := lowerSaddleM_tendsto_atTop hm
  have hc : Tendsto (fun x : ℝ => C / lowerSaddleM m x) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using ht.inv_tendsto_atTop.const_mul C
  have hh := ((tendsto_const_nhds (x := θ)).sub
    (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp ht)).add hc
  simp only [sub_zero, add_zero] at hh
  refine hh.congr' ?_
  filter_upwards [ht.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  simp only [Function.comp_apply, id_eq]; unfold lowerSaddleOmegaZero; field_simp

theorem lowerSaddleGrid_positive (d m θ C x : ℝ) : 0 < (lowerSaddleGrid d m θ C x : ℝ) :=
  (Real.exp_pos _).trans_le (Nat.le_ceil _)

theorem lowerSaddleH_positive (d m θ C x : ℝ) : 0 < lowerSaddleH d m θ C x :=
  inv_pos.2 (lowerSaddleGrid_positive d m θ C x)

lemma lowerSaddleGridBase_tendsto_atTop {d m θ : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C : ℝ) :
    Tendsto (lowerSaddleGridBase d m θ C) atTop atTop := by
  have ht := lowerSaddleM_tendsto_atTop hm
  have hω0 : Tendsto (lowerSaddleOmegaZero m θ C) atTop atTop := by
    refine (ht.atTop_mul_pos hθ (lowerSaddleOmegaZero_div_M_limit hm θ C)).congr' ?_
    filter_upwards [ht.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
    exact mul_div_cancel₀ _ hx.ne'
  exact Real.tendsto_exp_atTop.comp ((Real.tendsto_log_atTop.atTop_add_atTop hω0).atTop_div_const hd)

theorem lowerSaddleGrid_tendsto_atTop {d m θ : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C : ℝ) :
    Tendsto (fun x : ℝ => (lowerSaddleGrid d m θ C x : ℝ)) atTop atTop :=
  tendsto_atTop_mono (fun _ => Nat.le_ceil _) (lowerSaddleGridBase_tendsto_atTop hd hm hθ C)

lemma lowerSaddleOmega_rounding_limit {d m θ : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C : ℝ) :
    Tendsto (fun x : ℝ => lowerSaddleOmega d m θ C x - lowerSaddleOmegaZero m θ C x) atTop (𝓝 0) := by
  have hb := lowerSaddleGridBase_tendsto_atTop hd hm hθ C
  have hu : Tendsto (fun x : ℝ => 1 / lowerSaddleGridBase d m θ C x) atTop (𝓝 0) := by
    simpa only [one_div] using! hb.inv_tendsto_atTop
  have herr : Tendsto (fun x : ℝ => ((lowerSaddleGrid d m θ C x : ℝ) - lowerSaddleGridBase d m θ C x) /
      lowerSaddleGridBase d m θ C x) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => div_nonneg (sub_nonneg.2 (Nat.le_ceil _)) (Real.exp_pos _).le)
      (Eventually.of_forall fun x => div_le_div_of_nonneg_right ?_ (Real.exp_pos _).le) hu
    have hh := Nat.ceil_lt_add_one (show 0 ≤ lowerSaddleGridBase d m θ C x from (Real.exp_pos _).le)
    change (lowerSaddleGrid d m θ C x : ℝ) < lowerSaddleGridBase d m θ C x + 1 at hh
    linarith
  have hdiv : Tendsto (fun x : ℝ => (lowerSaddleGrid d m θ C x : ℝ) / lowerSaddleGridBase d m θ C x) atTop (𝓝 1) := by
    have hh := (tendsto_const_nhds (x := (1 : ℝ))).add herr
    simp only [add_zero] at hh
    exact hh.congr fun x => by have : lowerSaddleGridBase d m θ C x ≠ 0 := (Real.exp_pos _).ne'; field_simp; ring
  have hh := ((Real.continuousAt_log one_ne_zero).tendsto.comp hdiv).const_mul d
  simp only [Real.log_one, mul_zero] at hh
  refine hh.congr fun x => ?_
  simp only [Function.comp_apply]
  rw [Real.log_div (lowerSaddleGrid_positive d m θ C x).ne' (show lowerSaddleGridBase d m θ C x ≠ 0 from (Real.exp_pos _).ne')]
  unfold lowerSaddleGridBase lowerSaddleOmega; rw [Real.log_exp]; field_simp; ring

theorem lowerSaddleMu_eq_exp {d m θ C x : ℝ} (hx : 0 < x) :
    lowerSaddleMu d m θ C x = Real.exp (-lowerSaddleOmega d m θ C x) := by
  unfold lowerSaddleMu
  nth_rw 1 [← Real.exp_log hx]
  rw [Real.rpow_def_of_pos (lowerSaddleH_positive d m θ C x), ← Real.exp_add]
  congr 1; unfold lowerSaddleH lowerSaddleOmega; rw [Real.log_inv]; ring

lemma lowerSaddleH_eq_exp {d m θ C x : ℝ} (hd : d ≠ 0) :
    lowerSaddleH d m θ C x = Real.exp (-(Real.log x + lowerSaddleOmega d m θ C x) / d) := by
  unfold lowerSaddleH lowerSaddleOmega
  rw [show -(Real.log x + (d * Real.log (lowerSaddleGrid d m θ C x) - Real.log x)) / d =
    -Real.log (lowerSaddleGrid d m θ C x) by field_simp; ring,
    Real.exp_neg, Real.exp_log (lowerSaddleGrid_positive d m θ C x)]

theorem lowerSaddleOmega_div_M_limit {d m θ : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C : ℝ) :
    Tendsto (fun x : ℝ => lowerSaddleOmega d m θ C x / lowerSaddleM m x) atTop (𝓝 θ) := by
  have hh := (lowerSaddleOmegaZero_div_M_limit hm θ C).add
    ((lowerSaddleOmega_rounding_limit hd hm hθ C).mul (lowerSaddleM_tendsto_atTop hm).inv_tendsto_atTop)
  simp only [mul_zero, add_zero] at hh
  convert! hh using 1; funext x
  change lowerSaddleOmega d m θ C x / (lowerSaddleM m x : ℝ) =
    lowerSaddleOmegaZero m θ C x / (lowerSaddleM m x : ℝ) +
    (lowerSaddleOmega d m θ C x - lowerSaddleOmegaZero m θ C x) / (lowerSaddleM m x : ℝ)
  simp only [div_eq_mul_inv]; ring

lemma lowerSaddleOmega_tendsto_atTop {d m θ : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C : ℝ) :
    Tendsto (lowerSaddleOmega d m θ C) atTop atTop := by
  have ht := lowerSaddleM_tendsto_atTop hm
  refine (ht.atTop_mul_pos hθ (lowerSaddleOmega_div_M_limit hd hm hθ C)).congr' ?_
  filter_upwards [ht.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  exact mul_div_cancel₀ _ hx.ne'

lemma lowerSaddleOmega_div_log_limit {d m θ : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C : ℝ) :
    Tendsto (fun x : ℝ => lowerSaddleOmega d m θ C x / Real.log x) atTop (𝓝 0) := by
  have hMlog : Tendsto (fun x : ℝ => (lowerSaddleM m x : ℝ) / Real.log x) atTop (𝓝 0) := by
    have hh := (lowerSaddleM_div_sqrt_log_limit hm).mul tendsto_sqrt_log_div_log
    simp only [mul_zero] at hh
    refine hh.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hz : Real.sqrt (Real.log x) ≠ 0 := (Real.sqrt_pos.2 (Real.log_pos hx)).ne'
    field_simp
  have hh := (lowerSaddleOmega_div_M_limit hd hm hθ C).mul hMlog
  simp only [mul_zero] at hh
  refine hh.congr' ?_
  filter_upwards [(lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  field_simp

def lowerSaddleN (s d m θ C : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  Real.exp (lowerSaddleLogN s d (Real.log x) (lowerSaddleOmega d m θ C x)
    (τM (lowerSaddleM m x)) (lowerSaddleM m x))

def lowerSaddleEta (s d m θ C cf x : ℝ) : ℝ := cf * (lowerSaddleH d m θ C x) ^ s

def lowerSaddleActivity (s d m θ C : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  (lowerSaddleN s d m θ C τM x) ^ 2 * Real.exp (τM (lowerSaddleM m x) * lowerSaddleM m x)

def lowerSaddleRisk (s d m θ C cf : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  (lowerSaddleEta s d m θ C cf x) ^ 2 / lowerSaddleActivity s d m θ C τM x

def lowerSaddleEnergyOne (s d m θ C : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  x ^ (2 : ℕ) * (lowerSaddleH d m θ C x) ^ (d + 4 * s) *
    (lowerSaddleN s d m θ C τM x) ^ (-d)

def lowerSaddleEnergyTwo (s d m θ C CG : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  x * (lowerSaddleH d m θ C x) ^ (4 * s) *
    Real.exp (2 * τM (lowerSaddleM m x) * lowerSaddleM m x) *
    (lowerSaddleN s d m θ C τM x) ^ (4 - d) *
    (CG * lowerSaddleMu d m θ C x) ^ lowerSaddleM m x /
      ((lowerSaddleM m x + 1).factorial : ℝ)

def lowerSaddleEnergyThree (s d m θ C CG : ℝ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  x * (lowerSaddleH d m θ C x) ^ (4 * s) *
    (lowerSaddleActivity s d m θ C τM x) ^ 2 *
    (CG * lowerSaddleMu d m θ C x) ^ lowerSaddleD d m x /
      ((lowerSaddleD d m x + 1).factorial : ℝ)

theorem lowerSaddleN_positive (s d m θ C : ℝ) (τM : ℕ → ℝ) (x : ℝ) :
    0 < lowerSaddleN s d m θ C τM x := Real.exp_pos _

theorem lowerSaddleActivity_positive (s d m θ C : ℝ) (τM : ℕ → ℝ) (x : ℝ) :
    0 < lowerSaddleActivity s d m θ C τM x :=
  mul_pos (sq_pos_of_pos (lowerSaddleN_positive s d m θ C τM x)) (Real.exp_pos _)

theorem lowerSaddleTau_limit {m τ Cτ : ℝ} {τM : ℕ → ℝ}
    (hm : 0 < m) (hcontrol : LowerExponentControl τM τ Cτ) :
    Tendsto (fun x : ℝ => τM (lowerSaddleM m x)) atTop (𝓝 τ) := by
  have ht := lowerSaddleM_tendsto_atTop hm
  have he := (lowerSaddleM_nat_tendsto_atTop hm).eventually hcontrol
  have hu : Tendsto (fun x : ℝ => Cτ / lowerSaddleM m x) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using! ht.inv_tendsto_atTop.const_mul Cτ
  have hh : Tendsto (fun x : ℝ => τM (lowerSaddleM m x) - τ) atTop (𝓝 0) := by
    refine squeeze_zero' (he.mono fun _ hx => sub_nonneg.2 hx.1) ?_ hu
    filter_upwards [he, ht.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hM
    exact (le_div_iff₀ hM).2 hx.2
  simpa only [zero_add, sub_add_cancel] using hh.add_const τ

lemma lowerSaddleLogN_div_log_limit {d m θ τ Cτ : ℝ} {τM : ℕ → ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ)
    (hcontrol : LowerExponentControl τM τ Cτ) (s C : ℝ) :
    Tendsto (fun x : ℝ => Real.log (lowerSaddleN s d m θ C τM x) / Real.log x)
      atTop (𝓝 ((d - 4 * s) / (d * (d + 4)))) := by
  have hMlog : Tendsto (fun x : ℝ => (lowerSaddleM m x : ℝ) / Real.log x) atTop (𝓝 0) := by
    have hh := (lowerSaddleM_div_sqrt_log_limit hm).mul tendsto_sqrt_log_div_log
    simp only [mul_zero] at hh
    refine hh.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hz : Real.sqrt (Real.log x) ≠ 0 := (Real.sqrt_pos.2 (Real.log_pos hx)).ne'
    field_simp
  have hh := (((tendsto_const_nhds (x := (d - 4 * s) / d)).sub
    ((lowerSaddleOmega_div_log_limit hd hm hθ C).const_mul (1 + 4 * s / d))).sub
    (((lowerSaddleTau_limit hm hcontrol).mul hMlog).const_mul 2)).div_const (d + 4)
  simp only [mul_zero, sub_zero, div_div] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  unfold lowerSaddleN lowerSaddleLogN; rw [Real.log_exp]; field_simp [(Real.log_pos hx).ne']

theorem lowerSaddleLogN_div_M_sq_limit {d m θ τ Cτ : ℝ} {τM : ℕ → ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ)
    (hcontrol : LowerExponentControl τM τ Cτ) (s C : ℝ) :
    Tendsto (fun x : ℝ => Real.log (lowerSaddleN s d m θ C τM x) / (lowerSaddleM m x : ℝ) ^ 2)
      atTop (𝓝 (((d - 4 * s) / (d * (d + 4))) / m ^ 2)) := by
  refine ((lowerSaddleLogN_div_log_limit hd hm hθ hcontrol s C).div
    (lowerSaddleM_sq_div_log_limit hm) (pow_ne_zero 2 hm.ne')).congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  change (Real.log (lowerSaddleN s d m θ C τM x) / Real.log x) /
    ((lowerSaddleM m x : ℝ) ^ 2 / Real.log x) =
      Real.log (lowerSaddleN s d m θ C τM x) / (lowerSaddleM m x : ℝ) ^ 2
  field_simp [(Real.log_pos hx).ne']

theorem lowerSaddleN_tendsto_atTop {s d m θ τ Cτ : ℝ} {τM : ℕ → ℝ}
    (hs : 1 < s) (hd : 4 * s < d) (hm : 0 < m) (hθ : 0 < θ)
    (hcontrol : LowerExponentControl τM τ Cτ) (C : ℝ) :
    Tendsto (lowerSaddleN s d m θ C τM) atTop atTop := by
  have hd0 : 0 < d := by linarith
  have ht : Tendsto (fun x : ℝ => Real.log (lowerSaddleN s d m θ C τM x)) atTop atTop := by
    refine (Real.tendsto_log_atTop.atTop_mul_pos (by positivity)
      (lowerSaddleLogN_div_log_limit hd0 hm hθ hcontrol s C)).congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact mul_div_cancel₀ _ (Real.log_pos hx).ne'
  exact (Real.tendsto_exp_atTop.comp ht).congr fun x => Real.exp_log (lowerSaddleN_positive s d m θ C τM x)

theorem lowerSaddleMu_tends_zero {d m θ : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C : ℝ) :
    Tendsto (lowerSaddleMu d m θ C) atTop (𝓝 0) := by
  refine (Real.tendsto_exp_atBot.comp
    (tendsto_neg_atTop_atBot.comp (lowerSaddleOmega_tendsto_atTop hd hm hθ C))).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (lowerSaddleMu_eq_exp hx).symm

theorem lowerSaddleEta_tends_zero {s d m θ : ℝ}
    (hs : 0 < s) (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (C cf : ℝ) :
    Tendsto (lowerSaddleEta s d m θ C cf) atTop (𝓝 0) := by
  simpa only [Real.zero_rpow hs.ne', mul_zero] using!
    (((lowerSaddleGrid_tendsto_atTop hd hm hθ C).inv_tendsto_atTop).rpow_const (Or.inr hs.le)).const_mul cf

theorem tendsto_atBot_of_div_negative {f g : ℝ → ℝ} {c : ℝ}
    (hg : Tendsto g atTop atTop) (hf : Tendsto (fun x => f x / g x) atTop (𝓝 c))
    (hc : c < 0) : Tendsto f atTop atBot := by
  refine (hg.atTop_mul_neg hc hf).congr' ?_
  filter_upwards [hg.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  exact mul_div_cancel₀ _ hx.ne'

theorem lowerSaddleRisk_positive {s d m θ C cf x : ℝ} (hcf : 0 < cf) (τM : ℕ → ℝ) :
    0 < lowerSaddleRisk s d m θ C cf τM x :=
  div_pos (sq_pos_of_pos (mul_pos hcf (Real.rpow_pos_of_pos (lowerSaddleH_positive d m θ C x) s)))
    (lowerSaddleActivity_positive s d m θ C τM x)

theorem lowerSaddleD_div_M_limit {d m : ℝ} (hd : 0 < d) (hm : 0 < m) :
    Tendsto (fun x : ℝ => (lowerSaddleD d m x : ℝ) / lowerSaddleM m x) atTop (𝓝 ((d + 8) / 4)) := by
  have ht := lowerSaddleM_tendsto_atTop hm
  have hu : Tendsto (fun x : ℝ => 1 / (lowerSaddleM m x : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div] using! ht.inv_tendsto_atTop
  have herr : Tendsto (fun x : ℝ => ((lowerSaddleD d m x : ℝ) - (d + 8) / 4 * lowerSaddleM m x) / lowerSaddleM m x)
      atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => div_nonneg (sub_nonneg.2 (Nat.le_ceil _)) (by positivity))
      (Eventually.of_forall fun x => div_le_div_of_nonneg_right ?_ (by positivity)) hu
    have hh := Nat.ceil_lt_add_one (show 0 ≤ (d + 8) / 4 * (lowerSaddleM m x : ℝ) by positivity)
    change (lowerSaddleD d m x : ℝ) < (d + 8) / 4 * lowerSaddleM m x + 1 at hh
    linarith
  have hh := (tendsto_const_nhds (x := (d + 8) / 4)).add herr
  simp only [add_zero] at hh
  refine hh.congr' ?_
  filter_upwards [ht.eventually (eventually_gt_atTop (0 : ℝ))] with x hx
  field_simp; ring

def lowerSaddleTheta (s d τ : ℝ) : ℝ := d * τ / (2 * (s - 1))

theorem lowerSaddleCoefficient_pos {s d τ : ℝ}
    (hs : 1 < s) (hd : 4 * s < d) (hτ : 0 < τ) :
    0 < lowerSaddleCoefficient s d τ := by
  have hd0 : 0 < d := by linarith
  unfold lowerSaddleCoefficient; exact Real.sqrt_pos.2 (by positivity)

theorem lowerSaddleTheta_pos {s d τ : ℝ}
    (hs : 1 < s) (hd : 4 * s < d) (hτ : 0 < τ) : 0 < lowerSaddleTheta s d τ := by
  have hd0 : 0 < d := by linarith
  unfold lowerSaddleTheta; positivity

theorem actual_lowerSaddleRisk_rate_bracket {s d a b cf : ℝ}
    (hs : 1 < s) (hd : 4 * s < d) (ha : 0 < a) (hab : a < b) (hcf : 0 < cf) (C : ℝ) :
    ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∀ᶠ x : ℝ in atTop,
      c * rateScale (rateExponent s d) (stretchConstant s d (densityIntervalExponent a b))
        (lowerLogPower s d) x ≤
      lowerSaddleRisk s d (lowerSaddleCoefficient s d (densityIntervalExponent a b))
        (lowerSaddleTheta s d (densityIntervalExponent a b)) C cf (shrunkDensityExponent a b) x ∧
      lowerSaddleRisk s d (lowerSaddleCoefficient s d (densityIntervalExponent a b))
        (lowerSaddleTheta s d (densityIntervalExponent a b)) C cf (shrunkDensityExponent a b) x ≤
      A * rateScale (rateExponent s d) (stretchConstant s d (densityIntervalExponent a b))
        (lowerLogPower s d) x := by
  have hd0 : 0 < d := by linarith
  have hτ := densityIntervalExponent_pos ha hab
  let m := lowerSaddleCoefficient s d (densityIntervalExponent a b)
  let θ := lowerSaddleTheta s d (densityIntervalExponent a b)
  let τM := shrunkDensityExponent a b
  have hm : 0 < m := lowerSaddleCoefficient_pos hs hd hτ
  have hθ : 0 < θ := lowerSaddleTheta_pos hs hd hτ
  obtain ⟨Cτ, _, hcontrol⟩ := exists_actual_lowerExponentControl ha hab
  have hceil : (fun x : ℝ => (lowerSaddleM m x : ℝ) - m * Real.sqrt (Real.log x))
      =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs, norm_one, mul_one]
    rw [abs_of_nonneg (sub_nonneg.2 (lowerSaddleM_rounding hm.le).1)]
    linarith [(lowerSaddleM_rounding (x := x) hm.le).2]
  have hlogM : Tendsto (fun x : ℝ => Real.log (lowerSaddleM m x) - Real.log (Real.log x) / 2)
      atTop (𝓝 (Real.log m)) := by
    refine ((Real.continuousAt_log hm.ne').tendsto.comp (lowerSaddleM_div_sqrt_log_limit hm)).congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      (lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop (0 : ℝ))] with x hx hMx
    simp only [Function.comp_apply]
    rw [Real.log_div hMx.ne' (Real.sqrt_pos.2 (Real.log_pos hx)).ne', Real.log_sqrt (Real.log_pos hx).le]
  have hτO : (fun x : ℝ => (τM (lowerSaddleM m x) - densityIntervalExponent a b) * lowerSaddleM m x)
      =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
    refine Asymptotics.IsBigO.of_bound Cτ ?_
    filter_upwards [(lowerSaddleM_nat_tendsto_atTop hm).eventually hcontrol] with x hx
    simp only [Real.norm_eq_abs, norm_one, mul_one]
    rw [abs_of_nonneg (mul_nonneg (sub_nonneg.2 hx.1) (by positivity))]; exact hx.2
  have hc := Asymptotics.isBigO_const_one (2 * Real.log cf - 2 * (s - 1) / (d + 4) * C) (atTop : Filter ℝ) (F := ℝ)
  have hbigO : (fun x : ℝ => Real.log (lowerSaddleRisk s d m θ C cf τM x) -
      rateLog (rateExponent s d) (2 * d * densityIntervalExponent a b / (d + 4) * m) (lowerLogPower s d) x)
      =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
    refine ((((hc.sub (hceil.const_mul_left (2 * d * densityIntervalExponent a b / (d + 4)))).add
      ((hlogM.isBigO_one ℝ).const_mul_left (2 * (s - 1) / (d + 4)))).sub
      (((lowerSaddleOmega_rounding_limit hd0 hm hθ C).isBigO_one ℝ).const_mul_left (2 * (s - 1) / (d + 4)))).sub
      (hτO.const_mul_left (d / (d + 4)))).congr_left fun x => ?_
    have hH := lowerSaddleH_positive d m θ C x
    have hN := lowerSaddleN_positive s d m θ C τM x
    have hEta : 0 < lowerSaddleEta s d m θ C cf x := mul_pos hcf (Real.rpow_pos_of_pos hH s)
    have hlogR : Real.log (lowerSaddleRisk s d m θ C cf τM x) =
        2 * Real.log cf - rateExponent s d * Real.log x -
          (2 * (s - 1) * lowerSaddleOmega d m θ C x + d * τM (lowerSaddleM m x) * lowerSaddleM m x) / (d + 4) := by
      unfold lowerSaddleRisk
      rw [Real.log_div (pow_ne_zero 2 hEta.ne') (lowerSaddleActivity_positive s d m θ C τM x).ne', Real.log_pow]
      unfold lowerSaddleEta lowerSaddleActivity
      rw [Real.log_mul hcf.ne' (Real.rpow_pos_of_pos hH s).ne', Real.log_rpow hH,
        Real.log_mul (pow_ne_zero 2 hN.ne') (Real.exp_pos _).ne', Real.log_pow, Real.log_exp,
        lowerSaddleH_eq_exp hd0.ne', Real.log_exp]
      unfold lowerSaddleN; rw [Real.log_exp]
      have hh := lower_saddle_rate hs hd (Real.log x) (lowerSaddleOmega d m θ C x)
        (τM (lowerSaddleM m x)) (lowerSaddleM m x)
      ring_nf at hh ⊢; linarith
    rw [hlogR]
    unfold rateLog lowerLogPower lowerSaddleOmegaZero θ lowerSaddleTheta
    field_simp [show s - 1 ≠ 0 by linarith, show d + 4 ≠ 0 by linarith]; ring
  rw [← lower_saddle_stretchConstant hs hd hτ]
  obtain ⟨K, hK⟩ := hbigO.bound
  refine ⟨Real.exp (-K), Real.exp K, Real.exp_pos _, Real.exp_pos _, ?_⟩
  filter_upwards [hK] with x hx
  simp only [Real.norm_eq_abs, norm_one, mul_one] at hx
  have hp := lowerSaddleRisk_positive (s := s) (d := d) (m := m) (θ := θ) (C := C) (x := x) hcf τM
  rcases abs_le.1 hx with ⟨hl, hu⟩
  unfold rateScale
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_log hp]
  exact ⟨Real.exp_le_exp.2 (le_sub_iff_add_le.1 hl), Real.exp_le_exp.2 (sub_le_iff_le_add.1 hu)⟩

def lowerSaddleResponseQuantity (s d m θ C cf : ℝ) (q : ℕ) (τM : ℕ → ℝ) (x : ℝ) : ℝ :=
  (lowerSaddleEta s d m θ C cf x) ^ (4 * q) * (lowerSaddleN s d m θ C τM x) ^ d

def lowerSaddleResponseOrder (s d : ℝ) : ℕ := max 2 (Nat.floor (d / (4 * s)))

def LowerSaddleReg (K η0 s d m θ C cf : ℝ) (M0 : ℕ) (τM : ℕ → ℝ) (x : ℝ) : Prop :=
  M0 ≤ lowerSaddleM m x ∧
  lowerSaddleD d m x = Nat.ceil ((d + 8) / 4 * lowerSaddleM m x) ∧
  1 ≤ lowerSaddleN s d m θ C τM x ∧
  0 < lowerSaddleMu d m θ C x ∧ lowerSaddleMu d m θ C x < 1 ∧
  (lowerSaddleM m x : ℝ) / K ≤ lowerSaddleOmega d m θ C x ∧
  lowerSaddleOmega d m θ C x ≤ K * lowerSaddleM m x ∧
  (lowerSaddleM m x : ℝ) ^ 2 / K ≤ Real.log (lowerSaddleN s d m θ C τM x) ∧
  Real.log (lowerSaddleN s d m θ C τM x) ≤ K * (lowerSaddleM m x : ℝ) ^ 2 ∧
  0 < lowerSaddleEta s d m θ C cf x ∧ lowerSaddleEta s d m θ C cf x ≤ η0 ∧
  lowerSaddleResponseQuantity s d m θ C cf (lowerSaddleResponseOrder s d) τM x ≤ 1

theorem actual_lowerSaddle_fixed_regime_window {s d a b cf : ℝ}
    (hs : 1 < s) (hd : 4 * s < d) (ha : 0 < a) (hab : a < b) (hcf : 0 < cf) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (C η0 : ℝ) (M0 : ℕ), 0 < η0 →
      ∀ᶠ x : ℝ in atTop,
        LowerSaddleReg K η0 s d (lowerSaddleCoefficient s d (densityIntervalExponent a b))
          (lowerSaddleTheta s d (densityIntervalExponent a b)) C cf M0 (shrunkDensityExponent a b) x := by
  have hd0 : 0 < d := by linarith
  have hτ := densityIntervalExponent_pos ha hab
  let m := lowerSaddleCoefficient s d (densityIntervalExponent a b)
  let θ := lowerSaddleTheta s d (densityIntervalExponent a b)
  let τM := shrunkDensityExponent a b
  have hm : 0 < m := lowerSaddleCoefficient_pos hs hd hτ
  have hθ : 0 < θ := lowerSaddleTheta_pos hs hd hτ
  let v := ((d - 4 * s) / (d * (d + 4))) / m ^ 2
  have hv : 0 < v := by positivity
  let K := 2 + θ + v + 1 / θ + 1 / v
  have h1θ : 0 < 1 / θ := by positivity
  have h1v : 0 < 1 / v := by positivity
  have hKpos : 0 < K := by dsimp [K]; linarith
  have hθlow : 1 / K < θ := (div_lt_iff₀ hKpos).2
    (by simpa only [one_div, mul_inv_cancel₀ hθ.ne'] using mul_lt_mul_of_pos_left (by dsimp [K]; linarith : 1 / θ < K) hθ)
  have hNlow : 1 / K < v := (div_lt_iff₀ hKpos).2
    (by simpa only [one_div, mul_inv_cancel₀ hv.ne'] using mul_lt_mul_of_pos_left (by dsimp [K]; linarith : 1 / v < K) hv)
  obtain ⟨Cτ, _, hcontrol⟩ := exists_actual_lowerExponentControl ha hab
  refine ⟨K, by dsimp [K]; linarith, fun C η0 M0 hη0 => ?_⟩
  let q := lowerSaddleResponseOrder s d
  have hq : d / (4 * s) - 1 ≤ (q : ℝ) := by
    have hmax : (Nat.floor (d / (4 * s)) : ℝ) ≤ q := by exact_mod_cast le_max_right 2 (Nat.floor (d / (4 * s)))
    linarith [Nat.lt_floor_add_one (d / (4 * s))]
  have hqmul : d ≤ 4 * s * ((q : ℝ) + 1) := by
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < 4 * s)).1 (by linarith : d / (4 * s) ≤ (q : ℝ) + 1)
  have hc : (4 * q : ℝ) * (-s / d) + d * ((d - 4 * s) / (d * (d + 4))) < 0 := by
    rw [show (4 * q : ℝ) * (-s / d) + d * ((d - 4 * s) / (d * (d + 4))) =
      -4 * ((d - 4 * s) / (d * (d + 4))) + (d - 4 * s * ((q : ℝ) + 1)) / d by field_simp; ring]
    have hp : 0 < (d - 4 * s) / (d * (d + 4)) := by positivity
    linarith [div_nonpos_of_nonpos_of_nonneg (by linarith : d - 4 * s * ((q : ℝ) + 1) ≤ 0) hd0.le]
  have hlogEta : Tendsto (fun x : ℝ => Real.log (lowerSaddleEta s d m θ C cf x) / Real.log x) atTop (𝓝 (-s / d)) := by
    have hh := (tendsto_const_div_log (Real.log cf)).sub
      (((tendsto_const_nhds (x := (1 : ℝ))).add (lowerSaddleOmega_div_log_limit hd0 hm hθ C)).const_mul (s / d))
    simp only [add_zero, mul_one, zero_sub, ← neg_div] at hh
    refine hh.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    unfold lowerSaddleEta
    rw [Real.log_mul hcf.ne' (Real.rpow_pos_of_pos (lowerSaddleH_positive d m θ C x) s).ne',
      Real.log_rpow (lowerSaddleH_positive d m θ C x), lowerSaddleH_eq_exp hd0.ne', Real.log_exp]
    field_simp [(Real.log_pos hx).ne']; ring
  have hlogRsp : Tendsto (fun x : ℝ => Real.log (lowerSaddleResponseQuantity s d m θ C cf q τM x) / Real.log x)
      atTop (𝓝 ((4 * q : ℝ) * (-s / d) + d * ((d - 4 * s) / (d * (d + 4))))) := by
    refine ((hlogEta.const_mul ((4 : ℝ) * (q : ℝ))).add
      ((lowerSaddleLogN_div_log_limit hd0 hm hθ hcontrol s C).const_mul d)).congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x _
    have hEta : 0 < lowerSaddleEta s d m θ C cf x :=
      mul_pos hcf (Real.rpow_pos_of_pos (lowerSaddleH_positive d m θ C x) s)
    unfold lowerSaddleResponseQuantity
    rw [Real.log_mul (pow_ne_zero (4 * q) hEta.ne')
      (Real.rpow_pos_of_pos (lowerSaddleN_positive s d m θ C τM x) d).ne',
      Real.log_pow, Real.log_rpow (lowerSaddleN_positive s d m θ C τM x)]
    push_cast; ring
  have hrsp : Tendsto (lowerSaddleResponseQuantity s d m θ C cf q τM) atTop (𝓝 0) :=
    (Real.tendsto_exp_atBot.comp (tendsto_atBot_of_div_negative Real.tendsto_log_atTop hlogRsp hc)).congr
      fun x => Real.exp_log (by
        unfold lowerSaddleResponseQuantity lowerSaddleEta
        have := lowerSaddleH_positive d m θ C x
        have := lowerSaddleN_positive s d m θ C τM x; positivity)
  have hω := lowerSaddleOmega_div_M_limit hd0 hm hθ C
  have hN := lowerSaddleLogN_div_M_sq_limit hd0 hm hθ hcontrol s C
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    (lowerSaddleM_nat_tendsto_atTop hm).eventually (eventually_ge_atTop M0),
    (lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop (0 : ℝ)),
    (lowerSaddleN_tendsto_atTop hs hd hm hθ hcontrol C).eventually (eventually_ge_atTop (1 : ℝ)),
    (lowerSaddleMu_tends_zero hd0 hm hθ C).eventually (gt_mem_nhds one_pos),
    hω.eventually (lt_mem_nhds hθlow), hω.eventually (gt_mem_nhds (by dsimp [K]; linarith : θ < K)),
    hN.eventually (lt_mem_nhds hNlow), hN.eventually (gt_mem_nhds (by dsimp [K]; linarith : v < K)),
    (lowerSaddleEta_tends_zero (s := s) (by linarith) hd0 hm hθ C cf).eventually (gt_mem_nhds hη0),
    hrsp.eventually (gt_mem_nhds one_pos)]
    with x hx hM0 hMpos hN1 hMu1 hωl hωu hNl hNu hEta0 hRsp
  refine ⟨hM0, rfl, hN1, mul_pos hx (Real.rpow_pos_of_pos (lowerSaddleH_positive d m θ C x) d), hMu1,
    by simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using ((lt_div_iff₀ hMpos).1 hωl).le,
    ((div_lt_iff₀ hMpos).1 hωu).le,
    by simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one, one_mul] using ((lt_div_iff₀ (sq_pos_of_pos hMpos)).1 hNl).le,
    ((div_lt_iff₀ (sq_pos_of_pos hMpos)).1 hNu).le,
    mul_pos hcf (Real.rpow_pos_of_pos (lowerSaddleH_positive d m θ C x) s), hEta0.le, hRsp.le⟩

theorem eventually_lowerSaddle_grid_and_mass {d m θ cm Cmgf : ℝ}
    (hd : 0 < d) (hm : 0 < m) (hθ : 0 < θ) (hcm : 0 < cm) (hCmgf : 0 < Cmgf)
    (C : ℝ) (gridThreshold : ℕ) :
    ∀ᶠ x : ℝ in atTop, gridThreshold ≤ lowerSaddleGrid d m θ C x ∧
      8 * Cmgf * lowerSaddleMu d m θ C x ≤ cm / lowerSaddleM m x := by
  have hMmu : Tendsto (fun x : ℝ => (lowerSaddleM m x : ℝ) * lowerSaddleMu d m θ C x) atTop (𝓝 0) := by
    have hh := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      (lowerSaddleM_tendsto_atTop hm)).sub (lowerSaddleOmega_div_M_limit hd hm hθ C)
    simp only [zero_sub] at hh
    have ht : Tendsto (fun x : ℝ => Real.log (lowerSaddleM m x) - lowerSaddleOmega d m θ C x) atTop atBot := by
      refine tendsto_atBot_of_div_negative (lowerSaddleM_tendsto_atTop hm) ?_ (neg_neg_of_pos hθ)
      convert! hh using 1; funext x
      change (Real.log (lowerSaddleM m x) - lowerSaddleOmega d m θ C x) / (lowerSaddleM m x : ℝ) =
        Real.log (lowerSaddleM m x) / (lowerSaddleM m x : ℝ) - lowerSaddleOmega d m θ C x / (lowerSaddleM m x : ℝ)
      ring
    refine (Real.tendsto_exp_atBot.comp ht).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      (lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop (0 : ℝ))] with x hx hM
    simp only [Function.comp_apply]
    rw [Real.exp_sub, Real.exp_log hM, lowerSaddleMu_eq_exp hx, Real.exp_neg]; rfl
  filter_upwards [(tendsto_natCast_atTop_iff.1 (lowerSaddleGrid_tendsto_atTop hd hm hθ C)).eventually
      (eventually_ge_atTop gridThreshold),
    (lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop (0 : ℝ)),
    hMmu.eventually (gt_mem_nhds (by positivity : 0 < cm / (8 * Cmgf)))] with x hx hM hmass
  refine ⟨hx, (le_div_iff₀ hM).2 ?_⟩
  nlinarith only [(lt_div_iff₀ (by positivity : 0 < 8 * Cmgf)).1 hmass]

theorem eventually_actual_lowerSaddle_numeric_cost {s d a b CG C : ℝ}
    (hs : 1 < s) (hd : 4 * s < d) (ha : 0 < a) (hab : a < b) (hCG : 0 < CG)
    (hC : 1 + Real.log CG + (d ^ 2 - 16 * s) / (d * (d + 4)) *
      lowerSaddleTheta s d (densityIntervalExponent a b) +
      2 * d * densityIntervalExponent a b / (d + 4) < C) :
    ∀ᶠ x : ℝ in atTop,
      let m := lowerSaddleCoefficient s d (densityIntervalExponent a b)
      let θ := lowerSaddleTheta s d (densityIntervalExponent a b)
      let τM := shrunkDensityExponent a b
      CG * ((lowerSaddleActivity s d m θ C τM x) ^ 2 + lowerSaddleEnergyOne s d m θ C τM x +
        lowerSaddleEnergyTwo s d m θ C CG τM x + lowerSaddleEnergyThree s d m θ C CG τM x) ≤
          3 * CG * (lowerSaddleActivity s d m θ C τM x) ^ 2 := by
  have hd0 : 0 < d := by linarith
  have hτ := densityIntervalExponent_pos ha hab
  let m := lowerSaddleCoefficient s d (densityIntervalExponent a b)
  let θ := lowerSaddleTheta s d (densityIntervalExponent a b)
  let τM := shrunkDensityExponent a b
  have hm : 0 < m := lowerSaddleCoefficient_pos hs hd hτ
  have hθ : 0 < θ := lowerSaddleTheta_pos hs hd hτ
  obtain ⟨Cτ, _, hcontrol⟩ := exists_actual_lowerExponentControl ha hab
  have hbalance : θ * m ^ 2 = 4 * ((d - 4 * s) / (d * (d + 4))) := by
    have hp : 0 ≤ 8 * (d - 4 * s) * (s - 1) / (d ^ 2 * (d + 4) * densityIntervalExponent a b) := by positivity
    unfold θ m lowerSaddleTheta lowerSaddleCoefficient
    rw [Real.sq_sqrt hp]; field_simp [show s - 1 ≠ 0 by linarith]; ring
  let aliasUpper (x : ℝ) := (d ^ 2 - 16 * s) / (d * (d + 4)) * lowerSaddleOmega d m θ C x +
    (2 * d * τM (lowerSaddleM m x) / (d + 4) + Real.log CG + 1 - C) * lowerSaddleM m x
  have haliasLim : Tendsto (fun x : ℝ => aliasUpper x / lowerSaddleM m x)
      atTop (𝓝 ((d ^ 2 - 16 * s) / (d * (d + 4)) * θ +
        2 * d * densityIntervalExponent a b / (d + 4) + Real.log CG + 1 - C)) := by
    have hh := ((lowerSaddleOmega_div_M_limit hd0 hm hθ C).const_mul ((d ^ 2 - 16 * s) / (d * (d + 4)))).add
      ((((lowerSaddleTau_limit hm hcontrol).const_mul (2 * d)).div_const (d + 4)).add_const (Real.log CG + 1 - C))
    have hid : (d ^ 2 - 16 * s) / (d * (d + 4)) * θ +
        (2 * d * densityIntervalExponent a b / (d + 4) + (Real.log CG + 1 - C)) =
        (d ^ 2 - 16 * s) / (d * (d + 4)) * θ +
          2 * d * densityIntervalExponent a b / (d + 4) + Real.log CG + 1 - C := by ring
    rw [hid] at hh
    refine hh.congr' ?_
    filter_upwards [(lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop (0 : ℝ))] with x hx
    dsimp [aliasUpper]; field_simp; ring
  have htwo : Tendsto (fun x : ℝ => lowerSaddleEnergyTwo s d m θ C CG τM x /
      (lowerSaddleActivity s d m θ C τM x) ^ 2) atTop (𝓝 0) := by
    have hb := Real.tendsto_exp_atBot.comp
      (tendsto_atBot_of_div_negative (lowerSaddleM_tendsto_atTop hm) haliasLim (by linarith))
    refine squeeze_zero' ?_ ?_ hb
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have := lowerSaddleH_positive d m θ C x; have := lowerSaddleN_positive s d m θ C τM x
      have := lowerSaddleActivity_positive s d m θ C τM x
      unfold lowerSaddleEnergyTwo lowerSaddleMu; positivity
    · filter_upwards [eventually_gt_atTop (1 : ℝ),
        (lowerSaddleM_tendsto_atTop hm).eventually (eventually_ge_atTop (1 : ℝ)),
        (lowerSaddleGridBase_tendsto_atTop hd0 hm hθ C).eventually (eventually_ge_atTop (1 : ℝ))]
        with x hx hMx hbx
      have hx0 : 0 < x := by linarith
      have hH := lowerSaddleH_positive d m θ C x
      have hN := lowerSaddleN_positive s d m θ C τM x
      have hA := lowerSaddleActivity_positive s d m θ C τM x
      have hMu : 0 < lowerSaddleMu d m θ C x := mul_pos hx0 (Real.rpow_pos_of_pos hH d)
      have hp : 0 < lowerSaddleEnergyTwo s d m θ C CG τM x / (lowerSaddleActivity s d m θ C τM x) ^ 2 := by
        unfold lowerSaddleEnergyTwo; positivity
      refine (Real.exp_log hp).symm.trans_le (Real.exp_le_exp.2 ?_)
      have hMnat : 1 ≤ lowerSaddleM m x := by exact_mod_cast hMx
      have hs_st := Stirling.le_log_factorial_stirling (Nat.ne_of_gt (by omega : 0 < lowerSaddleM m x))
      have hlogM0 := Real.log_nonneg hMx
      have hlogpi := Real.log_nonneg (by linarith [Real.pi_gt_three] : 1 ≤ 2 * Real.pi)
      have hl := Real.log_le_log (by positivity : 0 < ((lowerSaddleM m x).factorial : ℝ))
        (by exact_mod_cast Nat.factorial_le (Nat.le_succ _) : ((lowerSaddleM m x).factorial : ℝ) ≤ ((lowerSaddleM m x + 1).factorial : ℝ))
      have hfacL : (lowerSaddleM m x : ℝ) * Real.log (lowerSaddleM m x) - lowerSaddleM m x ≤
          Real.log ((lowerSaddleM m x + 1).factorial : ℝ) := by linarith
      have hlow := Real.log_le_log (Real.exp_pos _) (Nat.le_ceil (lowerSaddleGridBase d m θ C x))
      change Real.log (lowerSaddleGridBase d m θ C x) ≤ Real.log (lowerSaddleGrid d m θ C x) at hlow
      unfold lowerSaddleGridBase at hlow; rw [Real.log_exp] at hlow
      have hω : lowerSaddleOmegaZero m θ C x ≤ lowerSaddleOmega d m θ C x := by
        unfold lowerSaddleOmega
        nlinarith [mul_le_mul_of_nonneg_left hlow hd0.le,
          mul_div_cancel₀ (Real.log x + lowerSaddleOmegaZero m θ C x) hd0.ne']
      have hωmul := mul_le_mul_of_nonneg_left hω (Nat.cast_nonneg (lowerSaddleM m x))
      have hsq := (sq_le_sq₀ (by positivity : 0 ≤ m * Real.sqrt (Real.log x)) (by positivity)).2
        (lowerSaddleM_rounding (x := x) hm.le).1
      rw [mul_pow, Real.sq_sqrt (Real.log_nonneg hx.le)] at hsq
      have hbudget : 4 * ((d - 4 * s) / (d * (d + 4))) * Real.log x ≤ θ * (lowerSaddleM m x : ℝ) ^ 2 := by
        have hh := mul_le_mul_of_nonneg_left hsq hθ.le; rwa [← mul_assoc, hbalance] at hh
      have hlog2 : Real.log (lowerSaddleEnergyTwo s d m θ C CG τM x /
          (lowerSaddleActivity s d m θ C τM x) ^ 2) =
          4 * ((d - 4 * s) / (d * (d + 4))) * Real.log x +
            ((d ^ 2 - 16 * s) / (d * (d + 4)) - lowerSaddleM m x) * lowerSaddleOmega d m θ C x +
            (2 * d * τM (lowerSaddleM m x) / (d + 4) + Real.log CG) * lowerSaddleM m x -
            Real.log ((lowerSaddleM m x + 1).factorial : ℝ) := by
        unfold lowerSaddleEnergyTwo
        rw [Real.log_div (by positivity) (pow_ne_zero 2 hA.ne'),
          Real.log_div (by positivity) (by positivity : 0 < ((lowerSaddleM m x + 1).factorial : ℝ)).ne', Real.log_pow]
        repeat rw [Real.log_mul (by positivity) (by positivity)]
        rw [Real.log_rpow hH, Real.log_exp, Real.log_rpow hN, Real.log_pow,
          Real.log_mul hCG.ne' hMu.ne', lowerSaddleMu_eq_exp hx0, Real.log_exp]
        unfold lowerSaddleActivity lowerSaddleN
        rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_pow, Real.log_exp, Real.log_exp,
          lowerSaddleH_eq_exp hd0.ne', Real.log_exp]
        unfold lowerSaddleLogN; field_simp; ring
      rw [hlog2]; dsimp [aliasUpper]; unfold lowerSaddleOmegaZero at *; nlinarith
  let countUpper (x : ℝ) := (1 - 4 * s / d) * Real.log x +
    (lowerSaddleD d m x : ℝ) * (Real.log CG - lowerSaddleOmega d m θ C x)
  have hcountLim : Tendsto (fun x : ℝ => countUpper x / Real.log x)
      atTop (𝓝 (1 - 4 * s / d - (d + 8) / 4 * θ * m ^ 2)) := by
    have hconst : Tendsto (fun x : ℝ => Real.log CG / (lowerSaddleM m x : ℝ)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using! (lowerSaddleM_tendsto_atTop hm).inv_tendsto_atTop.const_mul (Real.log CG)
    have hh := (tendsto_const_nhds (x := 1 - 4 * s / d)).add
      (((lowerSaddleD_div_M_limit hd0 hm).mul (hconst.sub (lowerSaddleOmega_div_M_limit hd0 hm hθ C))).mul
        (lowerSaddleM_sq_div_log_limit hm))
    have hid : 1 - 4 * s / d + ((d + 8) / 4 * (0 - θ) * m ^ 2) =
        1 - 4 * s / d - (d + 8) / 4 * θ * m ^ 2 := by ring
    rw [hid] at hh
    refine hh.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      (lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop (0 : ℝ))] with x hx _
    dsimp [countUpper]; field_simp [(Real.log_pos hx).ne']
  have hthree : Tendsto (fun x : ℝ => lowerSaddleEnergyThree s d m θ C CG τM x /
      (lowerSaddleActivity s d m θ C τM x) ^ 2) atTop (𝓝 0) := by
    have hc : 1 - 4 * s / d - (d + 8) / 4 * θ * m ^ 2 < 0 := by
      rw [mul_assoc ((d + 8) / 4), hbalance,
        show 1 - 4 * s / d - (d + 8) / 4 * (4 * ((d - 4 * s) / (d * (d + 4)))) =
          -4 * ((d - 4 * s) / (d * (d + 4))) by field_simp; ring]
      have : 0 < (d - 4 * s) / (d * (d + 4)) := by positivity
      linarith
    have hb := Real.tendsto_exp_atBot.comp (tendsto_atBot_of_div_negative Real.tendsto_log_atTop hcountLim hc)
    refine squeeze_zero' ?_ ?_ hb
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      have := lowerSaddleH_positive d m θ C x; have := lowerSaddleActivity_positive s d m θ C τM x
      unfold lowerSaddleEnergyThree lowerSaddleMu; positivity
    · filter_upwards [eventually_gt_atTop (0 : ℝ),
        (lowerSaddleOmega_tendsto_atTop hd0 hm hθ C).eventually (eventually_ge_atTop (0 : ℝ))] with x hx hω
      have hH := lowerSaddleH_positive d m θ C x
      have hA := lowerSaddleActivity_positive s d m θ C τM x
      have hMu : 0 < lowerSaddleMu d m θ C x := mul_pos hx (Real.rpow_pos_of_pos hH d)
      have hp : 0 < lowerSaddleEnergyThree s d m θ C CG τM x / (lowerSaddleActivity s d m θ C τM x) ^ 2 := by
        unfold lowerSaddleEnergyThree; positivity
      refine (Real.exp_log hp).symm.trans_le (Real.exp_le_exp.2 ?_)
      have hlog3 : Real.log (lowerSaddleEnergyThree s d m θ C CG τM x /
          (lowerSaddleActivity s d m θ C τM x) ^ 2) =
          (1 - 4 * s / d) * Real.log x - 4 * s / d * lowerSaddleOmega d m θ C x +
          (lowerSaddleD d m x : ℝ) * (Real.log CG - lowerSaddleOmega d m θ C x) -
            Real.log ((lowerSaddleD d m x + 1).factorial : ℝ) := by
        unfold lowerSaddleEnergyThree
        rw [Real.log_div (by positivity) (pow_ne_zero 2 hA.ne'),
          Real.log_div (by positivity) (by positivity)]
        repeat rw [Real.log_mul (by positivity) (by positivity)]
        rw [Real.log_rpow hH, Real.log_pow, Real.log_pow, Real.log_mul hCG.ne' hMu.ne',
          lowerSaddleMu_eq_exp hx, Real.log_exp, lowerSaddleH_eq_exp hd0.ne', Real.log_exp]
        field_simp; ring
      rw [hlog3]; dsimp [countUpper]
      have hf := Real.log_nonneg (by exact_mod_cast Nat.factorial_pos (lowerSaddleD d m x + 1) :
        (1 : ℝ) ≤ ((lowerSaddleD d m x + 1).factorial : ℝ))
      have hp0 : 0 ≤ 4 * s / d * lowerSaddleOmega d m θ C x := by positivity
      linarith
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    htwo.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hthree.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with x hx h2 h3
  have hA2 : 0 < (lowerSaddleActivity s d m θ C τM x) ^ 2 :=
    sq_pos_of_pos (lowerSaddleActivity_positive s d m θ C τM x)
  have h1 : lowerSaddleEnergyOne s d m θ C τM x = (lowerSaddleActivity s d m θ C τM x) ^ 2 := by
    have hx2 : x ^ (2 : ℕ) = Real.exp ((2 : ℝ) * Real.log x) := by
      change x ^ (2 : ℕ) = Real.exp (((2 : ℕ) : ℝ) * Real.log x)
      rw [Real.exp_nat_mul, Real.exp_log hx]
    unfold lowerSaddleEnergyOne lowerSaddleActivity lowerSaddleN
    rw [hx2, Real.rpow_def_of_pos (lowerSaddleH_positive d m θ C x),
      Real.rpow_def_of_pos (Real.exp_pos _), mul_pow]
    simp only [Real.log_exp, ← Real.exp_nat_mul, ← Real.exp_add]
    rw [lowerSaddleH_eq_exp hd0.ne', Real.log_exp]
    congr 1; unfold lowerSaddleLogN; field_simp [show d + 4 ≠ 0 by linarith]; ring
  change CG * ((lowerSaddleActivity s d m θ C τM x) ^ 2 + lowerSaddleEnergyOne s d m θ C τM x +
    lowerSaddleEnergyTwo s d m θ C CG τM x + lowerSaddleEnergyThree s d m θ C CG τM x) ≤
      3 * CG * (lowerSaddleActivity s d m θ C τM x) ^ 2
  rw [h1]
  have h2' := (div_lt_iff₀ hA2).1 h2
  have h3' := (div_lt_iff₀ hA2).1 h3
  exact (mul_le_mul_of_nonneg_left
    (by linarith only [h2', h3'] :
      (lowerSaddleActivity s d m θ C τM x) ^ 2 + (lowerSaddleActivity s d m θ C τM x) ^ 2 +
        lowerSaddleEnergyTwo s d m θ C CG τM x + lowerSaddleEnergyThree s d m θ C CG τM x ≤
          3 * (lowerSaddleActivity s d m θ C τM x) ^ 2)
    hCG.le).trans_eq (by ring)

def lowerSaddleExceptionalTail (d m θ C c x : ℝ) : ℝ :=
  2 * Real.exp (-c / ((lowerSaddleM m x : ℝ) ^ 2 * (lowerSaddleH d m θ C x) ^ d))

theorem actual_lowerSaddle_exceptionalTail_over_Psi_tends_zero {s d a b cm Cmgf : ℝ}
    (hs : 1 < s) (hd : 4 * s < d) (ha : 0 < a) (hab : a < b)
    (hcm : 0 < cm) (hCmgf : 0 < Cmgf) (C : ℝ) :
    Tendsto (fun x : ℝ =>
      lowerSaddleExceptionalTail d (lowerSaddleCoefficient s d (densityIntervalExponent a b))
        (lowerSaddleTheta s d (densityIntervalExponent a b)) C (cm ^ 2 / (8 * Cmgf)) x /
        (rateScale (rateExponent s d) (stretchConstant s d (densityIntervalExponent a b))
          (lowerLogPower s d) x) ^ 2) atTop (𝓝 0) := by
  have hd0 : 0 < d := by linarith
  have hτ := densityIntervalExponent_pos ha hab
  let m := lowerSaddleCoefficient s d (densityIntervalExponent a b)
  let θ := lowerSaddleTheta s d (densityIntervalExponent a b)
  let c := cm ^ 2 / (8 * Cmgf)
  let lam := rateExponent s d
  let κ := stretchConstant s d (densityIntervalExponent a b)
  let lp := lowerLogPower s d
  have hm := lowerSaddleCoefficient_pos hs hd hτ
  have hθ := lowerSaddleTheta_pos hs hd hτ
  have hc : 0 < c := by positivity
  let c' := c / (2 * m ^ 2)
  have hc' : 0 < c' := by positivity
  have hs_div : Tendsto (fun x : ℝ => x / Real.log x) atTop atTop := by
    have hh : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
      simpa only [Real.rpow_one] using tendsto_log_power_div_sample 1
    have hwithin : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hh, by
        filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
        exact div_pos (Real.log_pos hx) (by linarith)⟩
    exact hwithin.inv_tendsto_nhdsGT_zero.congr fun x => by change (Real.log x / x)⁻¹ = x / Real.log x; rw [inv_div]
  have hconst : Tendsto (fun x : ℝ => Real.log 2 / (x / Real.log x)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using! hs_div.inv_tendsto_atTop.const_mul (Real.log 2)
  have hrate : Tendsto (fun x : ℝ => rateLog lam κ lp x / Real.log x) atTop (𝓝 (-lam)) := by
    convert! (tendsto_normalized_log_scale lam κ lp 0).neg using 1; funext x; ring
  have hsq : Tendsto (fun x : ℝ => (Real.log x) ^ (2 : ℕ) / x) atTop (𝓝 0) := by
    simpa only [Real.rpow_two] using tendsto_log_power_div_sample 2
  have hcorr : Tendsto (fun x : ℝ => rateLog lam κ lp x / (x / Real.log x)) atTop (𝓝 0) := by
    have hh := hrate.mul hsq; simp only [mul_zero] at hh
    refine hh.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx; field_simp [(Real.log_pos hx).ne']
  have hlog : Tendsto (fun x : ℝ =>
      (Real.log 2 - c' * x / Real.log x - 2 * rateLog lam κ lp x) / (x / Real.log x)) atTop (𝓝 (-c')) := by
    have hh := (hconst.sub (tendsto_const_nhds (x := c'))).sub (hcorr.const_mul 2)
    simp only [zero_sub, mul_zero, sub_zero] at hh
    refine hh.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx; field_simp [(Real.log_pos hx).ne']
  have hexp0 : Tendsto (fun x : ℝ => 2 * Real.exp (-c' * x / Real.log x) / (rateScale lam κ lp x) ^ 2)
      atTop (𝓝 0) := by
    refine (Real.tendsto_exp_atBot.comp (tendsto_atBot_of_div_negative hs_div hlog (neg_neg_of_pos hc'))).congr fun x => ?_
    change Real.exp (Real.log 2 - c' * x / Real.log x - 2 * rateLog lam κ lp x) = _
    rw [Real.exp_sub, Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    unfold rateScale
    rw [show 2 * rateLog lam κ lp x = ((2 : ℕ) : ℝ) * rateLog lam κ lp x by rfl, Real.exp_nat_mul,
      show -c' * x / Real.log x = -(c' * x / Real.log x) by ring, Real.exp_neg]
    ring
  refine squeeze_zero' (Eventually.of_forall fun _ => by unfold lowerSaddleExceptionalTail rateScale; positivity) ?_ hexp0
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (lowerSaddleM_tendsto_atTop hm).eventually (eventually_gt_atTop (0 : ℝ)),
    (lowerSaddleM_sq_div_log_limit hm).eventually (gt_mem_nhds (by nlinarith : m ^ 2 < 2 * m ^ 2)),
    (lowerSaddleMu_tends_zero hd0 hm hθ C).eventually (gt_mem_nhds one_pos)] with x hx hMp hMsq hMu
  have hx0 : 0 < x := by linarith
  have hH : (lowerSaddleH d m θ C x) ^ d ≤ 1 / x :=
    (le_div_iff₀ hx0).2 (by unfold lowerSaddleMu at hMu; simpa only [mul_comm] using hMu.le)
  have hbound : (lowerSaddleM m x : ℝ) ^ 2 * (lowerSaddleH d m θ C x) ^ d ≤ 2 * m ^ 2 * Real.log x / x :=
    (mul_le_mul_of_nonneg_left hH (sq_nonneg _)).trans
      (by simpa only [one_div, div_eq_mul_inv, mul_assoc, one_mul] using
        mul_le_mul_of_nonneg_right ((div_lt_iff₀ (Real.log_pos hx)).1 hMsq).le (inv_nonneg.2 hx0.le))
  have hden : 0 < (lowerSaddleM m x : ℝ) ^ 2 * (lowerSaddleH d m θ C x) ^ d :=
    mul_pos (sq_pos_of_pos hMp) (Real.rpow_pos_of_pos (lowerSaddleH_positive d m θ C x) d)
  have hh := div_le_div_of_nonneg_left hc.le hden hbound
  rw [show c / (2 * m ^ 2 * Real.log x / x) = c' * x / Real.log x by dsimp [c']; field_simp] at hh
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
  unfold lowerSaddleExceptionalTail
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by convert neg_le_neg hh using 1 <;> ring)) (by norm_num)

end LowerEndpointAndSaddle

end NearlyMinimax
