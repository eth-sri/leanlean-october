module

public import NearlyMinimax.HighSourceRowTail
public import NearlyMinimax.HighUnionScorePrimitives


@[expose] public section

/-! The genuine complete-source all-count raw response numerator bound.
Every source row is integrated on its actual positive reference law;
the variance derivative is subtracted exactly once after their union. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

section
variable {ι E : Type*} [Fintype ι]

def highMarkedLocalScoreNumerator [MeasurableSpace E] {n : ℕ}
    (π : Measure E) (activation : E → ℝ) (a V η : ℝ)
    (p : Fin n → ℝ) (pReset : E → Fin n → ℝ) (cReset : E → ι → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : TernaryVector n) : ℝ :=
  highMarkedResponseAction π activation a V η pReset cReset g w φ y -
    η^2*(∏ u, p u)*∑ u, (w u)^2*highResponseVarianceTerm a V η g w φ c y u


end

section Complete
variable {d k D M q n : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
  (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
  (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)

local notation "R" => completeSourceRows C k D M q Cfr lam ℓ N μ
include hD hq hM hCfr hℓ hℓN

variable (hn : 1 ≤ n) (j : HighWindowLabels d k)
    (h : HighCompleteSourceHistory C k D M q Cfr lam ℓ N μ)
include hn

theorem completeSourceResponseAction_all_count_bound
    {a V η ρ : ℝ} (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ/2)
    (x : DesignSample d n) {g w : Fin n → ℝ}
    {φ : Fin n → HighFrameVector d D}
    (hg : ∀ u, |g u| ≤ ρ/2) (hw : ∀ u, |w u| ≤ 1)
    (hφ : ∀ v : HighFrameVector d D, (∑ γ, |v γ|) ≤ Cfr⁻¹ →
      ∀ u, |∑ γ, φ u γ*v γ| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y) (y : TernaryVector n) :
    |highMarkedResponseAction (highUnionLaw R (highCenterMix C))
      (highUnionActivation R (highCenterMix C)) a V η
      (fun e u => highUnionSourceResetDensity C R j h e (x u))
      (highUnionSourceResetCoefficient C R j h) g w φ y| ≤
      (C.densityUpper^n*highSeparatedDerivativeBudget a ρ*(n : ℝ)^2*η^2)*
        highRowTotalMass (R).rowMass := by
  let ad := C.densityLower+1/(M : ℝ)
  let bd := C.densityUpper-1/(M : ℝ)
  let G := completeSourceRows_guards k hD hq hM lam μ hCfr hℓ hℓN
  have hCf : 0 < Cfr := by linarith
  obtain ⟨had,hadbd⟩ := high_source_interval_numeric hM
  have hpos := sourceRowMass_positive_actual d k D M q hD hq had hadbd Cfr hCf
    lam ℓ N μ hℓ hℓN
  letI : StandardBorelSpace (HighUnionMark (SourceRowMark d D M q ad bd Cfr lam ℓ N μ)) :=
    highUnionMark_standardBorel
  let c := (highUnionSourceState C R h).2 j
  have hc  := highUnionSourceState_coefficient_ball C R G h j
  let β₀ : HighFrameIndex d D := ⟨fun _ => 0,by simp⟩
  let r₀ : HighResponseMarkIndex (HighFrameIndex d D) q := ((β₀,β₀),(false,false),0)
  let reset  :=
    fun i z u => highUnionSourceResetDensity C R j h
      (Sum.inl ⟨i,sourceRowDensityLift M ad bd Cfr lam ℓ N μ r₀ i z⟩) (x u)
  have hresetMeas (i) (u) : Measurable (fun z => reset i z u) := (highUnionSourceResetDensity_measurable C R G j h).comp
      (((measurable_inl.comp ((measurable_sigma_mk_actual i).comp
        (sourceRowDensityLift_measurable M q ad bd Cfr lam ℓ N μ r₀ i))).prodMk measurable_const))
  have hresetBound (i) (z) (u) : |reset i z u| ≤ C.densityUpper :=
    highUnionSourceResetDensity_abs_le C R G j h _ _
  have hirrel (i) (e : SourceRowMark d D M q ad bd Cfr lam ℓ N μ i) (u) :
      highUnionSourceResetDensity C R j h (Sum.inl ⟨i,e⟩) (x u) =
      reset i (sourceRowDensityProj d D M q ad bd Cfr lam ℓ N μ i e) u := by
    dsimp [reset]
    unfold highUnionSourceResetDensity
    unfold highUnionSourceDensity
    rw [highUnionSourceState_append,highUnionSourceState_append]
    change (if x u ∈ highTorusPatch j then (R).rowSlope j i e (x u)*_+(R).rowIntercept i e else _) =
      (if x u ∈ highTorusPatch j then (R).rowSlope j i
        (sourceRowDensityLift M ad bd Cfr lam ℓ N μ r₀ i
          (sourceRowDensityProj d D M q ad bd Cfr lam ℓ N μ i e)) (x u)*_+
        (R).rowIntercept i (sourceRowDensityLift M ad bd Cfr lam ℓ N μ r₀ i
          (sourceRowDensityProj d D M q ad bd Cfr lam ℓ N μ i e)) else _)
    simp [completeSourceRows]
    rw [sourceRow_density_projection_slope d k D M q ad bd Cfr lam ℓ N μ r₀ j i e (x u),
      sourceRow_density_projection_intercept d k D M q ad bd Cfr lam ℓ N μ r₀ i e]
  let O := fun e => (∏ u, highUnionSourceResetDensity C R j h e (x u))*
    highResponseProduct a V η g w φ (highUnionSourceResetCoefficient C R j h e) y
  have hmO : Measurable O := (Finset.measurable_fun_prod _ (fun u _ =>
    (highUnionSourceResetDensity_measurable C R G j h).comp
      (measurable_id.prodMk measurable_const))).mul
        (highMarkedResponseProduct_measurable a V η _
          (highUnionSourceResetCoefficient_measurable C R G j h) g w φ y)
  have hOb (e) : ‖O e‖ ≤ C.densityUpper^n := by
    have hcReset := highUnionResponseReset_ball R hCf G.vector_ball G.time_interval e hc
    have hResponse := highResponseProduct_ball_abs_le_one ha.ne' hη hηρ hg hw hφ hp hcReset y
    change |(∏ u, highUnionSourceResetDensity C R j h e (x u))*highResponseProduct a V η g w φ _ y| ≤ _
    rw [abs_mul]
    exact (mul_le_mul (finite_density_product_abs_bound _ (lt_trans zero_lt_one C.one_lt_densityUpper).le
      (fun u => highUnionSourceResetDensity_abs_le C R G j h e (x u))) hResponse
        (abs_nonneg _) (pow_nonneg (lt_trans zero_lt_one C.one_lt_densityUpper).le _)).trans_eq (mul_one _)
  have he : highMarkedResponseAction (highUnionLaw R (highCenterMix C))
      (highUnionActivation R (highCenterMix C)) a V η
      (fun e u => highUnionSourceResetDensity C R j h e (x u))
      (highUnionSourceResetCoefficient C R j h) g w φ y =
      ∑ i, highMarkedResponseAction ((R).rowLaw i) ((R).rowActivation i) a V η
        (fun e => reset i (sourceRowDensityProj d D M q ad bd Cfr lam ℓ N μ i e))
        (fun e => coefficientReset c ((R).rowVector i e) ((R).rowTime i e)) g w φ y := by
    unfold highMarkedResponseAction
    simp_rw [mul_assoc]
    rw [highUnionSource_bounded_action G hpos hmO hOb]
    simp only [O,hirrel,highUnionSourceResetCoefficient,highUnionResponseReset,
      highUnionResponseVector,highUnionResponseTime,Sum.elim_inl,c]
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun i _ =>
    sourceRow_reference_all_count_bound hn
      hCf ha hη hρ hηρ (lt_trans zero_lt_one C.one_lt_densityUpper).le hpos (hresetMeas i) (hresetBound i) hc hg hw hφ hp y)).trans_eq
  exact (Finset.mul_sum _ _ _).symm

theorem completeSourceNumerator_all_count_exponential_bound
    (a V η ρ : ℝ) (ha : 0 < a) (hη : 0 ≤ η) (hρ : 0 ≤ ρ) (hηρ : η ≤ ρ/2)
    (x : DesignSample d n) {g w : Fin n → ℝ}
    {φ : Fin n → HighFrameVector d D}
    (hg : ∀ u, |g u| ≤ ρ/2) (hw : ∀ u, |w u| ≤ 1)
    (hφ : ∀ v : HighFrameVector d D, (∑ γ, |v γ|) ≤ Cfr⁻¹ →
      ∀ u, |∑ γ, φ u γ*v γ| ≤ 1)
    (hp : ∀ f : ℝ, |f| ≤ ρ → ∀ y, 0 ≤ ternaryMass a f V y) (y : TernaryVector n) :
    let numerator := highMarkedLocalScoreNumerator (highUnionLaw R (highCenterMix C)) (highUnionActivation R (highCenterMix C)) a V η (fun u => highUnionSourceDensity C R h (x u)) (fun e u => highUnionSourceResetDensity C R j h e (x u)) (highUnionSourceResetCoefficient C R j h) g w φ
    |numerator ((highUnionSourceState C R h).2 j) y| ≤
      (highSeparatedScoreExponentialConstant a ρ C.densityUpper 1 1)^n *
        η^2*(highRowTotalMass (R).rowMass+1) := by
  intro numerator
  let G := completeSourceRows_guards k hD hq hM lam μ hCfr hℓ hℓN
  let c := (highUnionSourceState C R h).2 j
  let B := highRowTotalMass (R).rowMass
  have hc := highUnionSourceState_coefficient_ball C R G h j
  have hpCurrent (u) (b) : 0 ≤ ternaryMass a (coefficientRegression η g w φ c u) V b := by
    apply hp _
    have hv := hφ c hc u
    have hh : |η*w u*(∑ γ, φ u γ*c γ)| ≤ η := by
      rw [abs_mul,abs_mul,abs_of_nonneg hη]
      have ht := mul_le_mul (hw u) hv (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      nlinarith [mul_le_mul_of_nonneg_left ht hη]
    exact (abs_add_le _ _).trans (by linarith [hg u])
  have hIncoming (u) : |highUnionSourceDensity C R h (x u)| ≤ C.densityUpper := by
    have hi := highUnionSourceDensity_coarse_interval C R G h (x u)
    rw [abs_of_nonneg (C.densityLower_pos.le.trans hi.1)]
    exact hi.2
  have haction := completeSourceResponseAction_all_count_bound C hD hq hM Cfr lam ℓ N μ
    hCfr hℓ hℓN hn j h ha hη hρ hηρ x hg hw hφ hp y
  have hcorrection := high_response_variance_correction_abs_bound hn
    ha (lt_trans zero_lt_one C.one_lt_densityUpper).le
    hw hIncoming hpCurrent y
  have hraw : |numerator c y| ≤
      C.densityUpper^n*(highSeparatedDerivativeBudget a ρ*B+1/a^2)*(n : ℝ)^2*η^2 := by
    apply (abs_sub _ _).trans
    linarith
  apply hraw.trans
  simpa using highSeparated_score_budget_absorb hn a ρ C.densityUpper
    1 1 η B (lt_trans zero_lt_one C.one_lt_densityUpper).le (by norm_num) (by norm_num) G.total_positive.le

end Complete
end NearlyMinimax
