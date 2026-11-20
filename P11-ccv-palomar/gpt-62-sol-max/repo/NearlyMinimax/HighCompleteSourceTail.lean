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

def highMarkedLocalScoreNumerator {ι E : Type*} [Fintype ι] [MeasurableSpace E] {n : ℕ}
    (π : Measure E) (activation : E → ℝ) (a V η : ℝ)
    (p : Fin n → ℝ) (pReset : E → Fin n → ℝ) (cReset : E → ι → ℝ)
    (g w : Fin n → ℝ) (φ : Fin n → ι → ℝ) (c : ι → ℝ) (y : Fin n → Fin 3) : ℝ :=
  highMarkedResponseAction π activation a V η pReset cReset g w φ y -
    η^2*(∏ u, p u)*∑ u, (w u)^2*highResponseVarianceTerm a V η g w φ c y u

section Complete
variable {d k D M q n : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
  (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
  (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
  (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)

local notation "R" => completeSourceRows C k D M q Cfr lam ℓ N μ
include hD hq hM hCfr hℓ hℓN

section
variable (hn : 1 ≤ n)
    (j : HighWindowLabels d k)
    (h : HighCompleteSourceHistory C k D M q Cfr lam ℓ N μ)
    (a V η ρ : ℝ)
    (x : Fin n → Covariate d) (g w : Fin n → ℝ)
    (φ : Fin n → HighFrameIndex d D → ℝ)
    (H : ResponseGuards Cfr a V η ρ g w φ) (y : Fin n → Fin 3)
include hn H

theorem completeSourceResponseAction_all_count_bound :
    |highMarkedResponseAction (highUnionLaw R (highCenterMix C))
      (highUnionActivation R (highCenterMix C)) a V η
      (fun e u => highUnionSourceResetDensity C R j h e (x u))
      (highUnionSourceResetCoefficient C R j h) g w φ y| ≤
      (C.densityUpper^n*highSeparatedDerivativeBudget a ρ*(n : ℝ)^2*η^2)*
        highRowTotalMass (R).rowMass := by
  let ad := C.densityLower+1/(M : ℝ)
  let bd := C.densityUpper-1/(M : ℝ)
  obtain ⟨G, hpos⟩ := completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN
  have hCf := H.frame_pos
  letI : StandardBorelSpace (HighUnionMark (SourceRowMark d D M q ad bd Cfr lam ℓ N μ)) :=
    highUnionMark_standardBorel
  let c := (highUnionSourceState C R h).2 j
  have hc := highUnionSourceState_coefficient_ball C R G h j
  let β₀ : HighFrameIndex d D := ⟨fun _ => 0,by simp⟩
  let r₀ : HighResponseMarkIndex (HighFrameIndex d D) q := ((β₀,β₀),(false,false),0)
  let reset :=
    fun i z u => highUnionSourceResetDensity C R j h
      (Sum.inl ⟨i,sourceRowDensityLift d D M q ad bd Cfr lam ℓ N μ r₀ i z⟩) (x u)
  have hresetMeas (i) (u) : Measurable (fun z => reset i z u) := by
    exact (highUnionSourceResetDensity_measurable C R G j h).comp
      (((measurable_inl.comp ((measurable_sigma_mk_actual i).comp
        (sourceRowDensityLift_measurable d D M q ad bd Cfr lam ℓ N μ r₀ i))).prodMk measurable_const))
  have hresetBound (i) (z) (u) : |reset i z u| ≤ C.densityUpper :=
    highUnionSourceResetDensity_abs_le C R G j h _ _
  have hirrel (i) (e : SourceRowMark d D M q ad bd Cfr lam ℓ N μ i) (u) :
      highUnionSourceResetDensity C R j h (Sum.inl ⟨i,e⟩) (x u) =
      reset i (sourceRowDensityProj d D M q ad bd Cfr lam ℓ N μ i e) u :=
    completeSourceResetDensity_project C Cfr lam ℓ N μ j h r₀ i e (x u)
  let Φ := fun v => highResponseProduct a V η g w φ v y
  let O := highUnionSourceResetObservable C R j h x Φ
  obtain ⟨hmO, hOb⟩ := highUnionSourceResetObservable_facts C R G hCf j h x Φ
    (highMarkedResponseProduct_measurable a V η _ (fun i => measurable_pi_apply i) g w φ y)
    1 (fun _ hv => H.product_abs_le hv y)
  have he : highMarkedResponseAction (highUnionLaw R (highCenterMix C))
      (highUnionActivation R (highCenterMix C)) a V η
      (fun e u => highUnionSourceResetDensity C R j h e (x u))
      (highUnionSourceResetCoefficient C R j h) g w φ y =
      ∑ i, highMarkedResponseAction ((R).rowLaw i) ((R).rowActivation i) a V η
        (fun e => reset i (sourceRowDensityProj d D M q ad bd Cfr lam ℓ N μ i e))
        (fun e => coefficientReset c ((R).rowVector i e) ((R).rowTime i e)) g w φ y := by
    unfold highMarkedResponseAction
    simp_rw [mul_assoc]
    change (∫ e, highUnionActivation R (highCenterMix C) e * O e ∂highUnionLaw R (highCenterMix C)) = _
    rw [highUnionSource_bounded_action C R G hpos O hmO _ hOb]
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [] with e
    simp only [O,highUnionSourceResetObservable,Φ,hirrel,highUnionSourceResetCoefficient,highUnionResponseReset,
      highUnionResponseVector,highUnionResponseTime,Sum.elim_inl,c]
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun i _ =>
    sourceRow_reference_all_count_bound d k D M q hn ad bd Cfr lam ℓ N μ a V η ρ C.densityUpper
      (lt_trans zero_lt_one C.one_lt_densityUpper).le hpos i (reset i) (hresetMeas i) (hresetBound i)
      g w φ c H hc y)).trans_eq
  exact (Finset.mul_sum _ _ _).symm

theorem completeSourceNumerator_all_count_exponential_bound :
    |highMarkedLocalScoreNumerator (highUnionLaw R (highCenterMix C))
      (highUnionActivation R (highCenterMix C)) a V η
      (fun u => highUnionSourceDensity C R h (x u))
      (fun e u => highUnionSourceResetDensity C R j h e (x u))
      (highUnionSourceResetCoefficient C R j h) g w φ ((highUnionSourceState C R h).2 j) y| ≤
      (highSeparatedScoreExponentialConstant a ρ C.densityUpper 1 1)^n *
        η^2*(highRowTotalMass (R).rowMass+1) := by
  have G := (completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN).1
  let c := (highUnionSourceState C R h).2 j
  let B := highRowTotalMass (R).rowMass
  have hc := highUnionSourceState_coefficient_ball C R G h j
  have hIncoming (u) : |highUnionSourceDensity C R h (x u)| ≤ C.densityUpper := by
    have hi := highUnionSourceDensity_coarse_interval C R G h (x u)
    rw [abs_of_nonneg (C.densityLower_pos.le.trans hi.1)]
    exact hi.2
  have haction := completeSourceResponseAction_all_count_bound C hD hq hM Cfr lam ℓ N μ
    hCfr hℓ hℓN hn j h a V η ρ x g w φ H y
  have hcorrection := high_response_variance_correction_abs_bound hn a V η C.densityUpper
    H.scale_pos (lt_trans zero_lt_one C.one_lt_densityUpper).le (fun u => highUnionSourceDensity C R h (x u)) g w φ c
    H.weight hIncoming (H.mass_nonneg hc) y
  have hraw : |highMarkedLocalScoreNumerator (highUnionLaw R (highCenterMix C))
      (highUnionActivation R (highCenterMix C)) a V η
      (fun u => highUnionSourceDensity C R h (x u))
      (fun e u => highUnionSourceResetDensity C R j h e (x u))
      (highUnionSourceResetCoefficient C R j h) g w φ c y| ≤
      C.densityUpper^n*(highSeparatedDerivativeBudget a ρ*B+1/a^2)*(n : ℝ)^2*η^2 := by
    unfold highMarkedLocalScoreNumerator
    apply (abs_sub _ _).trans
    apply (add_le_add haction hcorrection).trans_eq <;> ring
  apply hraw.trans
  simpa only [mul_one,div_one] using highSeparated_score_budget_absorb n hn a ρ C.densityUpper
    1 1 η B (lt_trans zero_lt_one C.one_lt_densityUpper).le (by norm_num) (by norm_num) G.total_positive.le

end

end Complete
end NearlyMinimax
