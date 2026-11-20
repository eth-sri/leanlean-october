module

public import NearlyMinimax.HighSourceUnionAction
public import NearlyMinimax.HighSourceRawDecomposition


@[expose] public section

/-! Exact canonical complete-source append action, converted to the
manuscript's genuine ordinary and fine-pair signed first actions. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
attribute [local instance] Classical.propDecidable
attribute [local irreducible] highUnionSourceDensity highUnionSourceState historyMarkedAppend

theorem completeSourceCanonicalAction_eq_signed_first_action
    {d k D M q n : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
    (j : HighWindowLabels d k)
    (h : HighCompleteSourceHistory C k D M q Cfr lam ℓ N μ)
    (x : Fin n → Covariate d) (hx : ∀ u, x u ∈ highTorusPatch d k j)
    (Φ : (HighFrameIndex d D → ℝ) → ℝ) (hmΦ : Measurable Φ)
    (B : ℝ) (hΦ : ∀ v : HighFrameIndex d D → ℝ,
      (∑ γ, |v γ|) ≤ Cfr⁻¹ → |Φ v| ≤ B) :
    let R := completeSourceRows C k D M q Cfr lam ℓ N μ
    (∫ e, highUnionActivation R (highCenterMix C) e*
      ((∏ u, highUnionSourceResetDensity C R j h e (x u))*
        Φ (highUnionSourceResetCoefficient C R j h e)) ∂highUnionLaw R (highCenterMix C)) =
      completeSourceSignedFirstAction (C.densityLower+1/(M : ℝ))
        (C.densityUpper-1/(M : ℝ)) lam ℓ N μ D M q Cfr
        (fun u => highLocalCoordinates d k j (x u))
        (fun u => highUnionSourceDensity C R h (x u)) ((highUnionSourceState C R h).2 j) Φ := by
  dsimp only
  let ad := C.densityLower+1/(M : ℝ)
  let bd := C.densityUpper-1/(M : ℝ)
  let R := completeSourceRows C k D M q Cfr lam ℓ N μ
  let G := (completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN).1
  let c := (highUnionSourceState C R h).2 j
  let p := fun u : Fin n => highUnionSourceDensity C R h (x u)
  let U := fun u : Fin n => highLocalCoordinates d k j (x u)
  let O := highUnionSourceResetObservable C R j h x Φ
  obtain ⟨hmO, hOb⟩ := highUnionSourceResetObservable_facts C R G
    (by linarith) j h x Φ hmΦ B hΦ
  have hreset (i) (e : SourceRowMark d D M q ad bd Cfr lam ℓ N μ i) (u) :
      highUnionSourceResetDensity C R j h (Sum.inl ⟨i,e⟩) (x u) =
      R.rowSlope j i e (x u)*p u+R.rowIntercept i e := by
    rw [highUnionSourceResetDensity_inl, if_pos (hx u)]
  have hO (i) (e : SourceRowMark d D M q ad bd Cfr lam ℓ N μ i) :
      O (Sum.inl ⟨i,e⟩) = (∏ u, (R.rowSlope j i e (x u)*p u+R.rowIntercept i e))*
        Φ (coefficientReset c (R.rowVector i e) (R.rowTime i e)) := by
    simp only [O,highUnionSourceResetObservable,hreset,highUnionSourceResetCoefficient,highUnionResponseReset,
      highUnionResponseVector,highUnionResponseTime,Sum.elim_inl,c]
  change (∫ e, highUnionActivation R (highCenterMix C) e * O e ∂highUnionLaw R (highCenterMix C)) = _
  rw [completeSourceUnion_signed_action C hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN O hmO
    (C.densityUpper^n*B) hOb]
  change (∑ i : SourceRowIndex d D M q ad bd Cfr lam ℓ N μ,
      ∫ᵛ e, O (Sum.inl ⟨i,e⟩) ∂<•sourceRowSignedMeasure d D M q ad bd Cfr lam ℓ N μ i) =
    completeSourceSignedFirstAction ad bd lam ℓ N μ D M q Cfr U p c Φ
  classical
  have htags : (Finset.univ : Finset FinePairRowTag) = {.unit, .coarse, .fine} := by decide
  simp [Fintype.sum_sum_type, htags, completeSourceSignedFirstAction,
    finePairThreeRowFirstAction, add_assoc]
  repeat' apply congrArg₂ (· + ·)
  all_goals try (apply Finset.sum_congr rfl; intro i _)
  all_goals
    first
    | unfold finePairUnitFirstAction
    | unfold finePairCoarseFirstAction
    | unfold finePairFineFirstAction
    | unfold singletonFirstAction
    | unfold higherBandFirstAction
    try unfold highPacketFirstAction
    unfold sourceRowSignedMeasure
    congr 1
    funext e
    rw [hO]
    apply congrArg (fun t => t*Φ (coefficientReset c (highResponseMarkAtom Cfr q e.2.2).2
      (highResponseMarkAtom Cfr q e.2.2).1))
    dsimp only
    apply Finset.prod_congr rfl
    intro u _
    simp only [R, completeSourceRows, sourceRowData, sourceRowComponent, highUnionRowRestrict,
      finePairRowData, finePairRowSlope, finePairRowIntercept, higherBandFamilyComponent,
      higherBandRowData, singletonRowData, highPacketRowData, highPacketSlope, highPacketIntercept,
      localDensityReset, finePairPacketSlope, finePairPacketIntercept, finePairDensityReset, U]
    ring

end NearlyMinimax
