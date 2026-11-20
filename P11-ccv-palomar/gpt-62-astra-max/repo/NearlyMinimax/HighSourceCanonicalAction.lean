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
    {C : ModelConstants d} (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    {Cfr lam ℓ N μ : ℝ} (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
    {j : HighWindowLabels d k}
    (h : HighCompleteSourceHistory C k D M q Cfr lam ℓ N μ)
    {x : DesignSample d n} (hx : ∀ u, x u ∈ highTorusPatch j)
    {Φ : (HighFrameVector d D) → ℝ} (hmΦ : Measurable Φ)
    {B : ℝ} (hB : 0 ≤ B) (hΦ : ∀ v : HighFrameVector d D,
      (∑ γ, |v γ|) ≤ Cfr⁻¹ → |Φ v| ≤ B) :
    let R := completeSourceRows C k D M q Cfr lam ℓ N μ
    (∫ e, highUnionActivation R (highCenterMix C) e*
      ((∏ u, highUnionSourceResetDensity C R j h e (x u))*
        Φ (highUnionSourceResetCoefficient C R j h e)) ∂highUnionLaw R (highCenterMix C)) =
      completeSourceSignedFirstAction (C.densityLower+1/(M : ℝ))
        (C.densityUpper-1/(M : ℝ)) lam ℓ N μ M q Cfr
        (fun u => highLocalCoordinates j (x u))
        (fun u => highUnionSourceDensity C R h (x u)) ((highUnionSourceState C R h).2 j) Φ := by
  dsimp
  let ad := C.densityLower+1/(M : ℝ)
  let bd := C.densityUpper-1/(M : ℝ)
  let R := completeSourceRows C k D M q Cfr lam ℓ N μ
  let G := completeSourceRows_guards k hD hq hM lam μ hCfr hℓ hℓN
  let c := (highUnionSourceState C R h).2 j
  let p := fun u : Fin n => highUnionSourceDensity C R h (x u)
  let U := fun u : Fin n => highLocalCoordinates j (x u)
  let O := fun e => (∏ u, highUnionSourceResetDensity C R j h e (x u))*
    Φ (highUnionSourceResetCoefficient C R j h e)
  let mark := SourceRowMark d D M q ad bd Cfr lam ℓ N μ
  letI : StandardBorelSpace (HighUnionMark (mark)) :=
    highUnionMark_standardBorel
  have hc := highUnionSourceState_coefficient_ball C R G h j
  have hmCoef : Measurable (highUnionSourceResetCoefficient C R j h) :=
    measurable_pi_iff.mpr (highUnionSourceResetCoefficient_measurable C R G j h)
  have hmO : Measurable O := (Finset.measurable_fun_prod _ (fun u _ =>
    (highUnionSourceResetDensity_measurable C R G j h).comp
      (measurable_id.prodMk measurable_const))).mul (hmΦ.comp hmCoef)
  have hOb (e) : ‖O e‖ ≤ C.densityUpper^n*B := by
    change |(∏ u, highUnionSourceResetDensity C R j h e (x u))*Φ _| ≤ _
    rw [abs_mul]
    exact mul_le_mul (finite_density_product_abs_bound _
      (lt_trans zero_lt_one C.one_lt_densityUpper).le
      (fun u => highUnionSourceResetDensity_abs_le C R G j h e (x u)))
      (hΦ _ (highUnionResponseReset_ball R (by linarith) G.vector_ball G.time_interval e hc))
      (abs_nonneg _) (pow_nonneg (lt_trans zero_lt_one C.one_lt_densityUpper).le n)
  have hreset (i) (e : mark i) (u) :
      highUnionSourceResetDensity C R j h (Sum.inl ⟨i,e⟩) (x u) =
      R.rowSlope j i e (x u)*p u+R.rowIntercept i e := by
    unfold highUnionSourceResetDensity highUnionSourceDensity
    rw [highUnionSourceState_append]
    change (if x u ∈ highTorusPatch j then R.rowSlope j i e (x u)*_+R.rowIntercept i e else _) = _
    rw [if_pos (hx u)]
    dsimp [p]
    unfold highUnionSourceDensity
    rfl
  have hO (i) (e : mark i) :
      O (Sum.inl ⟨i,e⟩) = (∏ u, (R.rowSlope j i e (x u)*p u+R.rowIntercept i e))*
        Φ (coefficientReset c (R.rowVector i e) (R.rowTime i e)) := by
    simp only [O,hreset,highUnionSourceResetCoefficient,highUnionResponseReset,
      highUnionResponseVector,highUnionResponseTime,Sum.elim_inl,c]
  rw [completeSourceUnion_signed_action hD hq hM hCfr hℓ hℓN hmO hOb]
  change (∑ i : SourceRowIndex d D M q ad bd Cfr lam ℓ N μ,
      ∫ᵛ e, O (Sum.inl ⟨i,e⟩) ∂<•sourceRowSignedMeasure k i) =
    completeSourceSignedFirstAction ad bd lam ℓ N μ M q Cfr U p c Φ
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]
  have hunit : (∫ᵛ e, O (Sum.inl ⟨Sum.inl FinePairRowTag.unit,e⟩)
      ∂<•sourceRowSignedMeasure k (a := ad) (b := bd) (C := Cfr) (lam := lam) (ℓ := ℓ) (N := N) (μ := μ) (.inl .unit)) =
      finePairUnitFirstAction ad bd D q Cfr p c Φ := by
    unfold finePairUnitFirstAction sourceRowSignedMeasure
    congr 1
    funext e
    rw [hO]
    apply congrArg (fun t => t*Φ (coefficientReset c (highResponseMarkAtom Cfr e.2.2).2
      (highResponseMarkAtom Cfr e.2.2).1))
    dsimp
    apply Finset.prod_congr rfl
    intro u _
    simp only [R,completeSourceRows,sourceRowData,sourceRowComponent,highUnionRowRestrict,
      finePairRowData,finePairRowSlope,finePairRowIntercept,highPacketSlope,highPacketIntercept,
      highPacketObservable,localDensityReset]
    ring
  have hcoarse : (∫ᵛ e, O (Sum.inl ⟨Sum.inl FinePairRowTag.coarse,e⟩)
      ∂<•sourceRowSignedMeasure k (a := ad) (b := bd) (C := Cfr) (lam := lam) (ℓ := ℓ) (N := N) (μ := μ) (.inl .coarse)) =
      finePairCoarseFirstAction ad bd ℓ D q Cfr U p c Φ := by
    unfold finePairCoarseFirstAction sourceRowSignedMeasure
    congr 1
    funext e
    rw [hO]
    apply congrArg (fun t => t*Φ (coefficientReset c (highResponseMarkAtom Cfr e.2.2).2
      (highResponseMarkAtom Cfr e.2.2).1))
    dsimp
    apply Finset.prod_congr rfl
    intro u _
    simp only [R,completeSourceRows,sourceRowData,sourceRowComponent,highUnionRowRestrict,
      finePairRowData,finePairRowSlope,finePairRowIntercept,highPacketSlope,highPacketIntercept,
      highPacketObservable,localDensityReset,U]
    ring
  have hfine : (∫ᵛ e, O (Sum.inl ⟨Sum.inl FinePairRowTag.fine,e⟩)
      ∂<•sourceRowSignedMeasure k (a := ad) (b := bd) (C := Cfr) (lam := lam) (ℓ := ℓ) (N := N) (μ := μ) (.inl .fine)) =
      finePairFineFirstAction ad bd ℓ N M q Cfr U p c Φ := by
    unfold finePairFineFirstAction sourceRowSignedMeasure
    congr 1
    funext e
    rw [hO]
    apply congrArg (fun t => t*Φ (coefficientReset c (highResponseMarkAtom Cfr e.2.2).2
      (highResponseMarkAtom Cfr e.2.2).1))
    dsimp
    apply Finset.prod_congr rfl
    intro u _
    simp only [R,completeSourceRows,sourceRowData,sourceRowComponent,highUnionRowRestrict,
      finePairRowData,finePairRowSlope,finePairRowIntercept,finePairPacketSlope,finePairPacketIntercept,
      finePairPacketObservable,finePairDensityReset,U]
    ring
  have hsingle : (∫ᵛ e, O (Sum.inl ⟨Sum.inr (Sum.inl ()),e⟩)
      ∂<•sourceRowSignedMeasure k (a := ad) (b := bd) (C := Cfr) (lam := lam) (ℓ := ℓ) (N := N) (μ := μ) (.inr (.inl ()))) =
      singletonFirstAction ad bd q Cfr p c Φ := by
    unfold singletonFirstAction sourceRowSignedMeasure
    congr 1
    funext e
    rw [hO]
    apply congrArg (fun t => t*Φ (coefficientReset c (highResponseMarkAtom Cfr e.2.2).2
      (highResponseMarkAtom Cfr e.2.2).1))
    dsimp
    apply Finset.prod_congr rfl
    intro u _
    simp only [R,completeSourceRows,sourceRowData,sourceRowComponent,singletonRowData,
      highPacketSlope,highPacketIntercept,highPacketObservable,localDensityReset]
    ring
  have hhigher (i : HigherBandFamilyIndex d D M q ad bd Cfr lam ℓ N μ) :
      (∫ᵛ e, O (Sum.inl ⟨Sum.inr (Sum.inr i),e⟩)
        ∂<•sourceRowSignedMeasure k (.inr (.inr i))) =
      higherBandFirstAction ad bd lam ℓ (higherBandFamilyUpper d ℓ N μ i.val)
        (higherBandFamilyTarget i.val) (higherBandFamilyGuardDegree M i.val) q Cfr i.val.2 U p c Φ := by
    unfold higherBandFirstAction sourceRowSignedMeasure
    congr 1
    funext e
    rw [hO]
    apply congrArg (fun t => t*Φ (coefficientReset c (highResponseMarkAtom Cfr e.2.2).2
      (highResponseMarkAtom Cfr e.2.2).1))
    dsimp
    apply Finset.prod_congr rfl
    intro u _
    simp only [R,completeSourceRows,sourceRowData,sourceRowComponent,higherBandFamilyComponent,
      higherBandRowData,highPacketSlope,highPacketIntercept,highPacketObservable,localDensityReset,U]
    ring
  have htags : (Finset.univ : Finset FinePairRowTag) = {.unit,.coarse,.fine} := by decide
  simp [htags]
  simp [hunit,hcoarse,hfine,hsingle,hhigher,Fintype.sum_unique,
    completeSourceSignedFirstAction,finePairThreeRowFirstAction,add_assoc]

end NearlyMinimax
