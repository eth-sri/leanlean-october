module

public import NearlyMinimax.HighCompleteSourceTail


@[expose] public section

/-! Conversion of the true positive activated complete-source reference
law into the genuine signed atom packets. All spatial/field carriers and
finite response marks remain in their actual signed measures. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable

def sourceRowSignedMeasure {d : ℕ} (k : ℕ) {D M q : ℕ} {a b C lam ℓ N μ : ℝ} :
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) →
      SignedMeasure (SourceRowMark d D M q a b C lam ℓ N μ i)
  | .inl .unit => highPacketSignedMeasure (Measure.dirac ()) a b D 2 D q C
      (fun _ => finePairUnitMatrix d D)
  | .inl .coarse => highPacketSignedMeasure (finePairTimeFieldMeasure d 0 ℓ) a b D 2 D q C
      (finePairTimeMatrix d (finePairDistanceMatrix d D))
  | .inl .fine => finePairPacketSignedMeasure (finePairTimeFieldMeasure d ℓ N) a b M q C
      (finePairTimeMatrix d (finePairDistanceMatrix d D))
  | .inr (.inl _) => highPacketSignedMeasure (Measure.dirac ()) a b D 1 D q C
      (fun _ => finePairUnitMatrix d D)
  | .inr (.inr i) => higherBandSignedRow d (higherBandFamilyTarget i.val)
      (higherBandFamilyGuardDegree M i.val) D q a b C lam ℓ
      (higherBandFamilyUpper d ℓ N μ i.val) i.val.2

theorem sourceRow_activated_signed_action {d : ℕ} [NeZero d] {k D M q : ℕ}
    {a b C lam ℓ N μ : ℝ}
    (hpos : ∀ i, 0 < (sourceRowData d k D M q a b C lam ℓ N μ).rowMass i)
    {i : SourceRowIndex d D M q a b C lam ℓ N μ}
    {F : SourceRowMark d D M q a b C lam ℓ N μ i → ℝ} (hF : Measurable F)
    (L : ℝ) (hFbound : ∀ e, ‖F e‖ ≤ L) :
    let data := sourceRowData d k D M q a b C lam ℓ N μ
    (∫ e, (data).rowActivation i e * F e
      ∂(data).rowLaw i) =
      ∫ᵛ e, F e ∂<•sourceRowSignedMeasure k i := by
  cases i with
  | inl p =>
    cases p
    · exact absoluteMarkLaw_signed_action
        (w := (highPacketMarkWeight a b D 2 D q C (fun _ => finePairUnitMatrix d D)))
        (tensorWeight_integrable (densityPacketWeight a b D 2 D) q C
          (fun _ _ => measurable_const) (integrable_const _))
        (by fun_prop)
        (hpos (.inl .unit)) hF hFbound
    · exact absoluteMarkLaw_signed_action
        (tensorWeight_integrable (densityPacketWeight a b D 2 D) q C (finePairTimeMatrix_measurable d _)
          (finePairTimeMatrix_cost_integrable d 0 ℓ _))
        (tensorWeight_measurable (densityPacketWeight a b D 2 D) q C (finePairTimeMatrix_measurable d _))
        (hpos (.inl .coarse)) hF hFbound
    · exact absoluteMarkLaw_signed_action
        (tensorWeight_integrable (finePairDensityWeight a b M) q C (finePairTimeMatrix_measurable d _)
          (finePairTimeMatrix_cost_integrable d ℓ N _))
        (tensorWeight_measurable (finePairDensityWeight a b M) q C (finePairTimeMatrix_measurable d _))
        (hpos (.inl .fine)) hF hFbound
  | inr i =>
    cases i with
    | inl _ =>
      exact absoluteMarkLaw_signed_action
        (w := (highPacketMarkWeight a b D 1 D q C (fun _ => finePairUnitMatrix d D)))
        (tensorWeight_integrable (densityPacketWeight a b D 1 D) q C
          (fun _ _ => measurable_const) (integrable_const _))
        (by fun_prop)
        (hpos (.inr (.inl ()))) hF hFbound
    | inr i =>
      let r := higherBandFamilyTarget i.val
      let m := higherBandFamilyGuardDegree M i.val
      let T := higherBandFamilyUpper d ℓ N μ i.val
      letI := higherBandCarrierMeasure_finite d r ℓ i.property.1 i.val.2
      exact absoluteMarkLaw_signed_action
        (tensorWeight_integrable (densityPacketWeight a b m r D) q C
          (higherBandCarrierAmplitude_measurable d r D lam i.val.2)
          (higherBandCarrierAmplitude_cost_integrable d r D lam ℓ i.property.1 i.val.2))
        (tensorWeight_measurable (densityPacketWeight a b m r D) q C
          (higherBandCarrierAmplitude_measurable d r D lam i.val.2))
        (hpos (.inr (.inr i))) hF hFbound

/-- The entire canonical source generator is an actual finite sum of
its constructed signed packet integrals, with numerical source guards. -/
theorem completeSourceUnion_signed_action {d k D M q : ℕ} [NeZero d]
    {C : ModelConstants d} (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    {Cfr lam ℓ N μ : ℝ} (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
    {F : HighUnionMark (SourceRowMark d D M q (C.densityLower+1/(M : ℝ))
      (C.densityUpper-1/(M : ℝ)) Cfr lam ℓ N μ) → ℝ} (hF : Measurable F)
    {L : ℝ} (hFbound : ∀ e, ‖F e‖ ≤ L) :
    let R := completeSourceRows C k D M q Cfr lam ℓ N μ
    (∫ e, highUnionActivation R (highCenterMix C) e*F e ∂highUnionLaw R (highCenterMix C)) =
      ∑ i, ∫ᵛ e, F (Sum.inl ⟨i,e⟩)
        ∂<•sourceRowSignedMeasure k i := by
  dsimp
  let a := C.densityLower+1/(M : ℝ)
  let b := C.densityUpper-1/(M : ℝ)
  let R := completeSourceRows C k D M q Cfr lam ℓ N μ
  let G := completeSourceRows_guards k hD hq hM lam μ hCfr hℓ hℓN
  obtain ⟨ha,hab⟩ := high_source_interval_numeric hM
  have hpos := sourceRowMass_positive_actual d k D M q hD hq ha hab Cfr
    (by linarith) lam ℓ N μ hℓ hℓN
  rw [highUnionSource_bounded_action G hpos hF hFbound]
  apply Finset.sum_congr rfl
  intro i _
  exact sourceRow_activated_signed_action hpos
    (hF.comp (measurable_inl.comp (measurable_sigma_mk_actual i))) L (fun e => hFbound _)

end NearlyMinimax
