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

abbrev sourceRowSignedMeasure (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) :
    SignedMeasure (SourceRowMark d D M q a b C lam ℓ N μ i) :=
  (sourceRowPacket d D M q a b C lam ℓ N μ i).signed q C

theorem sourceRow_activated_signed_action (d : ℕ) [NeZero d] (k D M q : ℕ)
    (a b C lam ℓ N μ : ℝ)
    (hpos : ∀ i, 0 < (sourceRowData d k D M q a b C lam ℓ N μ).rowMass i)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ)
    (F : SourceRowMark d D M q a b C lam ℓ N μ i → ℝ) (hF : Measurable F)
    (L : ℝ) (hFbound : ∀ e, ‖F e‖ ≤ L) :
    (∫ e, (sourceRowData d k D M q a b C lam ℓ N μ).rowActivation i e * F e
      ∂(sourceRowData d k D M q a b C lam ℓ N μ).rowLaw i) =
      ∫ᵛ e, F e ∂<•sourceRowSignedMeasure d D M q a b C lam ℓ N μ i := by
  let P := sourceRowPacket d D M q a b C lam ℓ N μ i
  obtain ⟨hfin, hA⟩ := sourceRowPacket_valid d D M q a b C lam ℓ N μ i
  exact responsePacket_activated_signed_action P.carrier P.weights q C P.amplitude hA (hpos i) F hF L hFbound

/-- The entire canonical source generator is an actual finite sum of
its constructed signed packet integrals, with numerical source guards. -/
theorem completeSourceUnion_signed_action {d k D M q : ℕ} [NeZero d]
    (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
    (F : HighUnionMark (SourceRowMark d D M q (C.densityLower+1/(M : ℝ))
      (C.densityUpper-1/(M : ℝ)) Cfr lam ℓ N μ) → ℝ) (hF : Measurable F)
    (L : ℝ) (hFbound : ∀ e, ‖F e‖ ≤ L) :
    let R := completeSourceRows C k D M q Cfr lam ℓ N μ
    (∫ e, highUnionActivation R (highCenterMix C) e*F e ∂highUnionLaw R (highCenterMix C)) =
      ∑ i, ∫ᵛ e, F (Sum.inl ⟨i,e⟩)
        ∂<•sourceRowSignedMeasure d D M q (C.densityLower+1/(M : ℝ))
          (C.densityUpper-1/(M : ℝ)) Cfr lam ℓ N μ i := by
  dsimp only
  let a := C.densityLower+1/(M : ℝ)
  let b := C.densityUpper-1/(M : ℝ)
  let R := completeSourceRows C k D M q Cfr lam ℓ N μ
  obtain ⟨G, hpos⟩ := completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN
  rw [highUnionSource_bounded_action C R G hpos F hF L hFbound]
  apply Finset.sum_congr rfl
  intro i _
  exact sourceRow_activated_signed_action d k D M q a b Cfr lam ℓ N μ hpos i
    (fun e => F (Sum.inl ⟨i,e⟩))
    (hF.comp (measurable_inl.comp (measurable_sigma_mk_actual i))) L (fun e => hFbound _)

end NearlyMinimax
