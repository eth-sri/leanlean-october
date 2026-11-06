module
public import NearlyMinimax.FinePairUnionMassAnnihilation
public import NearlyMinimax.CompleteSourceRows
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
theorem highUnionSourceMass_append_indicator_zero_of_density_projection
    {d k F : ℕ} [NeZero k] [LinearOrder (HighWindowLabels d k)]
     [Fintype I]  [∀ i, MeasurableSpace (E i)]
    [∀ i, StandardBorelSpace (E i)] (C )
    (R : HighUnionRowData d k F I E) {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
    (hpos : ∀ i, 0 < R.rowMass i)
    (D : I → Type*) [∀ i, MeasurableSpace (D i)]
    (project : (i : I) → E i → D i) (lift : (i : I) → D i → E i)
    (hlift : ∀ i, Measurable (lift i))
    (hSlope : ∀ j i e x, R.rowSlope j i e x = R.rowSlope j i (lift i (project i e)) x)
    (hIntercept : ∀ i e, R.rowIntercept i e = R.rowIntercept i (lift i (project i e)))
    (hRowZero : ∀ i, ∀ H : D i → ℝ, Measurable H → ∀ L : ℝ,
      (∀ z, ‖H z‖ ≤ L) → (∫ e, R.rowActivation i e * H (project i e) ∂(R.rowLaw i)) = 0)
    (j : HighWindowLabels d k)
    (h )
    (S : Set ℝ) (hS : MeasurableSet S) :
    (∫ e, S.indicator (fun _ => 1)
      (highUnionSourceMass C R (historyMarkedAppend
        (fun i j => j ∈ highNeighborLabels d k i)
        (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,e))) *
      highUnionActivation R (highCenterMix C) e ∂highUnionLaw R (highCenterMix C)) = 0 := by
  letI : StandardBorelSpace (HighUnionMark E) := highUnionMark_standardBorel
  let Fobs : HighUnionMark E → ℝ := fun e => S.indicator (fun _ => 1)
    (highUnionSourceMass C R (historyMarkedAppend
      (fun i j => j ∈ highNeighborLabels d k i)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,e)))
  have hF : Measurable Fobs := (measurable_const.indicator hS).comp
    ((highUnionSourceMass_measurable C R G).comp
      ((historyMarkedAppend_measurable _ _ j).comp (measurable_const.prodMk measurable_id)))
  have hFbound (e) : ‖Fobs e‖ ≤ 1 :=
    (norm_indicator_le_norm_self (s := S) (fun _ : ℝ => 1) _).trans_eq (by simp)
  have hmass (i : I) (e : E i) :
      highUnionSourceMass C R (historyMarkedAppend
        (fun i j => j ∈ highNeighborLabels d k i)
        (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,Sum.inl ⟨i,e⟩)) =
      highUnionSourceMass C R (historyMarkedAppend
        (fun i j => j ∈ highNeighborLabels d k i)
        (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j
          (h,Sum.inl ⟨i,lift i (project i e)⟩)) := by
    apply integral_congr_ae
    filter_upwards [] with x
    change (highUnionSourceState C R _).1 x = (highUnionSourceState C R _).1 x
    rw [highUnionSourceState_append,highUnionSourceState_append]
    change (if x ∈ highTorusPatch d k j then R.rowSlope j i e x * _ + R.rowIntercept i e else _) =
      (if x ∈ highTorusPatch d k j then R.rowSlope j i (lift i (project i e)) x * _ +
        R.rowIntercept i (lift i (project i e)) else _)
    rw [hSlope j i e x,hIntercept i e]
  have hrow (i : I) : (∫ e, R.rowActivation i e * Fobs (Sum.inl ⟨i,e⟩) ∂(R.rowLaw i)) = 0 := by
    let Hi : D i → ℝ := fun z => Fobs (Sum.inl ⟨i,lift i z⟩)
    have hHi  := hF.comp
      (measurable_inl.comp ((rowSigmaMk_measurable i).comp (hlift i)))
    have hf (e : E i) : Fobs (Sum.inl ⟨i,e⟩) = Hi (project i e) :=
      congrArg (S.indicator (fun _ => 1)) (hmass i e)
    calc
      _ = ∫ e, R.rowActivation i e * Hi (project i e) ∂(R.rowLaw i) :=
        integral_congr_ae (Filter.Eventually.of_forall (fun e => congrArg _ (hf e)))
      _ = 0 := hRowZero i Hi hHi 1 (fun z => hFbound _)
  calc
    _ = ∫ e, highUnionActivation R (highCenterMix C) e * Fobs e ∂highUnionLaw R (highCenterMix C) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun e => mul_comm _ _))
    _ = ∑ i, ∫ e, R.rowActivation i e * Fobs (Sum.inl ⟨i,e⟩) ∂(R.rowLaw i) :=
      highUnionSource_bounded_action C R G hpos Fobs hF 1 hFbound
    _ = 0 := by simp only [hrow,Finset.sum_const_zero]
abbrev SourceRowDensityMark (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    SourceRowIndex d D M q a b C lam ℓ N μ → Type
  | .inl p => FinePairRowDensityMark d D M p
  | .inr (.inl _) => Unit × HighDensityMarkIndex D 1 D
  | .inr (.inr i) => HigherBandCarrier d (higherBandFamilyTarget i.val) i.val.2 ×
      HighDensityMarkIndex (higherBandFamilyGuardDegree M i.val) (higherBandFamilyTarget i.val) D
instance sourceRowDensityMark_measurable (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) :
    MeasurableSpace (SourceRowDensityMark d D M q a b C lam ℓ N μ i) := by
  cases i with
  | inl p => infer_instance
  | inr i => cases i <;> dsimp [SourceRowDensityMark] <;> infer_instance
def sourceRowDensityProj (d D M q : ℕ) (a b C lam ℓ N μ : ℝ) :
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) →
      SourceRowMark d D M q a b C lam ℓ N μ i → SourceRowDensityMark d D M q a b C lam ℓ N μ i
  | .inl p => finePairRowDensityProj d D M q p
  | .inr (.inl _) => fun e => (e.1,e.2.1)
  | .inr (.inr _) => fun e => (e.1,e.2.1)
def sourceRowDensityLift (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (r : HighResponseMarkIndex (HighFrameIndex d D) q) :
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) →
      SourceRowDensityMark d D M q a b C lam ℓ N μ i → SourceRowMark d D M q a b C lam ℓ N μ i
  | .inl p => finePairRowWithResponse d D M q p r
  | .inr (.inl _) => fun e => (e.1,(e.2,r))
  | .inr (.inr _) => fun e => (e.1,(e.2,r))
theorem sourceRowDensityLift_measurable (d D M q a b C lam ℓ N μ r i) :
    Measurable (sourceRowDensityLift d D M q a b C lam ℓ N μ r i) := by
  cases i with
  | inl p => exact finePairRowWithResponse_measurable d D M q p r
  | inr i => cases i <;> exact measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
theorem sourceRow_density_projection_slope (d k D M q a b C lam ℓ N μ r j i e x) :
    (sourceRowData d k D M q a b C lam ℓ N μ).rowSlope j i e x =
    (sourceRowData d k D M q a b C lam ℓ N μ).rowSlope j i
      (sourceRowDensityLift d D M q a b C lam ℓ N μ r i
        (sourceRowDensityProj d D M q a b C lam ℓ N μ i e)) x := by
  cases i with
  | inl p => cases p <;> rfl
  | inr i => cases i <;> rfl
theorem sourceRow_density_projection_intercept (d k D M q a b C lam ℓ N μ r i e) :
    (sourceRowData d k D M q a b C lam ℓ N μ).rowIntercept i e =
    (sourceRowData d k D M q a b C lam ℓ N μ).rowIntercept i
      (sourceRowDensityLift d D M q a b C lam ℓ N μ r i
        (sourceRowDensityProj d D M q a b C lam ℓ N μ i e)) := by
  cases i with
  | inl p => cases p <;> rfl
  | inr i => cases i <;> rfl
theorem sourceRow_density_observable_zero (d ) [NeZero d] (k D M q a b C lam ℓ N μ)
    (hpos : ∀ i, 0 < (sourceRowData d k D M q a b C lam ℓ N μ).rowMass i)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ)
    (H ) (hH : Measurable H)
    (B ) (hB : ∀ z, ‖H z‖ ≤ B) :
    (∫ e, (sourceRowData d k D M q a b C lam ℓ N μ).rowActivation i e *
      H (sourceRowDensityProj d D M q a b C lam ℓ N μ i e)
      ∂(sourceRowData d k D M q a b C lam ℓ N μ).rowLaw i) = 0 := by
  cases i with
  | inl p =>
    have hpos  := fun p => hpos (Sum.inl p)
    cases p
    · exact highPacketAbsoluteLaw_density_observable_zero (Measure.dirac ()) a b D 2 D q C
        (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _)
        (hpos .unit) H hH B hB
    · exact highPacketAbsoluteLaw_density_observable_zero (finePairTimeFieldMeasure d 0 ℓ)
        a b D 2 D q C _ (finePairTimeMatrix_measurable d _)
        (finePairTimeMatrix_cost_integrable d 0 ℓ _) (hpos .coarse) H hH B hB
    · exact finePairPacketAbsoluteLaw_density_observable_zero (finePairTimeFieldMeasure d ℓ N)
        a b M q C _ (finePairTimeMatrix_measurable d _)
        (finePairTimeMatrix_cost_integrable d ℓ N _) (hpos .fine) H hH B hB
  | inr i =>
    cases i with
    | inl _ =>
      exact highPacketAbsoluteLaw_density_observable_zero (Measure.dirac ()) a b D 1 D q C
        (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _)
        (hpos (.inr (.inl ()))) H hH B hB
    | inr i =>
      letI := higherBandCarrierMeasure_finite d (higherBandFamilyTarget i.val) ℓ (higherBandFamilyUpper d ℓ N μ i.val) i.property.1 i.val.2
      exact highPacketAbsoluteLaw_density_observable_zero _ a b (higherBandFamilyGuardDegree M i.val) (higherBandFamilyTarget i.val) D q C _
        (higherBandCarrierAmplitude_measurable d (higherBandFamilyTarget i.val) D lam i.val.2)
        (higherBandCarrierAmplitude_cost_integrable d (higherBandFamilyTarget i.val) D lam ℓ (higherBandFamilyUpper d ℓ N μ i.val) i.property.1 i.val.2)
        (hpos (.inr (.inr i))) H hH B hB
theorem sourceRowMass_positive_actual (d ) [NeZero d] (k D M q )
    (hD : 3 ≤ D) (hq : 1 ≤ q) (a b ) (ha : 0 < a) (hab : a < b)
    (C ) (hC : 0 < C) (lam ℓ N μ ) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
    (i ) :
    0 < (sourceRowData d k D M q a b C lam ℓ N μ).rowMass i := by
  cases i with
  | inl p => exact finePairRowMass_positive d D hD M q hq a b ha hab C hC ℓ N hℓ hℓN p
  | inr i =>
    cases i with
    | inl _ => exact singletonRowMass_positive d D q hq a b ha hab C hC
    | inr i => exact higherBandFamily_mass_positive d k D M q a b C lam ℓ N μ i
end NearlyMinimax
