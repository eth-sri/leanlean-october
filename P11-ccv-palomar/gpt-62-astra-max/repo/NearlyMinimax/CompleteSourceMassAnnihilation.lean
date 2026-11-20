module

public import NearlyMinimax.CompleteSourceRows
public import NearlyMinimax.HighUnionDensityCancellation


@[expose] public section

/-! Actual canonical mass cancellation for the entire source packet,
including the singleton, all three pair rows, and every selected higher
coarse/fine row. Primitive cancellation is proved from finite response
atoms on the true carrier spaces. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable

section
variable (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)

abbrev SourceRowDensityMark :
    SourceRowIndex d D M q a b C lam ℓ N μ → Type
  | .inl p => FinePairRowDensityMark d D M p
  | .inr (.inl _) => Unit × HighDensityMarkIndex D 1 D
  | .inr (.inr i) => HigherBandCarrier d (higherBandFamilyTarget i.val) i.val.2 ×
      HighDensityMarkIndex (higherBandFamilyGuardDegree M i.val) (higherBandFamilyTarget i.val) D

instance sourceRowDensityMark_measurable
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) :
    MeasurableSpace (SourceRowDensityMark d D M q a b C lam ℓ N μ i) := by
  cases i with
  | inl p => infer_instance
  | inr i => cases i <;> dsimp [SourceRowDensityMark] <;> infer_instance

def sourceRowDensityProj :
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) →
      SourceRowMark d D M q a b C lam ℓ N μ i → SourceRowDensityMark d D M q a b C lam ℓ N μ i
  | .inl p => finePairRowDensityProj d D M q p
  | .inr (.inl _) => fun e => (e.1,e.2.1)
  | .inr (.inr _) => fun e => (e.1,e.2.1)

end

def sourceRowDensityLift {d D : ℕ} (M : ℕ) {q : ℕ} (a b C lam ℓ N μ : ℝ)
    (r : HighResponseMarkIndex (HighFrameIndex d D) q) :
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) →
      SourceRowDensityMark d D M q a b C lam ℓ N μ i → SourceRowMark d D M q a b C lam ℓ N μ i
  | .inl p => finePairRowWithResponse d D M q p r
  | .inr (.inl _) => fun e => (e.1,(e.2,r))
  | .inr (.inr _) => fun e => (e.1,(e.2,r))

theorem sourceRowDensityLift_measurable {d D : ℕ} (M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (r : HighResponseMarkIndex (HighFrameIndex d D) q)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) :
    Measurable (sourceRowDensityLift M a b C lam ℓ N μ r i) := by
  cases i with
  | inl p => exact by cases p <;> exact measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
  | inr i => cases i <;> exact measurable_fst.prodMk (measurable_snd.prodMk measurable_const)

section
variable (d k D M q : ℕ) (a b C lam ℓ N μ : ℝ) (r : HighResponseMarkIndex (HighFrameIndex d D) q)
    (j : HighWindowLabels d k) (i : SourceRowIndex d D M q a b C lam ℓ N μ)
    (e : SourceRowMark d D M q a b C lam ℓ N μ i)

theorem sourceRow_density_projection_slope (x : Covariate d) :
    (sourceRowData d k D M q a b C lam ℓ N μ).rowSlope j i e x =
    (sourceRowData d k D M q a b C lam ℓ N μ).rowSlope j i
      (sourceRowDensityLift M a b C lam ℓ N μ r i
        (sourceRowDensityProj d D M q a b C lam ℓ N μ i e)) x := by
  cases i with
  | inl p => cases p <;> rfl
  | inr i => cases i <;> rfl

theorem sourceRow_density_projection_intercept :
    (sourceRowData d k D M q a b C lam ℓ N μ).rowIntercept i e =
    (sourceRowData d k D M q a b C lam ℓ N μ).rowIntercept i
      (sourceRowDensityLift M a b C lam ℓ N μ r i
        (sourceRowDensityProj d D M q a b C lam ℓ N μ i e)) := by
  cases i with
  | inl p => cases p <;> rfl
  | inr i => cases i <;> rfl

end

theorem sourceRow_density_observable_zero {d : ℕ} [NeZero d] {k D M q : ℕ}
    {a b C lam ℓ N μ : ℝ}
    (hpos : ∀ i, 0 < (sourceRowData d k D M q a b C lam ℓ N μ).rowMass i)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ)
    (H : SourceRowDensityMark d D M q a b C lam ℓ N μ i → ℝ) (hH : Measurable H)
    (B : ℝ) (hB : ∀ z, ‖H z‖ ≤ B) :
    let data := sourceRowData d k D M q a b C lam ℓ N μ
    (∫ e, (data).rowActivation i e *
      H (sourceRowDensityProj d D M q a b C lam ℓ N μ i e)
      ∂(data).rowLaw i) = 0 := by
  cases i with
  | inl p =>
    exact finePairRow_density_observable_zero D M q a b C ℓ N
      (fun p => hpos (Sum.inl p)) hH hB
  | inr i =>
    cases i with
    | inl _ =>
      exact highPacketAbsoluteLaw_density_observable_zero
        (A := (fun _ => finePairUnitMatrix d D)) (fun _ _ => measurable_const) (integrable_const _)
        (hpos (.inr (.inl ()))) hH hB
    | inr i =>
      exact higherBandRow_density_observable_zero i.property.1
        (hpos (.inr (.inr i))) hH hB

theorem sourceRowMass_positive_actual (d : ℕ) [NeZero d] (k D M q : ℕ)
    (hD : 3 ≤ D) (hq : 1 ≤ q) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (C : ℝ) (hC : 0 < C) (lam ℓ N μ : ℝ) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) :
    0 < (sourceRowData d k D M q a b C lam ℓ N μ).rowMass i := by
  cases i with
  | inl p => exact finePairRowMass_positive d hD M q hq ha hab hC hℓ hℓN p
  | inr i =>
    cases i with
    | inl _ => solve_by_elim [singletonRowMass_positive]
    | inr i => apply higherBandFamily_mass_positive

/-- Response-coordinate elimination on the actual calibrated family. -/
theorem completeSource_density_action_zero {d k D M q : ℕ}
    [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    {C : ModelConstants d} (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
    (j : HighWindowLabels d k)
    (h : HighCompleteSourceHistory C k D M q Cfr lam ℓ N μ)
    (T : (Covariate d → ℝ) → ℝ) (L : ℝ) :
    let R := completeSourceRows C k D M q Cfr lam ℓ N μ
    let Fobs := fun e => T (highUnionSourceDensity C R (historyMarkedAppend j (h,e)))
    Measurable Fobs → (∀ e, ‖Fobs e‖ ≤ L) →
      (∫ e, highUnionActivation R (highCenterMix C) e * Fobs e ∂highUnionLaw R (highCenterMix C)) = 0 := by
  let a := C.densityLower+1/(M : ℝ)
  let b := C.densityUpper-1/(M : ℝ)
  let R := completeSourceRows C k D M q Cfr lam ℓ N μ
  obtain ⟨ha,hab⟩ := high_source_interval_numeric hM
  have hCf : 0 < Cfr := by linarith
  have hpos := sourceRowMass_positive_actual d k D M q hD hq ha hab Cfr hCf lam ℓ N μ hℓ hℓN
  let β₀ : HighFrameIndex d D := ⟨fun _ => 0,by simp⟩
  let r₀ : HighResponseMarkIndex (HighFrameIndex d D) q := ((β₀,β₀),(false,false),0)
  exact highUnionSource_density_action_zero
    (completeSourceRows_guards k hD hq hM lam μ hCfr hℓ hℓN) hpos
    (sourceRowDensityLift_measurable M q a b Cfr lam ℓ N μ r₀)
    (sourceRow_density_projection_slope d k D M q a b Cfr lam ℓ N μ r₀)
    (sourceRow_density_projection_intercept d k D M q a b Cfr lam ℓ N μ r₀)
    (sourceRow_density_observable_zero hpos) j h T L

/-- Canonical append annihilation for mass indicators. -/
theorem completeSourceMass_append_indicator_zero {d k D M q : ℕ}
    [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    {C : ModelConstants d} (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
    (j : HighWindowLabels d k)
    (h : HighCompleteSourceHistory C k D M q Cfr lam ℓ N μ) (S : Set ℝ) (hS : MeasurableSet S) :
    let rows := completeSourceRows C k D M q Cfr lam ℓ N μ
    (∫ e, S.indicator (fun _ : ℝ => (1 : ℝ))
      (highUnionSourceMass C (rows)
        (historyMarkedAppend j (h,e))) *
      highUnionActivation (rows) (highCenterMix C) e
      ∂highUnionLaw (rows) (highCenterMix C)) = 0 := by
  intro rows
  let R := rows
  let G := completeSourceRows_guards k hD hq hM lam μ hCfr hℓ hℓN
  letI : StandardBorelSpace (HighUnionMark (SourceRowMark d D M q (C.densityLower+1/(M : ℝ))
    (C.densityUpper-1/(M : ℝ)) Cfr lam ℓ N μ)) := highUnionMark_standardBorel
  have hF : Measurable (fun e => S.indicator (fun _ : ℝ => (1 : ℝ))
      (highUnionSourceMass C R (historyMarkedAppend j (h,e)))) := (measurable_const.indicator (f := fun _ : ℝ => (1 : ℝ)) hS).comp
    ((highUnionSourceMass_measurable C R G).comp
      ((historyMarkedAppend_measurable j).comp (measurable_const.prodMk measurable_id)))
  simpa only [highUnionSourceMass, mul_comm] using completeSource_density_action_zero hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN j h
    (fun p => S.indicator (fun _ => 1) (∫ x, p x ∂cubeVolume d)) 1 hF
    (fun e => (norm_indicator_le_norm_self (s := S) (fun _ : ℝ => (1 : ℝ)) _).trans_eq (by simp))

end NearlyMinimax
