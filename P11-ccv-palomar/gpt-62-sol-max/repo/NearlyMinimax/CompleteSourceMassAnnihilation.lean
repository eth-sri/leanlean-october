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

abbrev SourceRowDensityMark (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) :=
  (sourceRowSpace d D M q a b C lam ℓ N μ i).DensityMark

def sourceRowDensityProj (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ) :
    SourceRowMark d D M q a b C lam ℓ N μ i → SourceRowDensityMark d D M q a b C lam ℓ N μ i :=
  (sourceRowSpace d D M q a b C lam ℓ N μ i).density

def sourceRowDensityLift (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (r : HighResponseMarkIndex (HighFrameIndex d D) q) (i : SourceRowIndex d D M q a b C lam ℓ N μ) :
    SourceRowDensityMark d D M q a b C lam ℓ N μ i → SourceRowMark d D M q a b C lam ℓ N μ i :=
  (sourceRowSpace d D M q a b C lam ℓ N μ i).withResponse r

theorem sourceRowDensityLift_measurable (d D M q : ℕ) (a b C lam ℓ N μ : ℝ)
    (r : HighResponseMarkIndex (HighFrameIndex d D) q) (i : SourceRowIndex d D M q a b C lam ℓ N μ) :
    Measurable (sourceRowDensityLift d D M q a b C lam ℓ N μ r i) :=
  (sourceRowSpace d D M q a b C lam ℓ N μ i).withResponse_measurable r

section
variable (d : ℕ) [NeZero d] (k D M q : ℕ)

theorem sourceRow_density_observable_zero
    (a b C lam ℓ N μ : ℝ)
    (hpos : ∀ i, 0 < (sourceRowData d k D M q a b C lam ℓ N μ).rowMass i)
    (i : SourceRowIndex d D M q a b C lam ℓ N μ)
    (H : SourceRowDensityMark d D M q a b C lam ℓ N μ i → ℝ) (hH : Measurable H)
    (B : ℝ) (hB : ∀ z, ‖H z‖ ≤ B) :
    (∫ e, (sourceRowData d k D M q a b C lam ℓ N μ).rowActivation i e *
      H (sourceRowDensityProj d D M q a b C lam ℓ N μ i e)
      ∂(sourceRowData d k D M q a b C lam ℓ N μ).rowLaw i) = 0 := by
  let P := sourceRowPacket d D M q a b C lam ℓ N μ i
  obtain ⟨hfin, hA⟩ := sourceRowPacket_valid d D M q a b C lam ℓ N μ i
  exact responsePacket_absolute_density_zero P.carrier P.weights q C P.amplitude hA (hpos i) H hH B hB


end

section ResetObservable
variable {d k D M q : ℕ} [NeZero d] [NeZero k] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (hD : 3 ≤ D) (hq : 1 ≤ q)
    (hM : highCenterResolutionThreshold C ≤ (M : ℝ))
    (Cfr lam ℓ N μ : ℝ) (hCfr : 1 ≤ Cfr) (hℓ : 0 < ℓ) (hℓN : ℓ < N)
    (j : HighWindowLabels d k) (h : HighCompleteSourceHistory C k D M q Cfr lam ℓ N μ)
include hD hq hM hCfr hℓ hℓN

local notation "R" => completeSourceRows C k D M q Cfr lam ℓ N μ
local notation "resetDensity" => highUnionSourceResetDensity C R j h
local notation "rowActivation" => highUnionActivation R (highCenterMix C)
local notation "rowMeasure" => highUnionLaw R (highCenterMix C)

local notation "ad" => C.densityLower + 1 / (M : ℝ)
local notation "bd" => C.densityUpper - 1 / (M : ℝ)

omit hD hq hM hCfr hℓ hℓN in
/-- A source reset density depends only on the row's density mark. -/
theorem completeSourceResetDensity_project
    (r : HighResponseMarkIndex (HighFrameIndex d D) q)
    (i : SourceRowIndex d D M q ad bd Cfr lam ℓ N μ)
    (e : SourceRowMark d D M q ad bd Cfr lam ℓ N μ i) (x : Covariate d) :
    resetDensity (Sum.inl ⟨i, e⟩) x =
      resetDensity (Sum.inl ⟨i, sourceRowDensityLift d D M q ad bd Cfr lam ℓ N μ r i
        (sourceRowDensityProj d D M q ad bd Cfr lam ℓ N μ i e)⟩) x := by
  rw [highUnionSourceResetDensity_inl, highUnionSourceResetDensity_inl]
  rcases i with (p | _ | i)
  · cases p <;> rfl
  · rfl
  · rfl

private theorem completeSource_reset_observable_zero (Φ : (Covariate d → ℝ) → ℝ)
    (hΦ : Measurable (fun e => Φ (resetDensity e)))
    (B : ℝ) (hB : ∀ e, ‖Φ (resetDensity e)‖ ≤ B) :
    (∫ e, rowActivation e * Φ (resetDensity e) ∂rowMeasure) = 0 := by
  obtain ⟨G, hpos⟩ := completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN
  let β₀ : HighFrameIndex d D := ⟨fun _ => 0,by simp⟩
  let r₀ : HighResponseMarkIndex (HighFrameIndex d D) q := ((β₀,β₀),(false,false),0)
  exact highUnionSource_reset_observable_zero C R G hpos
    (SourceRowDensityMark d D M q ad bd Cfr lam ℓ N μ)
    (sourceRowDensityProj d D M q ad bd Cfr lam ℓ N μ)
    (sourceRowDensityLift d D M q ad bd Cfr lam ℓ N μ r₀)
    (sourceRowDensityLift_measurable d D M q ad bd Cfr lam ℓ N μ r₀)
    (sourceRow_density_observable_zero d k D M q ad bd Cfr lam ℓ N μ hpos) j h
    (completeSourceResetDensity_project C Cfr lam ℓ N μ j h r₀) Φ hΦ B hB
/-- Appending a row annihilates the indicators of its total raw mass. -/
theorem completeSourceMass_append_indicator_zero (S : Set ℝ) (hS : MeasurableSet S) :
    (∫ e, S.indicator (fun _ : ℝ => (1 : ℝ))
      (highUnionSourceMass C R (historyMarkedAppend (highNeighbors d k)
        (highNeighbors_symm d k) j (h,e))) * rowActivation e ∂rowMeasure) = 0 := by
  letI := highUnionMark_standardBorel (E := SourceRowMark d D M q
    (C.densityLower + 1 / (M : ℝ)) (C.densityUpper - 1 / (M : ℝ)) Cfr lam ℓ N μ)
  let Φ (p : Covariate d → ℝ) := S.indicator (fun _ : ℝ => (1 : ℝ)) (∫ x, p x ∂cubeVolume d)
  have hΦ : Measurable (fun e => Φ (resetDensity e)) := (measurable_const.indicator hS).comp
    ((highUnionSourceMass_measurable C R (completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN).1).comp
      ((historyMarkedAppend_measurable _ _ j).comp (measurable_const.prodMk measurable_id)))
  simp_rw [mul_comm (S.indicator _ _) _]
  exact completeSource_reset_observable_zero C hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN j h Φ hΦ 1
    (fun e => (norm_indicator_le_norm_self (s := S) _ _).trans_eq (by simp))

set_option backward.isDefEq.respectTransparency true in
/-- Every finite product of the appended density also has zero signed mass. -/
theorem completeSourceDensity_product_zero (n : ℕ) (x : Fin n → Covariate d) :
    (∫ e, rowActivation e * ∏ i, resetDensity e (x i) ∂rowMeasure) = 0 := by
  have G := (completeSourceRows_guards C k D M q hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN).1
  obtain ⟨hF, hFb⟩ := highUnionSource_reset_product_facts C R G j h n x
  exact completeSource_reset_observable_zero C hD hq hM Cfr lam ℓ N μ hCfr hℓ hℓN j h
    (fun p => ∏ i, p (x i)) hF (C.densityUpper ^ n) hFb

end ResetObservable
end NearlyMinimax
