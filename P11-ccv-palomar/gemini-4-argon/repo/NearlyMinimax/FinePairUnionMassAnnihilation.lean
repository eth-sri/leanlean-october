module
public import NearlyMinimax.FinePairRowSource
public import NearlyMinimax.FinePairRowAnnihilation
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
section
variable {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, MeasurableSpace (E i)]
  (R : HighUnionRowData d k F I E)
variable [NeZero k] [LinearOrder (HighWindowLabels d k)] (C : ModelConstants d)
theorem highUnionSourceState_append (j h e) :
    highUnionSourceState C R (historyMarkedAppend
      (fun i j => j ∈ highNeighborLabels d k i)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,e)) =
    highUnionRawUpdate R (highCenterMix C) j e (highUnionSourceState C R h) :=
  have h_highUnionMarkedState_append (δ) : highUnionMarkedState R (fun i j => j ∈ highNeighborLabels d k i) δ highUnionVacuum
      (historyMarkedAppend (fun i j => j ∈ highNeighborLabels d k i)
        (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,e)) =
      highUnionRawUpdate R δ j e
        (highUnionMarkedState R (fun i j => j ∈ highNeighborLabels d k i) δ highUnionVacuum h) := highMarkedRawState_patch_append d k (highUnionSlope R)
    (fun _ e _ => highUnionIntercept R δ e) (fun _ => highUnionResponseReset R) highUnionVacuum j h e
  (h_highUnionMarkedState_append _)
theorem highUnionSourceDensity_append_of_not_mem (j h e x) (hx : x ∉ highTorusPatch d k j) :
    highUnionSourceDensity C R (historyMarkedAppend
      (fun i j => j ∈ highNeighborLabels d k i)
      (fun {_ _} h => highNeighborLabels_symmetric d k _ _ h) j (h,e)) x =
    highUnionSourceDensity C R h x := by
  change (highUnionSourceState C R _).1 x = _
  rw [highUnionSourceState_append R C j h e]
  have h_highUnionRawUpdate_density_of_not_mem (δ) (θ) : (highUnionRawUpdate R δ j e θ).1 x = θ.1 x := by
    simp only [highUnionRawUpdate, rawPatchUpdate, affinePatchUpdate, ite_eq_right hx]
  exact h_highUnionRawUpdate_density_of_not_mem _ _
end
abbrev FinePairRowDensityMark (d D M : ℕ) : FinePairRowTag → Type
  | .unit => Unit × HighDensityMarkIndex D 2 D
  | .coarse => (ℝ × FinePairFieldMark d) × HighDensityMarkIndex D 2 D
  | .fine => (ℝ × FinePairFieldMark d) × FinePairDensityIndex M
instance (d D M : ℕ) (i : FinePairRowTag) : MeasurableSpace (FinePairRowDensityMark d D M i) := by
  cases i <;> dsimp only [FinePairRowDensityMark] <;> infer_instance
def finePairRowDensityProj (d D M q i) :
    FinePairRowMark d D M q i → FinePairRowDensityMark d D M i := by
  cases i <;> exact fun e => (e.1,e.2.1)
def finePairRowWithResponse (d D M q i)
    (r : HighResponseMarkIndex (HighFrameIndex d D) q) :
    FinePairRowDensityMark d D M i → FinePairRowMark d D M q i := by
  cases i <;> exact fun e => (e.1,(e.2,r))
theorem finePairRowWithResponse_measurable (d D M q i r) :
    Measurable (finePairRowWithResponse d D M q i r) := by
  cases i <;> exact measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
theorem highUnionSource_bounded_action   [Fintype I] 
    [∀ i, MeasurableSpace (E i)] (C )
    (R : HighUnionRowData d k F I E) {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
    (hpos : ∀ i, 0 < R.rowMass i)
    (Fobs ) (hF : Measurable Fobs)
    (L ) (hL : ∀ e, ‖Fobs e‖ ≤ L) :
    (∫ e, highUnionActivation R (highCenterMix C) e * Fobs e
      ∂highUnionLaw R (highCenterMix C)) =
      ∑ i, ∫ e, R.rowActivation i e * Fobs (Sum.inl ⟨i,e⟩) ∂(R.rowLaw i) := by
  letI := G.row_probability
  have hi (i : I) : Integrable (R.rowActivation i) (R.rowLaw i) :=
    (integrable_const (R.rowMass i)).mono' (G.activation_measurable i).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun e => by
        simpa only [Real.norm_eq_abs] using G.activation_bound i e))
  have hUi := highRowUnionActivation_integrable R.rowLaw R.rowMass R.rowActivation
    G.activation_measurable hi
  have hUFi := hUi.mul_bdd (hF.comp measurable_inl).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun e => hL (Sum.inl e)))
  rw [highUnionActivation, highUnionLaw, highCenteredRowUnionActivation,
    highCenteredRowUnionLaw, balancedActivation_integral _ _ (highCenterMix_mem C).1
      (highCenterMix_mem C).2.le _
      (highRowUnionActivation_measurable _ _ G.activation_measurable) Fobs hF hUFi]
  exact highRowUnionActivation_action R.rowLaw R.rowMass hpos G.total_positive
    R.rowActivation G.activation_measurable (fun e => Fobs (Sum.inl e))
    (hF.comp measurable_inl) (fun i => (hi i).mul_bdd
      (hF.comp (measurable_inl.comp (rowSigmaMk_measurable i))).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun e => hL (Sum.inl ⟨i,e⟩))))
section
variable {d k D M q : ℕ} [NeZero k] [NeZero d] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (Cfr T₀ N : ℝ)
end
end NearlyMinimax
