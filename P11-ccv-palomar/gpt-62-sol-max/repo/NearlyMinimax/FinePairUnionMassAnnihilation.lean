module

public import NearlyMinimax.FinePairRowSource
public import NearlyMinimax.FinePairRows
public import NearlyMinimax.HighUnionSourceGeometry

@[expose] public section

/-! Genuine complete fine-pair union mass-indicator annihilation. The
response coordinates are summed out of the actual signed packets; no
invariant-law or conditional score equality is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable

/-- True complete-union action equals the sum of its actual uncentered
row actions, for any bounded measurable observable. -/
theorem highUnionSource_bounded_action {d k F : ℕ} {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, MeasurableSpace (E i)] (C : ModelConstants d)
    (R : HighUnionRowData d k F I E) {M Cfr : ℝ} (G : HighUnionSourceGuards C M Cfr R)
    (hpos : ∀ i, 0 < R.rowMass i)
    (Fobs : HighUnionMark E → ℝ) (hF : Measurable Fobs)
    (L : ℝ) (hL : ∀ e, ‖Fobs e‖ ≤ L) :
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
      (hF.comp (measurable_inl.comp (measurable_sigma_mk_actual i))).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun e => hL (Sum.inl ⟨i,e⟩))))

end NearlyMinimax
