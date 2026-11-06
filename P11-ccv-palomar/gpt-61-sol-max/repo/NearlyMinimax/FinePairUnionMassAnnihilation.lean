module

public import NearlyMinimax.FinePairRowSource
public import NearlyMinimax.FinePairRowAnnihilation
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

abbrev FinePairRowDensityMark (d D M : ℕ) : FinePairRowTag → Type
  | .unit => Unit × HighDensityMarkIndex D 2 D
  | .coarse => (ℝ × FinePairFieldMark d) × HighDensityMarkIndex D 2 D
  | .fine => (ℝ × FinePairFieldMark d) × FinePairDensityIndex M

instance (d D M : ℕ) (i : FinePairRowTag) : MeasurableSpace (FinePairRowDensityMark d D M i) := by
  cases i <;> dsimp only [FinePairRowDensityMark] <;> infer_instance

section
variable (d D M q : ℕ) (i : FinePairRowTag)

def finePairRowDensityProj  :
    FinePairRowMark d D M q i → FinePairRowDensityMark d D M i := by
  cases i <;> exact fun e => (e.1,e.2.1)

def finePairRowWithResponse 
    (r : HighResponseMarkIndex (HighFrameIndex d D) q) :
    FinePairRowDensityMark d D M i → FinePairRowMark d D M q i := by
  cases i <;> exact fun e => (e.1,(e.2,r))

theorem finePairRowWithResponse_measurable 
    r :
    Measurable (finePairRowWithResponse d D M q i r) := by
  cases i <;> exact measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
end


theorem finePairRow_density_observable_zero d [NeZero d] D M q
    a b C T₀ N (hpos : ∀ i, 0 < finePairRowMass d D M q a b C T₀ N i)
    (i : FinePairRowTag) F (hF : Measurable F)
    L (hL : ∀ e, ‖F e‖ ≤ L) :
    (∫ e, finePairRowActivation d D M q a b C T₀ N i e *
      F (finePairRowDensityProj d D M q i e) ∂finePairRowLaw d D M q a b C T₀ N i) = 0 := by
  cases i
  · exact highPacketAbsoluteLaw_density_observable_zero (Measure.dirac ()) a b D 2 D q C
      (fun _ => finePairUnitMatrix d D) (fun _ _ => measurable_const) (integrable_const _)
      (hpos .unit) F hF L hL
  · exact highPacketAbsoluteLaw_density_observable_zero (finePairTimeFieldMeasure d 0 T₀)
      a b D 2 D q C _ (finePairTimeMatrix_measurable d _)
      (finePairTimeMatrix_cost_integrable d 0 T₀ _) (hpos .coarse) F hF L hL
  · exact finePairPacketAbsoluteLaw_density_observable_zero (finePairTimeFieldMeasure d T₀ N)
      a b M q C _ (finePairTimeMatrix_measurable d _)
      (finePairTimeMatrix_cost_integrable d T₀ N _) (hpos .fine) F hF L hL

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
      (hF.comp (measurable_inl.comp (rowSigmaMk_measurable i))).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun e => hL (Sum.inl ⟨i,e⟩))))

section
variable {d k D M q : ℕ} [NeZero k] [NeZero d] [LinearOrder (HighWindowLabels d k)]
    (C : ModelConstants d) (Cfr T₀ N : ℝ)

end
end NearlyMinimax
