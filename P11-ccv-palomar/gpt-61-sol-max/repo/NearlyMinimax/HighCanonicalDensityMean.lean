module

public import NearlyMinimax.HighHistoryDensityMean
public import NearlyMinimax.HistoryReferenceMean

@[expose] public section

/-! Actual centered-packet density and mass on canonical marked histories,
including joint design measurability and the infinite reference mean. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem packetSum_borelSpace {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [MeasurableSpace A] [MeasurableSpace B] [BorelSpace A] [BorelSpace B] : BorelSpace (A ⊕ B) := by
  constructor
  apply le_antisymm
  · intro s hs
    have hsec := measurableSet_sum_iff.mp hs
    let  := borel (A ⊕ B)
    let : BorelSpace (A ⊕ B) := ⟨rfl⟩
    have hleft : MeasurableSet (Sum.inl '' (Sum.inl ⁻¹' s) : Set (A ⊕ B)) :=
      Topology.IsClosedEmbedding.inl.measurableEmbedding.measurableSet_image' hsec.1
    have hright : MeasurableSet (Sum.inr '' (Sum.inr ⁻¹' s) : Set (A ⊕ B)) :=
      Topology.IsClosedEmbedding.inr.measurableEmbedding.measurableSet_image' hsec.2
    have he : s = Sum.inl '' (Sum.inl ⁻¹' s) ∪ Sum.inr '' (Sum.inr ⁻¹' s) := by
      ext x
      cases x <;> simp
    rw [he]
    exact hleft.union hright
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    exact measurableSet_sum_iff.mpr ⟨(hs.preimage continuous_inl).measurableSet,
      (hs.preimage continuous_inr).measurableSet⟩

section Canonical
variable {Z : Type*} [MeasurableSpace Z] (d k F m r D q : ℕ) [NeZero k]
  [LinearOrder (HighWindowLabels d k)]
  (dependent : HighWindowLabels d k → HighWindowLabels d k → Prop)

variable (σ : Measure Z) [IsFiniteMeasure σ] (a b C δ : ℝ)
  (A : Z → HighFrameIndex d F → HighFrameIndex d F → ℝ)
  (hA : ∀ i j, Measurable (fun ζ => A ζ i j)) (hcost : Integrable (separatedMatrixCost A) σ)
  (hpos : 0 < highPacketMarkMass σ a b m r D q C A)
  (ha : 0 < a) (hab : a < b) (hr : 1 ≤ r) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
  (radius width : ℝ) (hR : 0 < radius) (ha1 : a + radius ≤ 1) (hb1 : 1 + radius ≤ b)
  (hW : b - a ≤ width) (hδW : δ * width ≤ radius / 2)
  (B : HighWindowLabels d k → Z → Covariate d → Fin r → ℝ)
  (hmB : ∀ j l, Measurable (fun zx : Z × Covariate d => B j zx.1 zx.2 l))
  (hB : ∀ j ζ x l, |B j ζ x l| ≤ 1)
  (initial : HighRawState d k F) (hinit : ∀ x, initial.1 x = 1)

include hA hcost hpos ha hab hr hδ0 hδ1 hR ha1 hb1 hW hδW hB hinit

end Canonical
end NearlyMinimax
