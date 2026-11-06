module

public import NearlyMinimax.HighHistoryDensityMean
public import NearlyMinimax.HistoryReferenceMeasure
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗍

/-! Actual centered-packet density and mass on canonical marked histories,
including joint design measurability and the infinite reference mean. -/
𝚸
𝚳
𝚨
𝚰
𝚩

𝗇 𝔄 A ⊕ B
𝗇 𝔇 Sum.inl '' Sum.inl ⁻¹' s
theorem packetSum_borelSpace [TopologicalSpace A] [TopologicalSpace B]
    [MeasurableSpace A] [MeasurableSpace B] [BorelSpace A] [BorelSpace B] : BorelSpace 𝔄 := by
  constructor
  apply le_antisymm
  · intro s hs
    have hsec := measurableSet_sum_iff.mp hs
    let := borel 𝔄
    let : BorelSpace 𝔄 := ⟨rfl⟩
    have hleft : MeasurableSet (𝔇 : Set 𝔄) :=
      Topology.IsClosedEmbedding.inl.measurableEmbedding.measurableSet_image' hsec.1
    have he : s = 𝔇 ∪ Sum.inr '' Sum.inr ⁻¹' s := by
      grind
    rw [he]
    exact hleft.union $ Topology.IsClosedEmbedding.inr.measurableEmbedding.measurableSet_image' hsec.2
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    exact measurableSet_sum_iff.mpr ⟨(hs.preimage continuous_inl).measurableSet,
      (hs.preimage continuous_inr).measurableSet⟩

section Canonical
𝗇 𝔅 𝙯
variable {Z : Type*} [MeasurableSpace Z] (d k F m r D q : ℕ) [NeZero k]
  [LinearOrder 𝔅]
  (dependent : 𝔅 → 𝔅 → Prop)

variable (σ : Measure Z) [IsFiniteMeasure σ] (a b C δ : ℝ)
  (A : Z → HighFrameIndex d F → 𝖲)
  (hA : 𝙚) (hcost : 𝙧)
  (hpos : 0 < 𝗎₁)
  (ha : 𝙆) (hab : 𝙭) (hr : 𝘗) (hδ0 : 𝚈) (hδ1 : δ < 1)
  (radius width : ℝ) (hR : 0 < radius) (ha1 : a + radius ≤ 1) (hb1 : 1 + radius ≤ b)
  (hW : 𝘅 ≤ width) (hδW : δ * width ≤ radius / 2)
  (B : 𝔅 → Z → Covariate d → 𝗢)
  (hmB : 𝘲)
  (hB : ∀ j ζ x l, |B j ζ x l| ≤ 1)
  (initial : HighRawState d k F) (hinit : 𝗅₂)

include hA hcost hpos ha hab hr hδ0 hδ1 hR ha1 hb1 hW hδW hB hinit
