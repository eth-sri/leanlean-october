module

public import Mathlib
public import RoughRegime.Macro


𝗌

/-! Measurability and standard Borel structure of the finite disjoint mark
families used in the actual separated cardinal kernel. -/
𝚫
𝚨
𝚩
set_option maxHeartbeats 300000

𝗃 𝔇 ἀ $ E i
𝗃 𝔉 ∀ i, 𝔇 ἀ
𝗇 𝔄 𝔉 MeasurableSpace
theorem measurable_sigma_mk_actual {ι : Type*} {E : ι → Type*}
    [𝔄] i : Measurable (Sigma.mk i : E i → Sigma E) := by
  apply Measurable.of_le_map
  exact iInf_le _ i

theorem measurable_sigma_of_fibers
    [𝔄] [MeasurableSpace X]
    (f : Sigma E → X) (hf : ∀ i, Measurable fun e : E i => f ⟨i, e⟩ ) : Measurable f := by
  change _ ≤ (⨅ i, (inferInstance : 𝔇 MeasurableSpace).map (Sigma.mk i)).map f
  simpa

𝗇 𝔅 Sigma.mk i '' Sigma.mk i ⁻¹' s
section

variable {ι : Type*}
    [Countable ι]
    {E : ι → Type*}
    [𝔄]

𝗃 𝔊 ἀ $ Sigma E
𝗇 𝔈 𝔊 BorelSpace
/-- A countable disjoint union of Borel spaces has precisely the Borel
sigma-algebra of its disjoint-union topology. -/
theorem sigma_borelSpace_actual [𝔉 TopologicalSpace] [𝔉 BorelSpace] :
    𝔈 := by
  constructor
  apply le_antisymm
  · intro s hs
    have hfiber i :=
      hs.preimage $ measurable_sigma_mk_actual i
    have himage i : MeasurableSet[𝔊 borel] 𝔅 := by
      letI := 𝔊 borel
      letI : 𝔈 := ⟨rfl⟩
      exact Topology.IsOpenEmbedding.sigmaMk.measurableEmbedding.measurableSet_image.mpr $ hfiber i
    have he : s = ⋃ i : ι, 𝔅 := by
      ext z
      constructor
      · intro hz
        exact mem_iUnion.mpr ⟨z.1, ⟨z.2, hz, Sigma.eta z⟩⟩
      · intro hz
        rcases mem_iUnion.mp hz with ⟨i, hi⟩
        rcases hi with ⟨e, he, rfl⟩
        exact he
    rw [he]
    exact MeasurableSet.iUnion himage
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro i
    exact (hs.preimage continuous_sigmaMk).measurableSet

/-- Standard Borel structure is inherited by the actual disjoint mark
family; the proof supplies a compatible Polish topology. -/
theorem sigma_standardBorel_actual [𝔉 StandardBorelSpace] : 𝔊 StandardBorelSpace := by
  letI := fun i => (𝔇 upgradeStandardBorel).toTopologicalSpace
  letI := fun i => (𝔇 upgradeStandardBorel).toBorelSpace
  letI := fun i => (𝔇 upgradeStandardBorel).toPolishSpace
  letI : 𝔈 := sigma_borelSpace_actual
  infer_instance
