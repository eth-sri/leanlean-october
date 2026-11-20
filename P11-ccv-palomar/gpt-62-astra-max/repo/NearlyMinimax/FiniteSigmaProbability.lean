module

public import Mathlib


@[expose] public section

/-! Measurability and standard Borel structure of the finite disjoint mark
families used in the actual separated cardinal kernel. -/
noncomputable section
open MeasureTheory Set
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

variable {ι : Type*} {E : ι → Type*} [∀ i, MeasurableSpace (E i)]

theorem measurable_sigma_mk_actual (i : ι) : Measurable (Sigma.mk i : E i → Sigma E) := by
  apply Measurable.of_le_map
  exact iInf_le _ i

theorem sigma_measurable_iff {X : Type*} [MeasurableSpace X] (f : Sigma E → X) :
    Measurable f ↔ ∀ i, Measurable (fun e => f ⟨i, e⟩) := by
  refine ⟨fun h i => h.comp (measurable_sigma_mk_actual i), ?_⟩
  intro h s hs
  exact MeasurableSpace.measurableSet_iInf.mpr (fun i => h i hs)

theorem sigma_uncurry_measurable {X : Type*} [MeasurableSpace X] {F : (i : ι) → E i → X}
    (h : ∀ i, Measurable (F i)) : Measurable (fun e : Sigma E => F e.1 e.2) := (sigma_measurable_iff _).2 h

/-- A countable disjoint union of Borel spaces has precisely the Borel
sigma-algebra of its disjoint-union topology. -/
theorem sigma_borelSpace_actual [Countable ι] {E : ι → Type*}
    [∀ i, TopologicalSpace (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)] :
    BorelSpace (Sigma E) := by
  constructor
  apply le_antisymm
  · intro s hs
    have hfiber (i : ι)  :=
      hs.preimage (measurable_sigma_mk_actual i)
    have himage (i : ι) : MeasurableSet[borel (Sigma E)] (Sigma.mk i '' (Sigma.mk i ⁻¹' s)) := by
      letI  := borel (Sigma E)
      letI : BorelSpace (Sigma E) := ⟨rfl⟩
      exact Topology.IsOpenEmbedding.sigmaMk.measurableEmbedding.measurableSet_image.mpr (hfiber i)
    have he : s = ⋃ i, Sigma.mk i '' (Sigma.mk i ⁻¹' s) := by
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
theorem sigma_standardBorel_actual [Countable ι] {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)] : StandardBorelSpace (Sigma E) := by
  letI  := fun i => (upgradeStandardBorel (E i)).toTopologicalSpace
  letI  := fun i => (upgradeStandardBorel (E i)).toBorelSpace
  letI  := fun i => (upgradeStandardBorel (E i)).toPolishSpace
  letI : BorelSpace (Sigma E) := sigma_borelSpace_actual
  infer_instance

end NearlyMinimax
