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

section
variable {ι : Type*}

section
variable {E : ι → Type*}
    [∀ i, MeasurableSpace (E i)]

theorem measurable_sigma_mk_actual (i : ι) : Measurable (Sigma.mk i : E i → Sigma E) := by
  apply Measurable.of_le_map
  exact iInf_le _ i

theorem measurable_sigma_of_fibers {X : Type*} [MeasurableSpace X]
    (f : Sigma E → X) (hf : ∀ i, Measurable (fun e : E i => f ⟨i, e⟩)) : Measurable f := by
  apply Measurable.of_le_map
  change _ ≤ (⨅ i, (inferInstance : MeasurableSpace (E i)).map (Sigma.mk i)).map f
  rw [MeasurableSpace.map_iInf]
  apply le_iInf
  assumption

end

section
variable [Countable ι] {E : ι → Type*}

/-- A countable disjoint union of Borel spaces has precisely the Borel
sigma-algebra of its disjoint-union topology. -/
theorem sigma_borelSpace_actual
    [∀ i, TopologicalSpace (E i)] [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)] :
    BorelSpace (Sigma E) := by
  constructor
  apply le_antisymm
  · intro s hs
    have hfiber (i : ι) :=
      hs.preimage (measurable_sigma_mk_actual i)
    have himage (i : ι) : MeasurableSet[borel (Sigma E)] (Sigma.mk i '' (Sigma.mk i ⁻¹' s)) := by
      letI : MeasurableSpace (Sigma E) := borel (Sigma E)
      letI : BorelSpace (Sigma E) := ⟨rfl⟩
      exact (Topology.IsOpenEmbedding.sigmaMk.measurableEmbedding.measurableSet_image).mpr (hfiber i)
    have he : s = ⋃ i : ι, Sigma.mk i '' (Sigma.mk i ⁻¹' s) := by
      ext z
      constructor
      · grind [mem_iUnion.mpr]
      · intro hz
        rcases mem_iUnion.mp hz with ⟨i, hi⟩
        rcases hi with ⟨e, he, rfl⟩
        assumption
    grind [MeasurableSet.iUnion]
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    change MeasurableSet[(⨅ i, (inferInstance : MeasurableSpace (E i)).map (Sigma.mk i))] s
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro i
    exact (hs.preimage continuous_sigmaMk).measurableSet

/-- Standard Borel structure is inherited by the actual disjoint mark
family; the proof supplies a compatible Polish topology. -/
theorem sigma_standardBorel_actual
    [∀ i, MeasurableSpace (E i)] [∀ i, StandardBorelSpace (E i)] : StandardBorelSpace (Sigma E) := by
  letI : ∀ i, TopologicalSpace (E i) := fun i => (upgradeStandardBorel (E i)).toTopologicalSpace
  letI : ∀ i, BorelSpace (E i) := fun i => (upgradeStandardBorel (E i)).toBorelSpace
  letI : ∀ i, PolishSpace (E i) := fun i => (upgradeStandardBorel (E i)).toPolishSpace
  letI : BorelSpace (Sigma E) := sigma_borelSpace_actual
  infer_instance

end

end

open scoped BigOperators in
/-- Integrability and integration over a finite mixture of pushforward measures. -/
theorem finite_map_mixture_moments {I X : Type*} [Fintype I] [MeasurableSpace X]
    {E : I → Type*} [∀ i, MeasurableSpace (E i)] (e : ∀ i, E i → X)
    (he : ∀ i, Measurable (e i)) (μ : ∀ i, Measure (E i))
    {f : X → ℝ} (hf : Measurable f) (hi : ∀ i, Integrable (f ∘ e i) (μ i)) :
    Integrable f (∑ i, (μ i).map (e i)) ∧
      (∫ x, f x ∂(∑ i, (μ i).map (e i))) = ∑ i, ∫ y, f (e i y) ∂μ i := by
  have h (i : I) := (integrable_map_measure hf.aestronglyMeasurable (he i).aemeasurable).2 (hi i)
  refine ⟨integrable_finsetSum_measure.mpr (fun i _ => h i), ?_⟩
  rw [integral_finsetSum_measure (fun i _ => h i)]
  exact Finset.sum_congr rfl (fun i _ => integral_map (he i).aemeasurable hf.aestronglyMeasurable)

end NearlyMinimax
