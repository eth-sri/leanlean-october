module

public import PottsDiscontinuity.RCInfinite.FiniteConditioning
public import PottsDiscontinuity.RCInfinite.FiniteEnergy

@[expose] public section

open MeasureTheory Set

namespace PottsDiscontinuity.RCInfinite
open FK
noncomputable section
open scoped Classical
attribute [local instance] configurationMeasurableSpace

attribute [local instance] edgeDecidableEq

/-- The original lattice edges belonging to a finite induced box. -/
def boxEdges (c : LatticeVertex) (r : ℕ) : Set Edge := Set.range (boxEdgeEmbedding c r)

variable {c d : LatticeVertex} {r s : ℕ}

section
variable (hbox : latticeBox c r ⊆ latticeBox d s) (i : Fin 2) (C : Configuration (boxGraph d s))
    (e : Edge)
include hbox

abbrev boxRestriction :=
  embeddedConfigurationRestriction _ _
    (boxVertexEmbedding hbox) (boxGraph_map_boxVertexEmbedding hbox)

abbrev boxRemovedEdges :=
  subgraphRemovedEdges ((boxGraph c r).map (boxVertexEmbedding hbox)) (boxGraph d s)

include C in
def boxOutsideState : RemovedConfiguration (boxGraph d s) (boxRemovedEdges hbox) :=
  (configurationSplitEquiv _ _ C).2

theorem boxEdgeEmbedding_compatible
    (e : (boxGraph c r).edgeSet) :
    boxEdgeEmbedding d s (embeddedEdgeEmbedding (boxGraph c r) (boxGraph d s)
      (boxVertexEmbedding hbox) (boxGraph_map_boxVertexEmbedding hbox) e) =
        boxEdgeEmbedding c r e := by
  apply Subtype.ext
  change Sym2.map (fun v : BoxVertex d s => v.val)
      (Sym2.map (boxVertexEmbedding hbox) e.val) =
    _
  rw [Sym2.map_map]
  rfl

theorem boxExtension_restriction_agrees (he : e ∈ boxEdges c r) :
    boxExtension i c r (boxRestriction hbox C) e = boxExtension i d s C e := by
  obtain ⟨f, rfl⟩ := he
  rw [boxExtension_at, ← boxEdgeEmbedding_compatible hbox f, boxExtension_at]
  simp_all

theorem outer_edge_mem_removed
    (e : (boxGraph d s).edgeSet) (he : boxEdgeEmbedding d s e ∉ boxEdges c r) :
    e ∈ boxRemovedEdges hbox := by
  rw [mem_subgraphRemovedEdges]
  intro hmap
  let em : ((boxGraph c r).map (boxVertexEmbedding hbox)).edgeSet := ⟨e.val, hmap⟩
  let f := (isolatedExtensionEdgeEquiv _ _).symm em
  have hf : embeddedEdgeEmbedding _ _
      (boxVertexEmbedding hbox) (boxGraph_map_boxVertexEmbedding hbox) f = e := by
    apply Subtype.ext
    rw [embeddedEdgeEmbedding_coe]
    exact congrArg Subtype.val
      ((isolatedExtensionEdgeEquiv _ _).apply_symm_apply em)
  apply he
  refine ⟨f, ?_⟩
  rw [← boxEdgeEmbedding_compatible hbox f, hf]

theorem boxExtension_outside_agrees (he : e ∉ boxEdges c r) :
    boxExtension i d s C e = boxExtension i d s (boxOutsideState hbox C).val e := by
  by_cases heouter : e ∈ boxEdges d s
  · obtain ⟨f, rfl⟩ := heouter
    have hf := outer_edge_mem_removed hbox f he
    rw [boxExtension_at, boxExtension_at]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    change _ ↔ (f ∈ C ∩ boxRemovedEdges hbox)
    simp_all
  · unfold boxExtension
    split_ifs <;> simp [boxConfiguration_outside d s _ e heouter, wiredBoxConfiguration_outside d s _ e heouter]

theorem box_inside_event
    {A : Set LatticeConfiguration} (hA : DependsOn (boxEdges c r) A) :
    (boxExtension i d s) ⁻¹' A =
      (boxRestriction hbox) ⁻¹' ((boxExtension i c r) ⁻¹' A) := by
  ext C
  exact (hA _ _
    (fun e he => boxExtension_restriction_agrees hbox i C e he)).symm

theorem box_outside_event
    {B : Set LatticeConfiguration} (hB : DependsOn (boxEdges c r)ᶜ B) :
    (boxExtension i d s) ⁻¹' B =
      (boxOutsideState hbox) ⁻¹'
        {K | boxExtension i d s K.val ∈ B} := by
  ext C
  exact hB _ _
    (fun e he => boxExtension_outside_agrees hbox i C e he)

end

variable (θ : Parameters) (i : Fin 2) (hbox : latticeBox c r ⊆ latticeBox d s)
    (A B : Set LatticeConfiguration) (hA : MeasurableSet A) (F : Finset Edge)
    (hF : ↑F ⊆ boxEdges c r) (hB : MeasurableSet B) (hin : DependsOn (boxEdges c r) A)
    (hout : DependsOn (boxEdges c r)ᶜ B) (hupper : IsUpperSet ((boxExtension i c r) ⁻¹' A))
    (hpart : ∀ K : RemovedConfiguration (boxGraph d s) (boxRemovedEdges hbox),
      (boxBoundary i c r).partition ≤ (isolatedExtensionPullbackBoundary
      (boxVertexEmbedding hbox) (frozenBoundary (boxBoundary i d s) K.val)).partition)
    {x : BoxVertex c r} (hx : x ∉ boxVertexBoundary c r)

include hF in
theorem box_allOpen_upper :
    IsUpperSet ((boxExtension i c r) ⁻¹' LatticeConfiguration.allOpen F) := by
  intro C D hCD hC e he
  obtain ⟨f, hf⟩ := hF he
  have hCf := hC e he
  rw [← hf, boxExtension_at] at hCf ⊢
  simp only [decide_eq_true_eq] at hCf ⊢
  exact hCD hCf

include hx in
theorem boxInterior_neighbor_closed
    {y : BoxVertex d s} (hxy : (boxGraph d s).Adj (boxVertexEmbedding hbox x) y) :
    ∃ z, boxVertexEmbedding hbox z = y ∧ (boxGraph c r).Adj x z := ⟨⟨y.val, (by
    by_contra hn
    exact hx ⟨x.property, y.val, hxy, hn⟩)⟩, Subtype.ext rfl, hxy⟩

include hx in
theorem boxInterior_avoids_outerBoundary :
    boxVertexEmbedding hbox x ∉
      (BoundaryCondition.wired (boxVertexBoundary d s)).boundary := by
  rintro ⟨_, y, hxy, hy⟩
  exact hx ⟨x.property, y, hxy, fun hys => hy (hbox hys)⟩

include hA hB hin hout hupper in
theorem box_joint_le_of_partitions
    (hpart : ∀ K : RemovedConfiguration (boxGraph d s) (boxRemovedEdges hbox),
      (isolatedExtensionPullbackBoundary (boxVertexEmbedding hbox)
        (frozenBoundary (boxBoundary i d s) K.val)).partition ≤ (boxBoundary i c r).partition) :
    (boxMeasure θ i d s : Measure LatticeConfiguration).real (A ∩ B) ≤
      (boxMeasure θ i c r : Measure LatticeConfiguration).real A *
        (boxMeasure θ i d s : Measure LatticeConfiguration).real B := by
  simp only [Measure.real]
  rw [boxMeasure_apply θ i d s (hA.inter hB), boxMeasure_apply θ i c r hA,
    boxMeasure_apply θ i d s hB, Set.preimage_inter,
    box_inside_event hbox i hin, box_outside_event hbox i hout]
  solve_by_elim [embedded_joint_le]

include hA hB hin hout hupper hpart in
theorem box_joint_ge_of_partitions :
    (boxMeasure θ i c r : Measure LatticeConfiguration).real A *
        (boxMeasure θ i d s : Measure LatticeConfiguration).real B ≤
      (boxMeasure θ i d s : Measure LatticeConfiguration).real (A ∩ B) := by
  simp only [Measure.real]
  rw [boxMeasure_apply θ i d s (hA.inter hB), boxMeasure_apply θ i c r hA,
    boxMeasure_apply θ i d s hB, Set.preimage_inter,
    box_inside_event hbox i hin, box_outside_event hbox i hout]
  solve_by_elim [embedded_joint_ge]

include hF in
theorem allOpen_dependsOn_box :
    DependsOn (boxEdges c r) (LatticeConfiguration.allOpen F) := by
  intro ω η hω
  constructor <;> intro h e he
  · rw [← hω e (hF he)]; exact h e he
  · rw [hω e (hF he)]; exact h e he

include hbox hF in
/-- Wired finite-volume comparison, with an arbitrary event of the exterior
edges retained in the joint probability. -/
theorem wired_box_joint_le
    (B : Set LatticeConfiguration) (hB : MeasurableSet B)
    (hout : DependsOn (boxEdges c r)ᶜ B) :
    (wiredBoxProbabilityMeasure θ d s : Measure LatticeConfiguration).real
        (LatticeConfiguration.allOpen F ∩ B) ≤
      (wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration).real
        (LatticeConfiguration.allOpen F) *
        (wiredBoxProbabilityMeasure θ d s : Measure LatticeConfiguration).real B := by
  apply box_joint_le_of_partitions θ 1 hbox _ B
    (isCylinder_allOpen F).measurableSet hB (allOpen_dependsOn_box F hF) hout
    (box_allOpen_upper 1 F hF)
  intro K
  exact isolatedExtensionPullback_frozenBoundary_partition_le_wired_of_closedInterior (boxGraph_map_boxVertexEmbedding hbox)
      (fun _ hx _ hxy => boxInterior_neighbor_closed hbox hx hxy)
      (fun _ hx => boxInterior_avoids_outerBoundary hbox hx) K

include hbox hF in
/-- The matching lower bound for free finite-volume laws. -/
theorem free_box_joint_ge
    (B : Set LatticeConfiguration) (hB : MeasurableSet B)
    (hout : DependsOn (boxEdges c r)ᶜ B) :
    (boxProbabilityMeasure θ c r : Measure LatticeConfiguration).real
        (LatticeConfiguration.allOpen F) *
        (boxProbabilityMeasure θ d s : Measure LatticeConfiguration).real B ≤
      (boxProbabilityMeasure θ d s : Measure LatticeConfiguration).real
        (LatticeConfiguration.allOpen F ∩ B) := by
  apply box_joint_ge_of_partitions θ 0 hbox _ B
    (isCylinder_allOpen F).measurableSet hB (allOpen_dependsOn_box F hF) hout
    (box_allOpen_upper 0 F hF)
  intro K x y hxy
  have hxy' : x = y := hxy
  simp_all

end
end PottsDiscontinuity.RCInfinite
