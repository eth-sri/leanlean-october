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

variable (hbox : latticeBox c r ⊆ latticeBox d s)

abbrev boxRestriction :=
  embeddedConfigurationRestriction (boxGraph c r) (boxGraph d s)
    (boxVertexEmbedding hbox) (boxGraph_map_boxVertexEmbedding hbox)

abbrev boxRemovedEdges :=
  subgraphRemovedEdges ((boxGraph c r).map (boxVertexEmbedding hbox)) (boxGraph d s)

def boxOutsideState
    (C : Configuration (boxGraph d s)) : RemovedConfiguration (boxGraph d s) (boxRemovedEdges hbox) :=
  (configurationSplitEquiv (boxGraph d s) (boxRemovedEdges hbox) C).2

theorem boxEdgeEmbedding_compatible
    (e : (boxGraph c r).edgeSet) :
    boxEdgeEmbedding d s (embeddedEdgeEmbedding (boxGraph c r) (boxGraph d s)
      (boxVertexEmbedding hbox) (boxGraph_map_boxVertexEmbedding hbox) e) =
        boxEdgeEmbedding c r e := by
  apply Subtype.ext
  change Sym2.map (fun v : BoxVertex d s => v.val)
      (Sym2.map (boxVertexEmbedding hbox) e.val) =
    Sym2.map (fun v : BoxVertex c r => v.val) e.val
  rw [Sym2.map_map]
  rfl

theorem boxExtension_restriction_agrees
    (i : Fin 2) (C : Configuration (boxGraph d s)) (e : Edge) (he : e ∈ boxEdges c r) :
    boxExtension i c r (boxRestriction hbox C) e = boxExtension i d s C e := by
  obtain ⟨f, rfl⟩ := he
  rw [boxExtension_at, ← boxEdgeEmbedding_compatible hbox f, boxExtension_at]
  simp

theorem outer_edge_mem_removed
    (e : (boxGraph d s).edgeSet) (he : boxEdgeEmbedding d s e ∉ boxEdges c r) :
    e ∈ boxRemovedEdges hbox := by
  rw [mem_subgraphRemovedEdges]
  intro hmap
  let em : ((boxGraph c r).map (boxVertexEmbedding hbox)).edgeSet := ⟨e.val, hmap⟩
  let f := (isolatedExtensionEdgeEquiv (boxGraph c r) (boxVertexEmbedding hbox)).symm em
  have hf : embeddedEdgeEmbedding (boxGraph c r) (boxGraph d s)
      (boxVertexEmbedding hbox) (boxGraph_map_boxVertexEmbedding hbox) f = e := by
    apply Subtype.ext
    rw [embeddedEdgeEmbedding_coe]
    exact congrArg Subtype.val
      ((isolatedExtensionEdgeEquiv (boxGraph c r) (boxVertexEmbedding hbox)).apply_symm_apply em)
  apply he
  refine ⟨f, ?_⟩
  rw [← boxEdgeEmbedding_compatible hbox f, hf]

theorem boxExtension_outside_agrees
    (i : Fin 2) (C : Configuration (boxGraph d s)) (e : Edge) (he : e ∉ boxEdges c r) :
    boxExtension i d s C e = boxExtension i d s (boxOutsideState hbox C).val e := by
  by_cases heouter : e ∈ boxEdges d s
  · obtain ⟨f, rfl⟩ := heouter
    have hf := outer_edge_mem_removed hbox f he
    rw [boxExtension_at, boxExtension_at]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    change (f ∈ C) ↔ (f ∈ C ∩ boxRemovedEdges hbox)
    simp_all
  · unfold boxExtension
    split_ifs
    ·
      simp [boxConfiguration_outside d s _ e heouter]
    ·
      simp [wiredBoxConfiguration_outside d s _ e heouter]

theorem box_inside_event (i : Fin 2)
    {A : Set LatticeConfiguration} (hA : DependsOn (boxEdges c r) A) :
    (boxExtension i d s) ⁻¹' A =
      (boxRestriction hbox) ⁻¹' ((boxExtension i c r) ⁻¹' A) := by
  ext C
  exact (hA (boxExtension i c r (boxRestriction hbox C)) (boxExtension i d s C)
    (fun e he => boxExtension_restriction_agrees hbox i C e he)).symm

theorem box_outside_event (i : Fin 2)
    {B : Set LatticeConfiguration} (hB : DependsOn (boxEdges c r)ᶜ B) :
    (boxExtension i d s) ⁻¹' B =
      (boxOutsideState hbox) ⁻¹'
        {K | boxExtension i d s K.val ∈ B} := by
  ext C
  exact hB (boxExtension i d s C) (boxExtension i d s (boxOutsideState hbox C).val)
    (fun e he => boxExtension_outside_agrees hbox i C e he)

end

theorem box_allOpen_upper (i : Fin 2) (F : Finset Edge)
    (hF : (F : Set Edge) ⊆ boxEdges c r) :
    IsUpperSet ((boxExtension i c r) ⁻¹' LatticeConfiguration.allOpen F) := by
  intro C D hCD hC e he
  obtain ⟨f, hf⟩ := hF he
  have hCf := hC e he
  rw [← hf, boxExtension_at] at hCf ⊢
  simp only [decide_eq_true_eq] at hCf ⊢
  exact hCD hCf

theorem boxInterior_neighbor_closed (hbox : latticeBox c r ⊆ latticeBox d s)
    {x : BoxVertex c r} (hx : x ∉ boxVertexBoundary c r)
    {y : BoxVertex d s} (hxy : (boxGraph d s).Adj (boxVertexEmbedding hbox x) y) :
    ∃ z : BoxVertex c r, boxVertexEmbedding hbox z = y ∧ (boxGraph c r).Adj x z := by
  have hy : y.val ∈ latticeBox c r := by
    by_contra hn
    exact hx ⟨x.property, y.val, hxy, hn⟩
  exact ⟨⟨y.val, hy⟩, Subtype.ext rfl, hxy⟩

theorem boxInterior_avoids_outerBoundary (hbox : latticeBox c r ⊆ latticeBox d s)
    {x : BoxVertex c r} (hx : x ∉ boxVertexBoundary c r) :
    boxVertexEmbedding hbox x ∉
      (BoundaryCondition.wired (boxVertexBoundary d s)).boundary := by
  rintro ⟨_, y, hxy, hy⟩
  exact hx ⟨x.property, y, hxy, fun hys => hy (hbox hys)⟩

theorem allOpen_dependsOn_box (F : Finset Edge) (hF : (F : Set Edge) ⊆ boxEdges c r) :
    DependsOn (boxEdges c r) (LatticeConfiguration.allOpen F) := by
  intro ω η hω
  constructor <;> intro h e he
  · simpa [← hω e (hF he)] using h e he
  · simpa [hω e (hF he)] using h e he

/-- Free or wired joint comparison for an increasing event depending on the inner edges. -/
theorem box_event_joint_compare (θ : Parameters) (i : Fin 2)
    (hbox : latticeBox c r ⊆ latticeBox d s) (A B : Set LatticeConfiguration)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hin : DependsOn (boxEdges c r) A) (hout : DependsOn (boxEdges c r)ᶜ B)
    (hup : IsUpperSet (boxExtension i c r ⁻¹' A)) :
    comparisonSign i * (boxMeasure θ i d s : Measure LatticeConfiguration).real (A ∩ B) ≤
      comparisonSign i * (boxMeasure θ i c r : Measure LatticeConfiguration).real A *
        (boxMeasure θ i d s : Measure LatticeConfiguration).real B := by
  simp only [Measure.real]
  rw [boxMeasure_apply θ i d s (hA.inter hB), boxMeasure_apply θ i c r hA,
    boxMeasure_apply θ i d s hB, Set.preimage_inter, box_inside_event hbox i hin,
    box_outside_event hbox i hout]
  refine embedded_joint_compare _ _ _ (boxGraph_map_boxVertexEmbedding hbox) i θ
    (boxBoundary i d s) (boxBoundary i c r) _ hup _ ?_
  intro K
  fin_cases i
  · simp only [boxBoundary]
    intro x y hxy
    subst y <;> simp_all
  · simpa [boxBoundary] using
      isolatedExtensionPullback_frozenBoundary_partition_le_wired_of_closedInterior
        (boxVertexEmbedding hbox) (boxGraph_map_boxVertexEmbedding hbox) (boxVertexBoundary c r)
        (fun _ hx _ hxy => boxInterior_neighbor_closed hbox hx hxy)
        (BoundaryCondition.wired (boxVertexBoundary d s))
        (fun _ hx => boxInterior_avoids_outerBoundary hbox hx) K

theorem box_joint_compare (θ : Parameters) (i : Fin 2) (hbox : latticeBox c r ⊆ latticeBox d s)
    (F : Finset Edge) (hF : (F : Set Edge) ⊆ boxEdges c r)
    (B : Set LatticeConfiguration) (hB : MeasurableSet B)
    (hout : DependsOn (boxEdges c r)ᶜ B) :
    comparisonSign i * (boxMeasure θ i d s : Measure LatticeConfiguration).real
      (LatticeConfiguration.allOpen F ∩ B) ≤
      comparisonSign i * (boxMeasure θ i c r : Measure LatticeConfiguration).real
        (LatticeConfiguration.allOpen F) * (boxMeasure θ i d s : Measure LatticeConfiguration).real B :=
  box_event_joint_compare θ i hbox _ B (isCylinder_allOpen F).measurableSet hB
    (allOpen_dependsOn_box F hF) hout (box_allOpen_upper i F hF)

end
end PottsDiscontinuity.RCInfinite
