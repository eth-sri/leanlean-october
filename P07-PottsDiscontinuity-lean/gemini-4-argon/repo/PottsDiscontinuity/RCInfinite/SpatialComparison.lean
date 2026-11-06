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
local instance edgeFintype {V : Type*} [Finite V] (G : SimpleGraph V) : Fintype G.edgeSet :=
  Fintype.ofFinite _
attribute [local instance] edgeDecidableEq

/-- The original lattice edges belonging to a finite induced box. -/
def boxEdges (c : LatticeVertex) (r : ℕ) : Set Edge := Set.range (boxEdgeEmbedding c r)

variable {c d : LatticeVertex} {r s : ℕ}

abbrev boxRestriction (hbox : latticeBox c r ⊆ latticeBox d s) :=
  embeddedConfigurationRestriction (boxGraph c r) (boxGraph d s)
    (boxVertexEmbedding hbox) (boxGraph_map_boxVertexEmbedding hbox)

abbrev boxRemovedEdges (hbox : latticeBox c r ⊆ latticeBox d s) :=
  subgraphRemovedEdges ((boxGraph c r).map (boxVertexEmbedding hbox)) (boxGraph d s)

def boxOutsideState (hbox : latticeBox c r ⊆ latticeBox d s)
    (C : Configuration (boxGraph d s)) : RemovedConfiguration (boxGraph d s) (boxRemovedEdges hbox) :=
  (configurationSplitEquiv (boxGraph d s) (boxRemovedEdges hbox) C).2

theorem boxEdgeEmbedding_compatible (hbox : latticeBox c r ⊆ latticeBox d s)
    (e : (boxGraph c r).edgeSet) :
    boxEdgeEmbedding d s (embeddedEdgeEmbedding (boxGraph c r) (boxGraph d s)
      (boxVertexEmbedding hbox) (boxGraph_map_boxVertexEmbedding hbox) e) =
        boxEdgeEmbedding c r e := by
  apply Subtype.ext
  change Sym2.map (fun v : BoxVertex d s => v.val) (Sym2.map (boxVertexEmbedding hbox) e.val) =
    Sym2.map (fun v : BoxVertex c r => v.val) e.val
  rw [Sym2.map_map]; rfl

theorem boxExtension_restriction_agrees (hbox : latticeBox c r ⊆ latticeBox d s)
    (i : Fin 2) (C : Configuration (boxGraph d s)) (e : Edge) (he : e ∈ boxEdges c r) :
    boxExtension i c r (boxRestriction hbox C) e = boxExtension i d s C e := by
  obtain ⟨f, rfl⟩ := he
  rw [boxExtension_at, ← boxEdgeEmbedding_compatible hbox f, boxExtension_at]
  exact decide_eq_decide.mpr (mem_embeddedConfigurationRestriction _ _ _ _ C f)

theorem outer_edge_mem_removed (hbox : latticeBox c r ⊆ latticeBox d s)
    (e : (boxGraph d s).edgeSet) (he : boxEdgeEmbedding d s e ∉ boxEdges c r) :
    e ∈ boxRemovedEdges hbox := by
  rw [mem_subgraphRemovedEdges]
  intro hmap
  let em : ((boxGraph c r).map (boxVertexEmbedding hbox)).edgeSet := ⟨e.val, hmap⟩
  let f := (isolatedExtensionEdgeEquiv (boxGraph c r) (boxVertexEmbedding hbox)).symm em
  have hf : embeddedEdgeEmbedding (boxGraph c r) (boxGraph d s)
      (boxVertexEmbedding hbox) (boxGraph_map_boxVertexEmbedding hbox) f = e :=
    Subtype.ext <| (embeddedEdgeEmbedding_coe _ _ _ _ f).trans <|
      congrArg Subtype.val ((isolatedExtensionEdgeEquiv (boxGraph c r) (boxVertexEmbedding hbox)).apply_symm_apply em)
  exact he ⟨f, by rw [← boxEdgeEmbedding_compatible hbox f, hf]⟩

theorem boxExtension_outside_agrees (hbox : latticeBox c r ⊆ latticeBox d s)
    (i : Fin 2) (C : Configuration (boxGraph d s)) (e : Edge) (he : e ∉ boxEdges c r) :
    boxExtension i d s C e = boxExtension i d s (boxOutsideState hbox C).val e := by
  by_cases heouter : e ∈ boxEdges d s
  · obtain ⟨f, rfl⟩ := heouter
    rw [boxExtension_at, boxExtension_at]
    exact Bool.eq_iff_iff.mpr <| by
      simp only [decide_eq_true_eq]
      exact ⟨fun h => Finset.mem_inter.mpr ⟨h, outer_edge_mem_removed hbox f he⟩,
        fun h => (Finset.mem_inter.mp h).1⟩
  · unfold boxExtension
    split_ifs
    · rw [boxConfiguration_outside d s _ e heouter, boxConfiguration_outside d s _ e heouter]
    · rw [wiredBoxConfiguration_outside d s _ e heouter, wiredBoxConfiguration_outside d s _ e heouter]

theorem box_inside_event (hbox : latticeBox c r ⊆ latticeBox d s) (i : Fin 2)
    {A : Set LatticeConfiguration} (hA : DependsOn (boxEdges c r) A) :
    (boxExtension i d s) ⁻¹' A =
      (boxRestriction hbox) ⁻¹' ((boxExtension i c r) ⁻¹' A) :=
  Set.ext fun C => (hA (boxExtension i c r (boxRestriction hbox C)) (boxExtension i d s C)
    (boxExtension_restriction_agrees hbox i C)).symm

theorem box_outside_event (hbox : latticeBox c r ⊆ latticeBox d s) (i : Fin 2)
    {B : Set LatticeConfiguration} (hB : DependsOn (boxEdges c r)ᶜ B) :
    (boxExtension i d s) ⁻¹' B =
      (boxOutsideState hbox) ⁻¹' {K | boxExtension i d s K.val ∈ B} :=
  Set.ext fun C => hB (boxExtension i d s C) (boxExtension i d s (boxOutsideState hbox C).val)
    (boxExtension_outside_agrees hbox i C)

theorem box_allOpen_upper (i : Fin 2) (F : Finset Edge)
    (hF : (F : Set Edge) ⊆ boxEdges c r) :
    IsUpperSet ((boxExtension i c r) ⁻¹' LatticeConfiguration.allOpen F) := by
  intro C D hCD hC e he
  obtain ⟨f, hf⟩ := hF he
  have hCf := hC e he
  rw [← hf, boxExtension_at, decide_eq_true_eq] at hCf ⊢
  exact hCD hCf

theorem boxInterior_neighbor_closed (hbox : latticeBox c r ⊆ latticeBox d s)
    {x : BoxVertex c r} (hx : x ∉ boxVertexBoundary c r)
    {y : BoxVertex d s} (hxy : (boxGraph d s).Adj (boxVertexEmbedding hbox x) y) :
    ∃ z : BoxVertex c r, boxVertexEmbedding hbox z = y ∧ (boxGraph c r).Adj x z :=
  ⟨⟨y.val, by_contra fun hn => hx ⟨x.property, y.val, hxy, hn⟩⟩, Subtype.ext rfl, hxy⟩

theorem boxInterior_avoids_outerBoundary (hbox : latticeBox c r ⊆ latticeBox d s)
    {x : BoxVertex c r} (hx : x ∉ boxVertexBoundary c r) :
    boxVertexEmbedding hbox x ∉
      (BoundaryCondition.wired (boxVertexBoundary d s)).boundary :=
  fun ⟨_, y, hxy, hy⟩ => hx ⟨x.property, y, hxy, fun hys => hy (hbox hys)⟩

theorem box_joint_le_of_partitions (θ : Parameters) (i : Fin 2)
    (hbox : latticeBox c r ⊆ latticeBox d s) (A B : Set LatticeConfiguration)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hin : DependsOn (boxEdges c r) A) (hout : DependsOn (boxEdges c r)ᶜ B)
    (hupper : IsUpperSet ((boxExtension i c r) ⁻¹' A))
    (hpart : ∀ K : RemovedConfiguration (boxGraph d s) (boxRemovedEdges hbox),
      (isolatedExtensionPullbackBoundary (boxVertexEmbedding hbox)
        (frozenBoundary (boxBoundary i d s) K.val)).partition ≤ (boxBoundary i c r).partition) :
    (boxMeasure θ i d s : Measure LatticeConfiguration).real (A ∩ B) ≤
      (boxMeasure θ i c r : Measure LatticeConfiguration).real A *
        (boxMeasure θ i d s : Measure LatticeConfiguration).real B := by
  simp only [Measure.real, boxMeasure_apply θ i d s (hA.inter hB), boxMeasure_apply θ i c r hA,
    boxMeasure_apply θ i d s hB, Set.preimage_inter,
    box_inside_event hbox i hin, box_outside_event hbox i hout]
  exact embedded_joint_le (boxGraph c r) (boxGraph d s) (boxVertexEmbedding hbox)
    (boxGraph_map_boxVertexEmbedding hbox) θ (boxBoundary i d s) (boxBoundary i c r)
    ((boxExtension i c r) ⁻¹' A) hupper hpart _

theorem box_joint_ge_of_partitions (θ : Parameters) (i : Fin 2)
    (hbox : latticeBox c r ⊆ latticeBox d s) (A B : Set LatticeConfiguration)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hin : DependsOn (boxEdges c r) A) (hout : DependsOn (boxEdges c r)ᶜ B)
    (hupper : IsUpperSet ((boxExtension i c r) ⁻¹' A))
    (hpart : ∀ K : RemovedConfiguration (boxGraph d s) (boxRemovedEdges hbox),
      (boxBoundary i c r).partition ≤ (isolatedExtensionPullbackBoundary
        (boxVertexEmbedding hbox) (frozenBoundary (boxBoundary i d s) K.val)).partition) :
    (boxMeasure θ i c r : Measure LatticeConfiguration).real A *
        (boxMeasure θ i d s : Measure LatticeConfiguration).real B ≤
      (boxMeasure θ i d s : Measure LatticeConfiguration).real (A ∩ B) := by
  simp only [Measure.real, boxMeasure_apply θ i d s (hA.inter hB), boxMeasure_apply θ i c r hA,
    boxMeasure_apply θ i d s hB, Set.preimage_inter,
    box_inside_event hbox i hin, box_outside_event hbox i hout]
  exact embedded_joint_ge (boxGraph c r) (boxGraph d s) (boxVertexEmbedding hbox)
    (boxGraph_map_boxVertexEmbedding hbox) θ (boxBoundary i d s) (boxBoundary i c r)
    ((boxExtension i c r) ⁻¹' A) hupper hpart _

theorem allOpen_dependsOn_box (F : Finset Edge) (hF : (F : Set Edge) ⊆ boxEdges c r) :
    DependsOn (boxEdges c r) (LatticeConfiguration.allOpen F) :=
  fun _ _ hω => ⟨fun h e he => hω e (hF he) ▸ h e he, fun h e he => (hω e (hF he)).symm ▸ h e he⟩

/-- Wired finite-volume comparison, with an arbitrary event of the exterior
edges retained in the joint probability. -/
theorem wired_box_joint_le (θ : Parameters) (hbox : latticeBox c r ⊆ latticeBox d s)
    (F : Finset Edge) (hF : (F : Set Edge) ⊆ boxEdges c r)
    (B : Set LatticeConfiguration) (hB : MeasurableSet B)
    (hout : DependsOn (boxEdges c r)ᶜ B) :
    (wiredBoxProbabilityMeasure θ d s : Measure LatticeConfiguration).real
        (LatticeConfiguration.allOpen F ∩ B) ≤
      (wiredBoxProbabilityMeasure θ c r : Measure LatticeConfiguration).real
        (LatticeConfiguration.allOpen F) *
        (wiredBoxProbabilityMeasure θ d s : Measure LatticeConfiguration).real B :=
  box_joint_le_of_partitions θ 1 hbox _ B
    (isCylinder_allOpen F).measurableSet hB (allOpen_dependsOn_box F hF) hout
    (box_allOpen_upper 1 F hF) fun K => by
      simpa [boxBoundary] using
        isolatedExtensionPullback_frozenBoundary_partition_le_wired_of_closedInterior
          (boxVertexEmbedding hbox) (boxGraph_map_boxVertexEmbedding hbox) (boxVertexBoundary c r)
          (fun _ hx _ hxy => boxInterior_neighbor_closed hbox hx hxy)
          (BoundaryCondition.wired (boxVertexBoundary d s))
          (fun _ hx => boxInterior_avoids_outerBoundary hbox hx) K

/-- The matching lower bound for free finite-volume laws. -/
theorem free_box_joint_ge (θ : Parameters) (hbox : latticeBox c r ⊆ latticeBox d s)
    (F : Finset Edge) (hF : (F : Set Edge) ⊆ boxEdges c r)
    (B : Set LatticeConfiguration) (hB : MeasurableSet B)
    (hout : DependsOn (boxEdges c r)ᶜ B) :
    (boxProbabilityMeasure θ c r : Measure LatticeConfiguration).real
        (LatticeConfiguration.allOpen F) *
        (boxProbabilityMeasure θ d s : Measure LatticeConfiguration).real B ≤
      (boxProbabilityMeasure θ d s : Measure LatticeConfiguration).real
        (LatticeConfiguration.allOpen F ∩ B) :=
  box_joint_ge_of_partitions θ 0 hbox _ B
    (isCylinder_allOpen F).measurableSet hB (allOpen_dependsOn_box F hF) hout
    (box_allOpen_upper 0 F hF) fun K x _ hxy =>
      (hxy : x = _) ▸ (isolatedExtensionPullbackBoundary (boxVertexEmbedding hbox)
        (frozenBoundary (boxBoundary 0 d s) K.val)).partition.iseqv.refl x

end
end PottsDiscontinuity.RCInfinite
