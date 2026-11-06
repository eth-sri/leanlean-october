module

public import PottsDiscontinuity.FK.Events
public import PottsDiscontinuity.TorusLoops.RectangleExplorationWeightedStep

/-!
# Root-set exploration events on the cut rectangle

This module records the finite exploration states used to iterate the
one-step estimate. The explored vertex set is the union of the actual open
clusters of the already selected left-boundary roots.
-/

@[expose] public noncomputable section

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus
open PottsDiscontinuity.FK

open scoped Classical

variable {N M : ℕ}

section
variable (hN : Even N) (hM : Even M)
/-- All listed roots cross to the right in distinct actual open clusters. -/
def rectangleDistinctRootCrossingEvent (roots : List (FaceVertex N M true)) :
    Set (Configuration (rectangleBaseGraph hN hM)) :=
  {A | (∀ x ∈ roots, A ∈ rectangleRootCrossingEvent hN hM x) ∧
    roots.Nodup ∧
    (∀ x ∈ roots, ∀ y ∈ roots, x ≠ y →
      ¬ ActualConnected (rectangleBaseGraph hN hM) A x y)}

/-- The union of the actual open clusters of a finite list of roots. -/
def rectangleRootClusterUnion (roots : List (FaceVertex N M true))
    (A : Configuration (rectangleBaseGraph hN hM)) : Set (FaceVertex N M true) :=
  {v | ∃ x ∈ roots, ActualConnected (rectangleBaseGraph hN hM) A x v}

/-- The exact finite vertex set in the open cluster of one root. -/
def rectangleRootClusterFinset (A : Configuration (rectangleBaseGraph hN hM)) (root : FaceVertex N M true) :
    Finset (FaceVertex N M true) :=
  Finset.univ.filter fun v => ActualConnected (rectangleBaseGraph hN hM) A root v

@[simp] theorem mem_rectangleRootClusterFinset (A : Configuration (rectangleBaseGraph hN hM)) (root v : FaceVertex N M true) :
    v ∈ rectangleRootClusterFinset hN hM A root ↔
      ActualConnected (rectangleBaseGraph hN hM) A root v := by
  simp [rectangleRootClusterFinset]

/-- The explored observation with root labels retained, so repeated roots are
still represented by the source tuple's set of labels. -/
def rectangleLabeledRootClusterObservation
    (roots : List (FaceVertex N M true))
    (A : Configuration (rectangleBaseGraph hN hM)) :
    Finset (FaceVertex N M true × Finset (FaceVertex N M true)) :=
  roots.toFinset.image fun root =>
    (root, rectangleRootClusterFinset hN hM A root)
end

/-- The vertex set represented by a root-labeled observation. -/
def rectangleLabeledObservationVertexSet
    (O : Finset (FaceVertex N M true × Finset (FaceVertex N M true))) :
    Set (FaceVertex N M true) :=
  {v | ∃ pair ∈ O, v ∈ pair.2}

section
variable (hN : Even N) (hM : Even M) (roots : List (FaceVertex N M true))
theorem rectangleLabeledObservationVertexSet_eq_rootClusterUnion
    (A : Configuration (rectangleBaseGraph hN hM)) :
    rectangleLabeledObservationVertexSet
      (rectangleLabeledRootClusterObservation hN hM roots A) =
      rectangleRootClusterUnion hN hM roots A := by
  simp [rectangleLabeledObservationVertexSet,
    rectangleLabeledRootClusterObservation, rectangleRootClusterFinset,
    rectangleRootClusterUnion]

theorem rectangleRootClusterFinset_eq_of_labeledObservation_eq
    (A B : Configuration (rectangleBaseGraph hN hM))
    (hobs : rectangleLabeledRootClusterObservation hN hM roots A =
      rectangleLabeledRootClusterObservation hN hM roots B)
    {root : FaceVertex N M true} (hroot : root ∈ roots) :
    rectangleRootClusterFinset hN hM A root =
      rectangleRootClusterFinset hN hM B root := by
  have hmemA : (root, rectangleRootClusterFinset hN hM A root) ∈
      rectangleLabeledRootClusterObservation hN hM roots A := by
    apply Finset.mem_image.mpr
    exact ⟨root, by simp_all, rfl⟩
  have hmemB : (root, rectangleRootClusterFinset hN hM A root) ∈
      rectangleLabeledRootClusterObservation hN hM roots B := by
    simp_all
  rcases Finset.mem_image.mp hmemB with ⟨other, hother, heq⟩
  grind

/-- The source distinct-root crossing event is determined by the exact
root-labeled cluster observation. -/
theorem rectangleDistinctRootCrossingEvent_labeledObservation_invariant
    (A B : Configuration (rectangleBaseGraph hN hM))
    (hobs : rectangleLabeledRootClusterObservation hN hM roots A =
      rectangleLabeledRootClusterObservation hN hM roots B) :
    (A ∈ rectangleDistinctRootCrossingEvent hN hM roots ↔
      B ∈ rectangleDistinctRootCrossingEvent hN hM roots) := by
  have hclusters : ∀ root, root ∈ roots →
      rectangleRootClusterFinset hN hM A root =
        rectangleRootClusterFinset hN hM B root := by
    grind [rectangleRootClusterFinset_eq_of_labeledObservation_eq]
  constructor
  · intro hA
    rcases hA with ⟨hcross, hnodup, hdistinct⟩
    refine ⟨?_, hnodup, ?_⟩
    · intro root hroot
      rcases hcross root hroot with ⟨v, hv, hconn⟩
      have hmem :=
        (mem_rectangleRootClusterFinset hN hM A root v).2 hconn
      rw [hclusters root hroot] at hmem
      exact ⟨v, hv, (mem_rectangleRootClusterFinset hN hM B root v).1 hmem⟩
    · intro x hx y hy hxy hconnB
      have hmemB :=
        (mem_rectangleRootClusterFinset hN hM B x y).2 hconnB
      grind [mem_rectangleRootClusterFinset]
  · intro hB
    rcases hB with ⟨hcross, hnodup, hdistinct⟩
    refine ⟨?_, hnodup, ?_⟩
    · intro root hroot
      rcases hcross root hroot with ⟨v, hv, hconn⟩
      have hmem :=
        (mem_rectangleRootClusterFinset hN hM B root v).2 hconn
      rw [← hclusters root hroot] at hmem
      exact ⟨v, hv, (mem_rectangleRootClusterFinset hN hM A root v).1 hmem⟩
    · intro x hx y hy hxy hconnA
      have hmemA :=
        (mem_rectangleRootClusterFinset hN hM A x y).2 hconnA
      grind [mem_rectangleRootClusterFinset]

/-- Finite set of actually occurring root-cluster observations. Restricting the
index to the range makes every fiber nonempty. -/
def rectangleRootObservationIndex  :=
  {O : Finset (FaceVertex N M true × Finset (FaceVertex N M true)) //
    O ∈ Set.range (rectangleLabeledRootClusterObservation hN hM roots)}

/-- The observation index of one rectangle configuration. -/
def rectangleRootObservationIndexOf
    (A : Configuration (rectangleBaseGraph hN hM)) :
    rectangleRootObservationIndex hN hM roots :=
  ⟨rectangleLabeledRootClusterObservation hN hM roots A,
    Set.mem_range_self A⟩

/-- The observation indices on which the listed roots cross distinctly. -/
def rectangleGoodRootObservation  :
    Set (rectangleRootObservationIndex hN hM roots) :=
  {b | ∃ A, rectangleRootObservationIndexOf hN hM roots A = b ∧
    A ∈ rectangleDistinctRootCrossingEvent hN hM roots}

/-- Frozen states consistent with an observation: they keep each old root's
recorded cluster and every open edge lies inside the explored vertex set. -/
def rectangleObservationRemovedStateEvent
    (O : Finset (FaceVertex N M true × Finset (FaceVertex N M true))) :
    Set (RemovedConfiguration (rectangleBaseGraph hN hM)
      (rectangleComplementRemovedEdges hN hM
        (rectangleLabeledObservationVertexSet O))) :=
  {K | (∀ root ∈ roots,
      (root, rectangleRootClusterFinset hN hM K.val root) ∈ O) ∧
    ∀ ⦃x y : FaceVertex N M true⦄,
      (openGraph (rectangleBaseGraph hN hM) K.val).Adj x y →
        x ∈ rectangleLabeledObservationVertexSet O ∧
        y ∈ rectangleLabeledObservationVertexSet O}

theorem rectangleDistinctRootCrossingEvent_iff_good_observation
    (A : Configuration (rectangleBaseGraph hN hM)) :
    A ∈ rectangleDistinctRootCrossingEvent hN hM roots ↔
      rectangleRootObservationIndexOf hN hM roots A ∈
        rectangleGoodRootObservation hN hM roots := by
  constructor
  · tauto
  · rintro ⟨B, hB, hgood⟩
    apply (rectangleDistinctRootCrossingEvent_labeledObservation_invariant
      hN hM roots B A (congrArg Subtype.val hB)).mp hgood
end

section
variable (hN : Even N) (hM : Even M)
theorem rectangleRootObservationIndex_fiber_has_law_support
    (q : Set.Ici (1 : ℝ))
    (roots : List (FaceVertex N M true))
    (b : rectangleRootObservationIndex hN hM roots) :
    ∃ A ∈ {A | rectangleRootObservationIndexOf hN hM roots A = b},
      A ∈ (law (rectangleBaseGraph hN hM) (rectangleFKParameters q)
        (BoundaryCondition.free ∅)).support := by
  rcases b.property with ⟨A, hA⟩
  refine ⟨A, ?_, ?_⟩
  · apply Subtype.ext
    tauto
  · rw [law_support]
    simp

/-- The root-cluster union is closed under open rectangle adjacency. -/
theorem rectangleRootClusterUnion_open_adj (roots : List (FaceVertex N M true))
    (A : Configuration (rectangleBaseGraph hN hM))
    {x y : FaceVertex N M true}
    (hxy : (openGraph (rectangleBaseGraph hN hM) A).Adj x y)
    (hx : x ∈ rectangleRootClusterUnion hN hM roots A) :
    y ∈ rectangleRootClusterUnion hN hM roots A := by
  rcases hx with ⟨r, hr, hreach⟩
  exact ⟨r, hr, hreach.trans hxy.reachable⟩

theorem rectangleRemovedEdge_of_endpoint_mem
    (U : Set (FaceVertex N M true))
    {x y : FaceVertex N M true}
    (hxy : (rectangleBaseGraph hN hM).Adj x y) (hx : x ∈ U) :
    (⟨s(x, y), (rectangleBaseGraph hN hM).mem_edgeSet.mpr hxy⟩ :
      (rectangleBaseGraph hN hM).edgeSet) ∈ rectangleComplementRemovedEdges hN hM U := by
  rw [rectangleComplementRemovedEdges, mem_subgraphRemovedEdges]
  intro he
  obtain ⟨a, b, hab, hax, hby⟩ :=
    (SimpleGraph.map_adj (rectangleComplementEmbedding U)
      (rectangleComplementGraph hN hM U) x y).mp (by tauto)
  have hax' : a.val = x := by tauto
  grind

theorem rectangleRemovedEdge_touches_U
    (U : Set (FaceVertex N M true))
    {e : (rectangleBaseGraph hN hM).edgeSet}
    (he : e ∈ rectangleComplementRemovedEdges hN hM U)
    (a b : FaceVertex N M true) (heq : e.val = s(a, b)) :
    a ∈ U ∨ b ∈ U := by
  by_contra hn
  have haU : a ∉ U := by
    simp_all
  have hbU : b ∉ U := by
    simp_all
  have hbase : (rectangleBaseGraph hN hM).Adj a b := by
    aesop
  have hIAdj : (rectangleComplementGraph hN hM U).Adj
      ⟨a, haU⟩ ⟨b, hbU⟩ := by
    tauto
  have hmapAdj : ((rectangleComplementGraph hN hM U).map
      (rectangleComplementEmbedding U)).Adj a b := by
    apply (SimpleGraph.map_adj (rectangleComplementEmbedding U)
      (rectangleComplementGraph hN hM U) a b).mpr
    exact ⟨⟨a, haU⟩, ⟨b, hbU⟩, hIAdj, rfl, rfl⟩
  simp_all [rectangleComplementGraph, rectangleComplementEmbedding, rectangleComplementRemovedEdges]

theorem rectangleRemovedState_open_adj_of_mem
    (U : Set (FaceVertex N M true))
    (A : Configuration (rectangleBaseGraph hN hM))
    {x y : FaceVertex N M true} (hx : x ∈ U)
    (hxy : (openGraph (rectangleBaseGraph hN hM) A).Adj x y) :
    (openGraph (rectangleBaseGraph hN hM)
      (rectangleComplementRemovedState hN hM U A).val).Adj x y := by
  have hbase :=
    openGraph_le (rectangleBaseGraph hN hM) A hxy
  have hopen :=
    (openGraph_adj (rectangleBaseGraph hN hM) A x y).mp hxy
  rcases hopen with ⟨e, heA, hexy⟩
  have heR : e ∈ rectangleComplementRemovedEdges hN hM U := by
    have heEq : e = ⟨s(x, y), (rectangleBaseGraph hN hM).mem_edgeSet.mpr hbase⟩ :=
      Subtype.ext hexy
    simp_all [rectangleRemovedEdge_of_endpoint_mem]
  have heK : e ∈ (rectangleComplementRemovedState hN hM U A).val := by
    have hs : e ∈ (rectangleComplementRemovedState hN hM U A).val ↔
        e ∈ A ∧ e ∈ rectangleComplementRemovedEdges hN hM U := by
      simp [rectangleComplementRemovedState, configurationSplitEquiv]
    simp_all
  have hKopen : s(x, y) ∈ openEdges (rectangleBaseGraph hN hM)
      (rectangleComplementRemovedState hN hM U A).val := by
    tauto
  exact (openGraph_adj (rectangleBaseGraph hN hM)
    (rectangleComplementRemovedState hN hM U A).val x y).mpr hKopen

/-- Every open edge in the exact state associated with an observation stays
inside that observation's union of old root clusters. -/
theorem rectangleRemovedState_open_edges_inside_of_observation
    (roots : List (FaceVertex N M true))
    (A : Configuration (rectangleBaseGraph hN hM))
    {x y : FaceVertex N M true}
    (hxy : (openGraph (rectangleBaseGraph hN hM)
      (rectangleComplementRemovedState hN hM
        (rectangleLabeledObservationVertexSet
          (rectangleLabeledRootClusterObservation hN hM roots A)) A).val).Adj x y) :
    x ∈ rectangleLabeledObservationVertexSet
        (rectangleLabeledRootClusterObservation hN hM roots A) ∧
    y ∈ rectangleLabeledObservationVertexSet
        (rectangleLabeledRootClusterObservation hN hM roots A) := by
  let U := rectangleLabeledObservationVertexSet
    (rectangleLabeledRootClusterObservation hN hM roots A)
  let K := rectangleComplementRemovedState hN hM U A
  let G := rectangleBaseGraph hN hM
  have hKsub : K.val ⊆ A := by
    intro e he
    have hs : e ∈ K.val ↔ e ∈ A ∧ e ∈ rectangleComplementRemovedEdges hN hM U := by
      simp [K, rectangleComplementRemovedState, configurationSplitEquiv]
    simp_all
  have hopenK := (openGraph_adj G K.val x y).mp hxy
  rcases hopenK with ⟨e, heK, hexy⟩
  have hopenA : s(x, y) ∈ Subtype.val '' (↑A : Set G.edgeSet) :=
    ⟨e, hKsub heK, hexy⟩
  have hxyA : (openGraph G A).Adj x y := by
    apply (openGraph_adj G A x y).mpr
    tauto
  have hUeq :=
    rectangleLabeledObservationVertexSet_eq_rootClusterUnion hN hM roots A
  rcases (rectangleRemovedEdge_touches_U hN hM U (K.property heK) x y hexy) with hx | hy
  · have hyUnion := rectangleRootClusterUnion_open_adj hN hM roots A hxyA (hUeq ▸ hx)
    grind
  · have hxUnion := rectangleRootClusterUnion_open_adj hN hM roots A hxyA.symm (hUeq ▸ hy)
    grind

/-- Under the explicit condition that the removed state has no open edge
leaving `U`, the exact removed-state configuration and the full configuration
have identical root clusters for roots in `U`. -/
theorem rectangleRemovedState_clusterFinset_eq_of_open_edges_inside
    (U : Set (FaceVertex N M true))
    (A : Configuration (rectangleBaseGraph hN hM)) (root : FaceVertex N M true)
    (hroot : root ∈ U)
    (hclosed : ∀ ⦃x y : FaceVertex N M true⦄,
      (openGraph (rectangleBaseGraph hN hM)
        (rectangleComplementRemovedState hN hM U A).val).Adj x y → x ∈ U ∧ y ∈ U) :
    rectangleRootClusterFinset hN hM
        (rectangleComplementRemovedState hN hM U A).val root =
      rectangleRootClusterFinset hN hM A root := by
  let K := (rectangleComplementRemovedState hN hM U A).val
  have hKsub : K ⊆ A := by
    intro e he
    have hs : e ∈ (rectangleComplementRemovedState hN hM U A).val ↔
        e ∈ A ∧ e ∈ rectangleComplementRemovedEdges hN hM U := by
      simp [rectangleComplementRemovedState, configurationSplitEquiv]
    grind
  have htransfer : ∀ {x y : FaceVertex N M true},
      (openGraph (rectangleBaseGraph hN hM) A).Reachable x y → x ∈ U →
      (openGraph (rectangleBaseGraph hN hM) K).Reachable x y ∧ y ∈ U := by
    intro x y hxy hx
    rcases hxy with ⟨w⟩
    induction w with
    | nil => tauto
    | @cons x y z hxy w ih =>
        have hxyK := rectangleRemovedState_open_adj_of_mem hN hM U A hx hxy
        have htail := ih ((hclosed hxyK).2)
        exact ⟨hxyK.reachable.trans htail.1, htail.2⟩
  apply Finset.ext
  intro v
  simp
  constructor
  · intro hreach
    exact actualConnected_mono hKsub hreach
  · intro hreach
    exact (htransfer hreach hroot).1

/-- A configuration's exact removed-edge state is consistent with its
root-labeled cluster observation. -/
theorem rectangleRemovedState_mem_observationRemovedStateEvent
    (roots : List (FaceVertex N M true))
    (A : Configuration (rectangleBaseGraph hN hM)) :
    rectangleComplementRemovedState hN hM
      (rectangleLabeledObservationVertexSet
        (rectangleLabeledRootClusterObservation hN hM roots A)) A ∈
      rectangleObservationRemovedStateEvent hN hM roots
        (rectangleLabeledRootClusterObservation hN hM roots A) := by
  let O := rectangleLabeledRootClusterObservation hN hM roots A
  let U := rectangleLabeledObservationVertexSet O
  have hclosed : ∀ ⦃x y : FaceVertex N M true⦄,
      (openGraph (rectangleBaseGraph hN hM)
        (rectangleComplementRemovedState hN hM U A).val).Adj x y →
        x ∈ U ∧ y ∈ U := by
    grind [rectangleRemovedState_open_edges_inside_of_observation]
  have hUeq : U = rectangleRootClusterUnion hN hM roots A := by
    grind [rectangleLabeledObservationVertexSet_eq_rootClusterUnion]
  refine ⟨?_, hclosed⟩
  intro root hroot
  have hrootU : root ∈ U :=
    hUeq.symm ▸ ⟨root, hroot, SimpleGraph.Reachable.rfl⟩
  have hclusterEq := rectangleRemovedState_clusterFinset_eq_of_open_edges_inside
    hN hM U A root hrootU hclosed
  rw [hclusterEq]
  apply Finset.mem_image.mpr
  exact ⟨root, by simpa using hroot, rfl⟩

theorem rectangleComplementOpenAdj_of_openAdj
    (U : Set (FaceVertex N M true))
    (A : Configuration (rectangleBaseGraph hN hM))
    {x y : FaceVertex N M true} (hx : x ∉ U) (hy : y ∉ U)
    (hxy : (openGraph (rectangleBaseGraph hN hM) A).Adj x y) :
    (openGraph (rectangleComplementGraph hN hM U)
      (embeddedConfigurationRestriction (rectangleComplementGraph hN hM U)
        (rectangleBaseGraph hN hM) (rectangleComplementEmbedding U)
        (rectangleComplementGraph_map_le hN hM U) A)).Adj
      ⟨x, hx⟩ ⟨y, hy⟩ := by
  let G := rectangleBaseGraph hN hM
  let I := rectangleComplementGraph hN hM U
  let f := rectangleComplementEmbedding U
  let hIG := rectangleComplementGraph_map_le hN hM U
  let C := embeddedConfigurationRestriction I G f hIG A
  have hbase := openGraph_le G A hxy
  have hI : I.Adj ⟨x, hx⟩ ⟨y, hy⟩ := by
    tauto
  let eI : I.edgeSet := ⟨s(⟨x, hx⟩, ⟨y, hy⟩), I.mem_edgeSet.mpr hI⟩
  have hopenG := (openGraph_adj G A x y).mp hxy
  change s(x, y) ∈ Subtype.val '' (↑A : Set G.edgeSet) at hopenG
  have heC : eI ∈ C := by
    aesop
  apply (openGraph_adj I C ⟨x, hx⟩ ⟨y, hy⟩).mpr
  tauto

theorem rectangleComplementActualConnected_of_component_disjoint
    (U : Set (FaceVertex N M true))
    (A : Configuration (rectangleBaseGraph hN hM)) (root v : FaceVertex N M true)
    (hdisjoint : ∀ z, ActualConnected (rectangleBaseGraph hN hM) A root z → z ∉ U)
    (hreach : ActualConnected (rectangleBaseGraph hN hM) A root v) :
    ActualConnected (rectangleComplementGraph hN hM U)
      (embeddedConfigurationRestriction (rectangleComplementGraph hN hM U)
        (rectangleBaseGraph hN hM) (rectangleComplementEmbedding U)
        (rectangleComplementGraph_map_le hN hM U) A)
      ⟨root, hdisjoint root SimpleGraph.Reachable.rfl⟩
      ⟨v, hdisjoint v hreach⟩ := by
  let G := rectangleBaseGraph hN hM
  let I := rectangleComplementGraph hN hM U
  let f := rectangleComplementEmbedding U
  let hIG := rectangleComplementGraph_map_le hN hM U
  let C := embeddedConfigurationRestriction I G f hIG A
  have hwalk : ∀ {x y : FaceVertex N M true}
      (w : (openGraph G A).Walk x y)
      (hroot : ActualConnected G A root x),
      ActualConnected I C ⟨x, hdisjoint x hroot⟩
        ⟨y, hdisjoint y (hroot.trans w.reachable)⟩ := by
    intro x y w hroot
    induction w with
    | nil =>
        tauto
    | @cons x y z hxy w ih =>
        have hrootY := hroot.trans hxy.reachable
        have hxyI := rectangleComplementOpenAdj_of_openAdj hN hM U A
          (hdisjoint x hroot) (hdisjoint y hrootY) hxy
        exact hxyI.reachable.trans (ih hrootY)
  rcases hreach with ⟨w⟩
  tauto

/-- If the new root's cluster is distinct from every old root cluster, its
left-to-right crossing is already visible in the induced complement. -/
theorem rectangleRootCrossing_complement_of_distinct_roots
    (roots : List (FaceVertex N M true))
    (A : Configuration (rectangleBaseGraph hN hM)) (u : FaceVertex N M true)
    (hseparate : ∀ x ∈ roots,
      ¬ ActualConnected (rectangleBaseGraph hN hM) A x u)
    (hcross : A ∈ rectangleRootCrossingEvent hN hM u) :
    rectangleComplementRootCrossingEvent hN hM
      (rectangleRootClusterUnion hN hM roots A) u
      (by
        intro hu
        rcases hu with ⟨x, hx, hxu⟩
        grind)
      (embeddedConfigurationRestriction (rectangleComplementGraph hN hM
        (rectangleRootClusterUnion hN hM roots A)) (rectangleBaseGraph hN hM)
        (rectangleComplementEmbedding (rectangleRootClusterUnion hN hM roots A))
        (rectangleComplementGraph_map_le hN hM
          (rectangleRootClusterUnion hN hM roots A)) A) := by
  let U := rectangleRootClusterUnion hN hM roots A
  have hdisjoint : ∀ z, ActualConnected (rectangleBaseGraph hN hM) A u z → z ∉ U := by
    intro z huz hzU
    rcases hzU with ⟨x, hx, hxz⟩
    exact hseparate x hx (huz.trans hxz.symm).symm
  rcases hcross with ⟨v, hv, hreach⟩
  refine ⟨⟨v, hdisjoint v hreach⟩, hv, ?_⟩
  grind [rectangleComplementActualConnected_of_component_disjoint]
end

end PottsDiscontinuity.TorusLoops
