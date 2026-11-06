module

public import PottsDiscontinuity.FK.Events
public import PottsDiscontinuity.TorusLoops.RectangleExplorationWeightedStep

/-!
# Root-set exploration events on the cut rectangle

This module records the finite exploration states used to iterate the
one-step estimate. The explored vertex set is the union of the actual open
clusters of the already selected left-boundary roots.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus
open PottsDiscontinuity.FK

open scoped Classical

variable {N M : ℕ}

def rectangleDistinctRootCrossingEvent (hN : Even N) (hM : Even M)
    (roots : List (FaceVertex N M true)) :
    Set (Configuration (rectangleBaseGraph hN hM)) :=
  {A | (∀ x ∈ roots, A ∈ rectangleRootCrossingEvent hN hM x) ∧
    roots.Nodup ∧
    (∀ x ∈ roots, ∀ y ∈ roots, x ≠ y →
      ¬ ActualConnected (rectangleBaseGraph hN hM) A x y)}

def rectangleRootClusterUnion (hN : Even N) (hM : Even M)
    (roots : List (FaceVertex N M true))
    (A : Configuration (rectangleBaseGraph hN hM)) : Set (FaceVertex N M true) :=
  {v | ∃ x ∈ roots, ActualConnected (rectangleBaseGraph hN hM) A x v}

noncomputable def rectangleRootClusterFinset (hN : Even N) (hM : Even M)
    (A : Configuration (rectangleBaseGraph hN hM)) (root : FaceVertex N M true) :
    Finset (FaceVertex N M true) :=
  Finset.univ.filter fun v => ActualConnected (rectangleBaseGraph hN hM) A root v

@[simp] theorem mem_rectangleRootClusterFinset (hN : Even N) (hM : Even M)
    (A : Configuration (rectangleBaseGraph hN hM)) (root v : FaceVertex N M true) :
    v ∈ rectangleRootClusterFinset hN hM A root ↔
      ActualConnected (rectangleBaseGraph hN hM) A root v := by
  simp [rectangleRootClusterFinset]

noncomputable def rectangleLabeledRootClusterObservation
    (hN : Even N) (hM : Even M) (roots : List (FaceVertex N M true))
    (A : Configuration (rectangleBaseGraph hN hM)) :
    Finset (FaceVertex N M true × Finset (FaceVertex N M true)) :=
  roots.toFinset.image fun root =>
    (root, rectangleRootClusterFinset hN hM A root)

def rectangleLabeledObservationVertexSet
    (O : Finset (FaceVertex N M true × Finset (FaceVertex N M true))) :
    Set (FaceVertex N M true) :=
  {v | ∃ pair ∈ O, v ∈ pair.2}

theorem rectangleLabeledObservationVertexSet_eq_rootClusterUnion
    (hN : Even N) (hM : Even M) (roots : List (FaceVertex N M true))
    (A : Configuration (rectangleBaseGraph hN hM)) :
    rectangleLabeledObservationVertexSet
      (rectangleLabeledRootClusterObservation hN hM roots A) =
      rectangleRootClusterUnion hN hM roots A := by
  ext v
  simp [rectangleLabeledObservationVertexSet,
    rectangleLabeledRootClusterObservation, rectangleRootClusterFinset,
    rectangleRootClusterUnion]

theorem rectangleRootClusterFinset_eq_of_labeledObservation_eq
    (hN : Even N) (hM : Even M) (roots : List (FaceVertex N M true))
    (A B : Configuration (rectangleBaseGraph hN hM))
    (hobs : rectangleLabeledRootClusterObservation hN hM roots A =
      rectangleLabeledRootClusterObservation hN hM roots B)
    {root : FaceVertex N M true} (hroot : root ∈ roots) :
    rectangleRootClusterFinset hN hM A root =
      rectangleRootClusterFinset hN hM B root := by
  have hmemB : (root, rectangleRootClusterFinset hN hM A root) ∈
      rectangleLabeledRootClusterObservation hN hM roots B :=
    hobs ▸ Finset.mem_image.mpr ⟨root, by simpa using hroot, rfl⟩
  rcases Finset.mem_image.mp hmemB with ⟨other, _, heq⟩
  cases congrArg Prod.fst heq
  exact (congrArg Prod.snd heq).symm

private theorem rectangleDistinctRootCrossingEvent_labeledObservation_imp
    (hN : Even N) (hM : Even M) (roots : List (FaceVertex N M true))
    {A B : Configuration (rectangleBaseGraph hN hM)}
    (hobs : rectangleLabeledRootClusterObservation hN hM roots A =
      rectangleLabeledRootClusterObservation hN hM roots B)
    (hA : A ∈ rectangleDistinctRootCrossingEvent hN hM roots) :
    B ∈ rectangleDistinctRootCrossingEvent hN hM roots := by
  have hclusters (root : FaceVertex N M true) (hr : root ∈ roots) :=
    rectangleRootClusterFinset_eq_of_labeledObservation_eq hN hM roots A B hobs hr
  rcases hA with ⟨hcross, hnodup, hdistinct⟩
  refine ⟨fun root hroot => ?_, hnodup, fun x hx y hy hxy hconnB => hdistinct x hx y hy hxy ?_⟩
  · rcases hcross root hroot with ⟨v, hv, hconn⟩
    have hmem : v ∈ rectangleRootClusterFinset hN hM B root := by
      rw [← hclusters root hroot, mem_rectangleRootClusterFinset]; exact hconn
    exact ⟨v, hv, (mem_rectangleRootClusterFinset hN hM B root v).1 hmem⟩
  · have hmemA : y ∈ rectangleRootClusterFinset hN hM A x := by
      rw [hclusters x hx, mem_rectangleRootClusterFinset]; exact hconnB
    exact (mem_rectangleRootClusterFinset hN hM A x y).1 hmemA

theorem rectangleDistinctRootCrossingEvent_labeledObservation_invariant
    (hN : Even N) (hM : Even M) (roots : List (FaceVertex N M true))
    (A B : Configuration (rectangleBaseGraph hN hM))
    (hobs : rectangleLabeledRootClusterObservation hN hM roots A =
      rectangleLabeledRootClusterObservation hN hM roots B) :
    (A ∈ rectangleDistinctRootCrossingEvent hN hM roots ↔
      B ∈ rectangleDistinctRootCrossingEvent hN hM roots) :=
  ⟨rectangleDistinctRootCrossingEvent_labeledObservation_imp hN hM roots hobs,
   rectangleDistinctRootCrossingEvent_labeledObservation_imp hN hM roots hobs.symm⟩

def rectangleRootObservationIndex (hN : Even N) (hM : Even M)
    (roots : List (FaceVertex N M true)) :=
  {O : Finset (FaceVertex N M true × Finset (FaceVertex N M true)) //
    O ∈ Set.range (rectangleLabeledRootClusterObservation hN hM roots)}

noncomputable def rectangleRootObservationIndexOf
    (hN : Even N) (hM : Even M) (roots : List (FaceVertex N M true))
    (A : Configuration (rectangleBaseGraph hN hM)) :
    rectangleRootObservationIndex hN hM roots :=
  ⟨rectangleLabeledRootClusterObservation hN hM roots A, Set.mem_range_self A⟩

def rectangleGoodRootObservation (hN : Even N) (hM : Even M)
    (roots : List (FaceVertex N M true)) :
    Set (rectangleRootObservationIndex hN hM roots) :=
  {b | ∃ A, rectangleRootObservationIndexOf hN hM roots A = b ∧
    A ∈ rectangleDistinctRootCrossingEvent hN hM roots}

def rectangleObservationRemovedStateEvent
    (hN : Even N) (hM : Even M) (roots : List (FaceVertex N M true))
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
    (hN : Even N) (hM : Even M) (roots : List (FaceVertex N M true))
    (A : Configuration (rectangleBaseGraph hN hM)) :
    A ∈ rectangleDistinctRootCrossingEvent hN hM roots ↔
      rectangleRootObservationIndexOf hN hM roots A ∈
        rectangleGoodRootObservation hN hM roots :=
  ⟨fun hA => ⟨A, rfl, hA⟩, fun ⟨B, hB, hgood⟩ =>
    (rectangleDistinctRootCrossingEvent_labeledObservation_invariant
      hN hM roots B A (congrArg Subtype.val hB)).mp hgood⟩

theorem rectangleRootObservationIndex_fiber_has_law_support
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (roots : List (FaceVertex N M true))
    (b : rectangleRootObservationIndex hN hM roots) :
    ∃ A ∈ {A | rectangleRootObservationIndexOf hN hM roots A = b},
      A ∈ (law (rectangleBaseGraph hN hM) (rectangleFKParameters q)
        (BoundaryCondition.free ∅)).support := by
  rcases b.property with ⟨A, hA⟩
  exact ⟨A, Subtype.ext hA, by rw [law_support]; simp⟩

theorem rectangleRootClusterUnion_open_adj (hN : Even N) (hM : Even M)
    (roots : List (FaceVertex N M true))
    (A : Configuration (rectangleBaseGraph hN hM))
    {x y : FaceVertex N M true}
    (hxy : (openGraph (rectangleBaseGraph hN hM) A).Adj x y)
    (hx : x ∈ rectangleRootClusterUnion hN hM roots A) :
    y ∈ rectangleRootClusterUnion hN hM roots A := by
  rcases hx with ⟨r, hr, hreach⟩
  exact ⟨r, hr, hreach.trans hxy.reachable⟩

private theorem rectangleRemovedEdge_of_endpoint_mem
    (hN : Even N) (hM : Even M) (U : Set (FaceVertex N M true))
    {x y : FaceVertex N M true}
    (hxy : (rectangleBaseGraph hN hM).Adj x y) (hx : x ∈ U) :
    (⟨s(x, y), (rectangleBaseGraph hN hM).mem_edgeSet.mpr hxy⟩ :
      (rectangleBaseGraph hN hM).edgeSet) ∈ rectangleComplementRemovedEdges hN hM U := by
  rw [rectangleComplementRemovedEdges, mem_subgraphRemovedEdges]
  intro he
  obtain ⟨a, _, _, hax, _⟩ := (SimpleGraph.map_adj (rectangleComplementEmbedding U)
    (rectangleComplementGraph hN hM U) x y).mp
    (((rectangleComplementGraph hN hM U).map (rectangleComplementEmbedding U)).mem_edgeSet.mp he)
  exact a.property ((by simpa [rectangleComplementEmbedding] using hax : a.val = x) ▸ hx)

private theorem rectangleRemovedEdge_touches_U
    (hN : Even N) (hM : Even M) (U : Set (FaceVertex N M true))
    {e : (rectangleBaseGraph hN hM).edgeSet}
    (he : e ∈ rectangleComplementRemovedEdges hN hM U)
    (a b : FaceVertex N M true) (heq : e.val = s(a, b)) :
    a ∈ U ∨ b ∈ U := by
  by_contra hn
  have hbase : (rectangleBaseGraph hN hM).Adj a b :=
    (rectangleBaseGraph hN hM).mem_edgeSet.mp (heq ▸ e.property)
  have hnot : e.val ∉ ((rectangleComplementGraph hN hM U).map
      (rectangleComplementEmbedding U)).edgeSet :=
    (mem_subgraphRemovedEdges e).mp (by simpa [rectangleComplementRemovedEdges] using he)
  exact hnot (heq.symm ▸ ((rectangleComplementGraph hN hM U).map
    (rectangleComplementEmbedding U)).mem_edgeSet.mpr
    ((SimpleGraph.map_adj (rectangleComplementEmbedding U)
      (rectangleComplementGraph hN hM U) a b).mpr
      ⟨⟨a, fun ha => hn (Or.inl ha)⟩, ⟨b, fun hb => hn (Or.inr hb)⟩,
        by simpa [rectangleComplementGraph] using hbase, rfl, rfl⟩))

private theorem rectangleRemovedState_open_adj_of_mem
    (hN : Even N) (hM : Even M) (U : Set (FaceVertex N M true))
    (A : Configuration (rectangleBaseGraph hN hM))
    {x y : FaceVertex N M true} (hx : x ∈ U)
    (hxy : (openGraph (rectangleBaseGraph hN hM) A).Adj x y) :
    (openGraph (rectangleBaseGraph hN hM)
      (rectangleComplementRemovedState hN hM U A).val).Adj x y := by
  have hbase : (rectangleBaseGraph hN hM).Adj x y :=
    openGraph_le (rectangleBaseGraph hN hM) A hxy
  rcases (openGraph_adj (rectangleBaseGraph hN hM) A x y).mp hxy with ⟨e, heA, hexy⟩
  have heR : e ∈ rectangleComplementRemovedEdges hN hM U :=
    (Subtype.ext hexy : e = ⟨s(x, y), (rectangleBaseGraph hN hM).mem_edgeSet.mpr hbase⟩).symm ▸
      rectangleRemovedEdge_of_endpoint_mem hN hM U hbase hx
  have heK : e ∈ (rectangleComplementRemovedState hN hM U A).val := by
    simpa [rectangleComplementRemovedState, configurationSplitEquiv, heR] using heA
  exact (openGraph_adj (rectangleBaseGraph hN hM)
    (rectangleComplementRemovedState hN hM U A).val x y).mpr ⟨e, heK, hexy⟩

theorem rectangleRemovedState_open_edges_inside_of_observation
    (hN : Even N) (hM : Even M) (roots : List (FaceVertex N M true))
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
  have hKsub : K.val ⊆ A := fun e he => by
    have : e ∈ A ∧ e ∈ rectangleComplementRemovedEdges hN hM U := by
      simpa [K, rectangleComplementRemovedState, configurationSplitEquiv] using he
    exact this.1
  rcases (openGraph_adj G K.val x y).mp hxy with ⟨e, heK, hexy⟩
  have hxyA : (openGraph G A).Adj x y := (openGraph_adj G A x y).mpr ⟨e, hKsub heK, hexy⟩
  have hUeq := rectangleLabeledObservationVertexSet_eq_rootClusterUnion hN hM roots A
  rcases rectangleRemovedEdge_touches_U hN hM U (K.property heK) x y hexy with hx | hy
  · exact ⟨hx, hUeq.symm ▸ rectangleRootClusterUnion_open_adj hN hM roots A hxyA (hUeq ▸ hx)⟩
  · exact ⟨hUeq.symm ▸ rectangleRootClusterUnion_open_adj hN hM roots A hxyA.symm (hUeq ▸ hy), hy⟩

theorem rectangleRemovedState_clusterFinset_eq_of_open_edges_inside
    (hN : Even N) (hM : Even M) (U : Set (FaceVertex N M true))
    (A : Configuration (rectangleBaseGraph hN hM)) (root : FaceVertex N M true)
    (hroot : root ∈ U)
    (hclosed : ∀ ⦃x y : FaceVertex N M true⦄,
      (openGraph (rectangleBaseGraph hN hM)
        (rectangleComplementRemovedState hN hM U A).val).Adj x y → x ∈ U ∧ y ∈ U) :
    rectangleRootClusterFinset hN hM
        (rectangleComplementRemovedState hN hM U A).val root =
      rectangleRootClusterFinset hN hM A root := by
  let K := (rectangleComplementRemovedState hN hM U A).val
  have hKsub : K ⊆ A := fun e he => by
    have : e ∈ A ∧ e ∈ rectangleComplementRemovedEdges hN hM U := by
      simpa [K, rectangleComplementRemovedState, configurationSplitEquiv] using he
    exact this.1
  have htransfer : ∀ {x y : FaceVertex N M true},
      (openGraph (rectangleBaseGraph hN hM) A).Reachable x y → x ∈ U →
      (openGraph (rectangleBaseGraph hN hM) K).Reachable x y ∧ y ∈ U := by
    rintro x y ⟨w⟩ hx
    induction w with
    | nil => exact ⟨SimpleGraph.Reachable.rfl, hx⟩
    | @cons x y z hxy w ih =>
      have hxyK := rectangleRemovedState_open_adj_of_mem hN hM U A hx hxy
      exact ⟨hxyK.reachable.trans (ih (hclosed hxyK).2).1, (ih (hclosed hxyK).2).2⟩
  ext v
  simp only [mem_rectangleRootClusterFinset]
  exact ⟨actualConnected_mono hKsub, fun hreach => (htransfer hreach hroot).1⟩

theorem rectangleRemovedState_mem_observationRemovedStateEvent
    (hN : Even N) (hM : Even M) (roots : List (FaceVertex N M true))
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
        x ∈ U ∧ y ∈ U :=
    fun _ _ => rectangleRemovedState_open_edges_inside_of_observation hN hM roots A
  have hUeq : U = rectangleRootClusterUnion hN hM roots A :=
    rectangleLabeledObservationVertexSet_eq_rootClusterUnion hN hM roots A
  refine ⟨fun root hroot => ?_, hclosed⟩
  rw [rectangleRemovedState_clusterFinset_eq_of_open_edges_inside hN hM U A root
    (hUeq.symm ▸ ⟨root, hroot, SimpleGraph.Reachable.rfl⟩) hclosed]
  exact Finset.mem_image.mpr ⟨root, by simpa using hroot, rfl⟩

private theorem rectangleComplementOpenAdj_of_openAdj
    (hN : Even N) (hM : Even M) (U : Set (FaceVertex N M true))
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
  have hI : I.Adj ⟨x, hx⟩ ⟨y, hy⟩ := by
    simpa [I, rectangleComplementGraph] using openGraph_le G A hxy
  let eI : I.edgeSet := ⟨s(⟨x, hx⟩, ⟨y, hy⟩), I.mem_edgeSet.mpr hI⟩
  rcases (openGraph_adj G A x y).mp hxy with ⟨eG, heG, heqG⟩
  have heC : eI ∈ embeddedConfigurationRestriction I G f hIG A := by
    rw [mem_embeddedConfigurationRestriction, show embeddedEdgeEmbedding I G f hIG eI = eG from
      Subtype.ext (by simp [embeddedEdgeEmbedding_coe, eI, f, rectangleComplementEmbedding, heqG])]
    exact heG
  exact (openGraph_adj I _ ⟨x, hx⟩ ⟨y, hy⟩).mpr ⟨eI, heC, rfl⟩

private theorem rectangleComplementActualConnected_of_component_disjoint
    (hN : Even N) (hM : Even M) (U : Set (FaceVertex N M true))
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
      (w : (openGraph G A).Walk x y) (hroot : ActualConnected G A root x),
      ActualConnected I C ⟨x, hdisjoint x hroot⟩
        ⟨y, hdisjoint y (hroot.trans w.reachable)⟩ := by
    intro x y w hroot
    induction w with
    | nil => exact SimpleGraph.Reachable.rfl
    | @cons x y z hxy w ih =>
      exact (rectangleComplementOpenAdj_of_openAdj hN hM U A
        (hdisjoint x hroot) (hdisjoint y (hroot.trans hxy.reachable)) hxy).reachable.trans
        (ih (hroot.trans hxy.reachable))
  rcases hreach with ⟨w⟩
  exact hwalk w SimpleGraph.Reachable.rfl

theorem rectangleRootCrossing_complement_of_distinct_roots
    (hN : Even N) (hM : Even M) (roots : List (FaceVertex N M true))
    (A : Configuration (rectangleBaseGraph hN hM)) (u : FaceVertex N M true)
    (hseparate : ∀ x ∈ roots,
      ¬ ActualConnected (rectangleBaseGraph hN hM) A x u)
    (hcross : A ∈ rectangleRootCrossingEvent hN hM u) :
    rectangleComplementRootCrossingEvent hN hM
      (rectangleRootClusterUnion hN hM roots A) u
      (fun ⟨x, hx, hxu⟩ => hseparate x hx hxu)
      (embeddedConfigurationRestriction (rectangleComplementGraph hN hM
        (rectangleRootClusterUnion hN hM roots A)) (rectangleBaseGraph hN hM)
        (rectangleComplementEmbedding (rectangleRootClusterUnion hN hM roots A))
        (rectangleComplementGraph_map_le hN hM
          (rectangleRootClusterUnion hN hM roots A)) A) := by
  have hdisjoint : ∀ z, ActualConnected (rectangleBaseGraph hN hM) A u z →
      z ∉ rectangleRootClusterUnion hN hM roots A :=
    fun _ huz ⟨x, hx, hxz⟩ => hseparate x hx (huz.trans hxz.symm).symm
  rcases hcross with ⟨v, hv, hreach⟩
  exact ⟨⟨v, hdisjoint v hreach⟩, hv,
    rectangleComplementActualConnected_of_component_disjoint hN hM _ A u v hdisjoint hreach⟩

end PottsDiscontinuity.TorusLoops
