module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Topology.Instances.EReal.Lemmas
public import PottsDiscontinuity.CorrLength.ConnectionEvents
public import PottsDiscontinuity.CorrLength.RotatedLattice
public import PottsDiscontinuity.Duality.ConnectionEvents
public import PottsDiscontinuity.Duality.ConnectionSymmetry
public import PottsDiscontinuity.Duality.FiniteDuality
public import PottsDiscontinuity.FK.BoundaryPartitionLaw
public import PottsDiscontinuity.FK.ConditionalEmbeddedLaw
public import PottsDiscontinuity.FK.ConditionalLaw
public import PottsDiscontinuity.FK.DomainMarkov
public import PottsDiscontinuity.FK.Events
public import PottsDiscontinuity.FK.Expectation
public import PottsDiscontinuity.FK.Graph
public import PottsDiscontinuity.FK.IncreasingEvents
public import PottsDiscontinuity.FK.SubgraphComparison
public import PottsDiscontinuity.RCMProof.Contracts
public import PottsDiscontinuity.SixVertex.InfinityEndpointOrder
public import PottsDiscontinuity.Torus.DiamondClusterProjection
public import PottsDiscontinuity.Torus.DiamondFullFlows
public import PottsDiscontinuity.Torus.DiamondGraph
public import PottsDiscontinuity.Torus.DiamondIntersectionLocality
public import PottsDiscontinuity.Torus.DiamondSeamWinding
public import PottsDiscontinuity.Torus.RibbonConnectivity
public import PottsDiscontinuity.Torus.RibbonIntersection
public import PottsDiscontinuity.Torus.WindingReorientation
public import PottsDiscontinuity.TorusLoops.FiniteEnergy
public import PottsDiscontinuity.TorusRC.CylinderEvents
public import PottsDiscontinuity.TorusRC.ElementaryTail
public import PottsDiscontinuity.TorusRC.IndexedGraphBridge
public import PottsDiscontinuity.TorusRC.MeasureBridge
public import PottsDiscontinuity.TorusTopology.LiftedPotentials
public import PottsDiscontinuity.TorusTopology.PositiveLoops

/-! # Equation (3.16): torus vertical-winding tail rate via adaptive cluster exploration -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration

open Torus TorusRC TorusTopology FK FK.FiniteProbability CorrLength MeasureTheory Filter Topology Finset
open PottsDiscontinuity.SixVertex

noncomputable section
open scoped Classical

attribute [local instance] configurationMeasurableSpace

/-! ### 1. PMF Conditioning, Fiber Averaging, and Closed-Subgraph Law -/

private theorem joint_expectation_le_filter {α : Type*} [Fintype α] (p : PMF α) (T E : Set α)
    (hT : ∃ a ∈ T, a ∈ p.support) :
    expectation p ((T ∩ E).indicator fun _ => (1 : ℝ)) ≤
      expectation (p.filter T hT) (E.indicator fun _ => (1 : ℝ)) := by
  refine Finset.sum_le_sum fun a _ => ?_
  by_cases ha : a ∈ T
  · by_cases he : a ∈ E
    · simp only [Set.indicator_of_mem (show a ∈ T ∩ E from ⟨ha, he⟩), Set.indicator_of_mem he, mul_one]
      refine ENNReal.toReal_mono ((p.filter T hT).apply_ne_top a) ?_
      rw [PMF.filter_apply, Set.indicator_of_mem ha]
      have hden : (∑' b, T.indicator p b) ≤ 1 := by
        rw [← p.tsum_coe]; exact ENNReal.tsum_le_tsum fun b => by by_cases hb : b ∈ T <;> simp [hb]
      have hinv : (1 : ENNReal) ≤ (∑' b, T.indicator p b)⁻¹ := by simpa using ENNReal.inv_le_inv.mpr hden
      simpa only [mul_one] using mul_le_mul' (le_refl (p a)) hinv
    · simp [he]
  · simp only [Set.indicator_of_notMem (show a ∉ T ∩ E from fun h => ha h.1), mul_zero]
    by_cases he : a ∈ E
    · rw [Set.indicator_of_mem he, mul_one]; exact ENNReal.toReal_nonneg
    · simp [he]

private def recordConditional {α β : Type*} [Fintype α]
    (p : PMF α) (hp : ∀ a, a ∈ p.support) (f : α → β) (a : α) : PMF α :=
  p.filter {b | f b = f a} ⟨a, rfl, hp a⟩

private lemma expectation_congr_on_support {α : Type*} [Fintype α] (p : PMF α) (F G : α → ℝ)
    (h : ∀ a, a ∈ p.support → F a = G a) : expectation p F = expectation p G :=
  Finset.sum_congr rfl fun a _ => by
    by_cases ha : p a = 0
    · simp [ha]
    · rw [h a ha]

private lemma expectation_le_on_support {α : Type*} [Fintype α] (p : PMF α) (F H : α → ℝ)
    (h : ∀ a, a ∈ p.support → F a ≤ H a) : expectation p F ≤ expectation p H :=
  Finset.sum_le_sum fun a _ => by
    by_cases ha : p a = 0
    · simp [ha]
    · exact mul_le_mul_of_nonneg_left (h a ha) ENNReal.toReal_nonneg

private theorem record_step_le {α β : Type*} [Fintype α] (p : PMF α) (hp : ∀ a, a ∈ p.support)
    (f : α → β) (E H : Set α) (hE : ∀ a b, f b = f a → (b ∈ E ↔ a ∈ E)) (c : ℝ)
    (hc : ∀ a ∈ E, expectation (recordConditional p hp f a) (H.indicator fun _ => (1 : ℝ)) ≤ c) :
    expectation p ((E ∩ H).indicator fun _ => (1 : ℝ)) ≤
      c * expectation p (E.indicator fun _ => (1 : ℝ)) := by
  have hbind : p.bind (recordConditional p hp f) = p := by
    ext b; rw [PMF.bind_apply, tsum_fintype]
    have he (a : α) : p a * recordConditional p hp f a b =
        (if f a = f b then p a else 0) * (p b * (∑ x : α, if f x = f b then p x else 0)⁻¹) := by
      rw [recordConditional, PMF.filter_apply, tsum_fintype]
      by_cases h : f a = f b
      · rw [show {x : α | f x = f a} = {x | f x = f b} by rw [h]]
        simp [Set.indicator_apply, h]
      · simp [Set.indicator_apply, h, Ne.symm h]
    simp_rw [he]
    have hnz : (∑ x : α, if f x = f b then p x else 0) ≠ 0 := fun hz => by
      have ha : p b ≤ ∑ x : α, if f x = f b then p x else 0 := by
        simpa only [ite_true] using
          (Finset.single_le_sum (f := fun x : α => if f x = f b then p x else 0)
            (fun _ _ => bot_le) (Finset.mem_univ b) :
            (if f b = f b then p b else 0) ≤ _)
      exact hp b (le_zero_iff.mp (hz ▸ ha))
    have hnt : (∑ x : α, if f x = f b then p x else 0) ≠ ⊤ := by
      simpa only [tsum_fintype, Set.indicator_apply, Set.mem_ofPred_eq] using
        p.tsum_coe_indicator_ne_top {x | f x = f b}
    rw [← Finset.sum_mul, mul_comm (p b), ← mul_assoc, ENNReal.mul_inv_cancel hnz hnt, one_mul]
  conv_lhs => rw [← hbind, expectation_bind]
  calc _ ≤ expectation p (E.indicator fun _ => c) := expectation_mono p _ _ fun a => by
        by_cases ha : a ∈ E
        · have heq : expectation (recordConditional p hp f a) ((E ∩ H).indicator fun _ => (1 : ℝ)) =
              expectation (recordConditional p hp f a) (H.indicator fun _ => (1 : ℝ)) :=
            expectation_congr_on_support _ _ _ fun b hb => by
              have hbE := (hE a b ((PMF.mem_support_filter_iff _).1 hb).1).2 ha
              by_cases hbH : b ∈ H <;> simp [hbE, hbH]
          rw [heq, Set.indicator_of_mem ha]; exact hc a ha
        · have heq : expectation (recordConditional p hp f a) ((E ∩ H).indicator fun _ => (1 : ℝ)) = 0 := by
            rw [← expectation_const (recordConditional p hp f a) 0]
            exact expectation_congr_on_support _ _ _ fun b hb => by
              have hbE : b ∉ E := fun h => ha ((hE a b ((PMF.mem_support_filter_iff _).1 hb).1).1 h)
              simp [hbE]
          rw [heq, Set.indicator_of_notMem ha]
    _ = _ := by
        unfold expectation; rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => by by_cases ha : a ∈ E <;> simp [ha]; ring

section FiniteGraph
variable {V : Type*} [Finite V]
local instance {G : SimpleGraph V} : Fintype G.edgeSet := Fintype.ofFinite _
local instance {G : SimpleGraph V} : DecidableEq G.edgeSet := Classical.decEq _

private lemma fk_measureReal_eq_expectation (G : SimpleGraph V) (θ : Parameters)
    (ξ : BoundaryCondition V) (E : Set (Configuration G)) :
    (measure G θ ξ E).toReal = expectation (law G θ ξ) (E.indicator fun _ => (1 : ℝ)) := by
  rw [measure_toReal_eq_indicator_sum]; unfold expectation
  exact Finset.sum_congr rfl fun A _ => by
    rw [law_apply, ENNReal.toReal_ofReal (configurationProbability_pos G θ ξ A).le]

private def closedSubgraphRecord (G H : SimpleGraph V) : RemovedConfiguration H (subgraphRemovedEdges G H) :=
  ⟨∅, Finset.empty_subset _⟩

private def subgraphRemainderRead {G H : SimpleGraph V} (hGH : G ≤ H) (C : Configuration H) : Configuration G :=
  (subgraphRemainingConfigurationEquiv hGH).symm (configurationSplitEquiv H (subgraphRemovedEdges G H) C).1

private lemma closedSubgraph_reconstruct {G H : SimpleGraph V}
    (hGH : G ≤ H) (C : Configuration H)
    (hC : C ∈ frozenStateEvent (subgraphRemovedEdges G H) (closedSubgraphRecord G H)) :
    subgraphConfigurationEmbedding hGH (subgraphRemainderRead hGH C) = C := by
  have he := congrArg Subtype.val ((subgraphRemainingConfigurationEquiv hGH).apply_symm_apply
    (configurationSplitEquiv H (subgraphRemovedEdges G H) C).1)
  change subgraphConfigurationEmbedding hGH (subgraphRemainderRead hGH C) = C \ subgraphRemovedEdges G H at he
  change C ∩ subgraphRemovedEdges G H = ∅ at hC
  rwa [Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_iff_inter_eq_empty.2 hC)] at he

private theorem closedSubgraph_joint_le {G H : SimpleGraph V} (hGH : G ≤ H)
    (θ : Parameters) (E : Set (Configuration G)) :
    expectation (law H θ (BoundaryCondition.free ∅))
      ((frozenStateEvent (subgraphRemovedEdges G H) (closedSubgraphRecord G H) ∩
        (subgraphRemainderRead hGH) ⁻¹' E).indicator fun _ => (1 : ℝ)) ≤
      expectation (law G θ (BoundaryCondition.free ∅)) (E.indicator fun _ => (1 : ℝ)) := by
  let R := subgraphRemovedEdges G H
  let K := closedSubgraphRecord G H
  refine (joint_expectation_le_filter (law H θ (BoundaryCondition.free ∅))
    (frozenStateEvent R K) ((subgraphRemainderRead hGH) ⁻¹' E)
    (frozenStateEvent_support θ (BoundaryCondition.free ∅) R K)).trans_eq ?_
  let P := (law H θ (BoundaryCondition.free ∅)).filter (frozenStateEvent R K)
    (frozenStateEvent_support θ (BoundaryCondition.free ∅) R K)
  have hmap : P.map (subgraphRemainderRead hGH) = law G θ (BoundaryCondition.free ∅) := by
    have he : P.map (subgraphRemainderRead hGH) =
        (P.map fun C => (configurationSplitEquiv H R C).1).map (subgraphRemainingConfigurationEquiv hGH).symm := by
      rw [PMF.map_comp]; rfl
    rw [he, law_filter_frozen_map_remaining, ← law_subgraphRemaining_map hGH θ (frozenBoundary (BoundaryCondition.free ∅) K.val),
      PMF.map_comp, show (subgraphRemainingConfigurationEquiv hGH).symm ∘ subgraphRemainingConfigurationEquiv hGH = id by
        funext C; simp, PMF.map_id]
    exact law_eq_of_boundary_partition_eq θ _ _ (by change componentSetoid H (BoundaryCondition.free ∅) ∅ = _; rw [componentSetoid_empty])
  change expectation P (fun C => E.indicator (fun _ => (1 : ℝ)) (subgraphRemainderRead hGH C)) = _
  rw [← expectation_map, hmap]

/-! ### 2. Multi-Seed Cluster Exploration and Adaptive Domain Markov -/

private def actualClusterReveal (G : SimpleGraph V) (v : V) (A : Configuration G) : Configuration G :=
  Finset.univ.filter fun e : G.edgeSet => ∃ u : V, u ∈ e.1 ∧ ActualConnected G A v u

private theorem actualConnected_iff_of_reveal_agreement (G : SimpleGraph V) (v : V)
    (A B : Configuration G) (hagree : B ∩ actualClusterReveal G v A = A ∩ actualClusterReveal G v A) (u : V) :
    ActualConnected G B v u ↔ ActualConnected G A v u := by
  have hstate {e : G.edgeSet} (he : e ∈ actualClusterReveal G v A) : e ∈ B ↔ e ∈ A := by
    simpa [Finset.mem_inter, he] using Finset.ext_iff.mp hagree e
  have hadj_mem (C : Configuration G) {x y : V} (h : (openGraph G C).Adj x y) :
      (⟨s(x, y), G.mem_edgeSet.mpr ((openGraph_le G C) h)⟩ : G.edgeSet) ∈ C := by
    obtain ⟨e, heC, heq⟩ := (openGraph_adj G C x y).mp h
    have he' : e = ⟨s(x, y), G.mem_edgeSet.mpr ((openGraph_le G C) h)⟩ := Subtype.ext heq
    rwa [← he']
  have mem_hadj (C : Configuration G) {x y : V} (hxy : G.Adj x y)
      (he : (⟨s(x, y), G.mem_edgeSet.mpr hxy⟩ : G.edgeSet) ∈ C) : (openGraph G C).Adj x y :=
    (openGraph_adj G C x y).mpr ⟨⟨s(x, y), G.mem_edgeSet.mpr hxy⟩, he, rfl⟩
  constructor <;> intro hu <;> change (openGraph G _).Reachable v u at hu ⊢ <;>
    rw [SimpleGraph.reachable_iff_reflTransGen] at hu ⊢
  · induction hu with
    | refl => exact Relation.ReflTransGen.refl
    | @tail y z _ hedge ih =>
      have hyA : ActualConnected G A v y := (SimpleGraph.reachable_iff_reflTransGen v y).mpr ih
      have hG : G.Adj y z := (openGraph_le G B) hedge
      have heR : (⟨s(y, z), G.mem_edgeSet.mpr hG⟩ : G.edgeSet) ∈ actualClusterReveal G v A := by
        simp only [actualClusterReveal, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨y, Sym2.mem_iff'.2 (Or.inl rfl), hyA⟩
      exact Relation.ReflTransGen.tail ih (mem_hadj A hG ((hstate heR).mp (hadj_mem B hedge)))
  · induction hu with
    | refl => exact Relation.ReflTransGen.refl
    | @tail y z hpref hedge ih =>
      have hyA : ActualConnected G A v y := (SimpleGraph.reachable_iff_reflTransGen v y).mpr hpref
      have hG : G.Adj y z := (openGraph_le G A) hedge
      have heR : (⟨s(y, z), G.mem_edgeSet.mpr hG⟩ : G.edgeSet) ∈ actualClusterReveal G v A := by
        simp only [actualClusterReveal, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨y, Sym2.mem_iff'.2 (Or.inl rfl), hyA⟩
      exact Relation.ReflTransGen.tail ih (mem_hadj B hG ((hstate heR).mpr (hadj_mem A hedge)))

private def actualMultiClusterConnected (G : SimpleGraph V) (S : Finset V) (A : Configuration G) (u : V) : Prop :=
  ∃ s ∈ S, ActualConnected G A s u

private def actualMultiClusterReveal (G : SimpleGraph V) (S : Finset V) (A : Configuration G) : Configuration G :=
  Finset.univ.filter fun e : G.edgeSet => ∃ u : V, u ∈ e.1 ∧ actualMultiClusterConnected G S A u

private def actualMultiClusterComplementSet (G : SimpleGraph V) (S : Finset V) (A : Configuration G) : Set V :=
  {u | ¬ actualMultiClusterConnected G S A u}

private def inducedVertexEmbedding (T : Set V) : T ↪ V := ⟨Subtype.val, Subtype.val_injective⟩

omit [Finite V] in
private lemma inducedVertexGraph_le (G : SimpleGraph V) (T : Set V) :
    (G.induce T).map (inducedVertexEmbedding T) ≤ G := by
  intro a b hab; obtain ⟨u, v, huv, rfl, rfl⟩ := (SimpleGraph.map_adj _ _ _ _).1 hab; exact huv

omit [Finite V] in
private theorem actualConnected_inducedRestriction (G : SimpleGraph V) (T : Set V) (A : Configuration G)
    (hT : ∀ a ∈ T, ∀ b, (openGraph G A).Adj a b → b ∈ T) (u v : T) :
    ActualConnected (G.induce T) (embeddedConfigurationRestriction (G.induce T) G
      (inducedVertexEmbedding T) (inducedVertexGraph_le G T) A) u v ↔
      ActualConnected G A u.val v.val := by
  have hadj (a b : T) : (openGraph (G.induce T) (embeddedConfigurationRestriction (G.induce T) G
      (inducedVertexEmbedding T) (inducedVertexGraph_le G T) A)).Adj a b ↔ (openGraph G A).Adj a.val b.val := by
    rw [openGraph_adj, openGraph_adj]
    refine ⟨fun ⟨e, he, hep⟩ => ⟨embeddedEdgeEmbedding _ _ _ _ e,
        (mem_embeddedConfigurationRestriction _ _ _ _ _ _).1 he,
        by change Sym2.map Subtype.val e.val = s(a.val, b.val); rw [hep]; rfl⟩,
      fun ⟨e, he, hep⟩ => ?_⟩
    have hg : G.Adj a.val b.val := G.mem_edgeSet.1 (hep ▸ e.property)
    refine ⟨⟨s(a, b), hg⟩, (mem_embeddedConfigurationRestriction _ _ _ _ A _).2 ?_, rfl⟩
    rwa [show embeddedEdgeEmbedding (G.induce T) G (inducedVertexEmbedding T) (inducedVertexGraph_le G T) ⟨s(a, b), hg⟩ = e from
      Subtype.ext hep.symm]
  refine ⟨fun ⟨p⟩ => ⟨p.map {toFun := Subtype.val, map_rel' := fun h => (hadj _ _).1 h}⟩, fun ⟨p⟩ => ?_⟩
  have lift {a b : V} (p : (openGraph G A).Walk a b) (ha : a ∈ T) (hb : b ∈ T) :
      (openGraph (G.induce T) (embeddedConfigurationRestriction (G.induce T) G
        (inducedVertexEmbedding T) (inducedVertexGraph_le G T) A)).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons a b c hab p ih =>
      have hb' := hT a ha b hab
      exact ((hadj ⟨a, ha⟩ ⟨b, hb'⟩).2 hab).reachable.trans (ih hb' hb)
  exact lift p u.property v.property

private def clusterRecord (G : SimpleGraph V) (S : Finset V) (A : Configuration G) :
    Configuration G × Configuration G :=
  (actualMultiClusterReveal G S A, A ∩ actualMultiClusterReveal G S A)

private lemma seed_connection_iff_of_multi_agree (G : SimpleGraph V) (S : Finset V)
    (A B : Configuration G) (hagree : B ∩ actualMultiClusterReveal G S A = A ∩ actualMultiClusterReveal G S A)
    {s : V} (hs : s ∈ S) (u : V) :
    ActualConnected G B s u ↔ ActualConnected G A s u := by
  have hsub : actualClusterReveal G s A ⊆ actualMultiClusterReveal G S A := fun e he => by
    simp only [actualClusterReveal, actualMultiClusterReveal, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    obtain ⟨w, hw, hc⟩ := he; exact ⟨w, hw, s, hs, hc⟩
  have hag : B ∩ actualClusterReveal G s A = A ∩ actualClusterReveal G s A := by
    ext e; have he := Finset.ext_iff.1 hagree e
    simp only [Finset.mem_inter] at he ⊢
    exact ⟨fun ⟨hB, hR⟩ => ⟨(he.1 ⟨hB, hsub hR⟩).1, hR⟩, fun ⟨hA, hR⟩ => ⟨(he.2 ⟨hA, hsub hR⟩).1, hR⟩⟩
  exact actualConnected_iff_of_reveal_agreement G s A B hag u

private lemma clusterRecord_eq_iff_frozen (G : SimpleGraph V) (S : Finset V) (A B : Configuration G) :
    clusterRecord G S B = clusterRecord G S A ↔ B ∩ actualMultiClusterReveal G S A = A ∩ actualMultiClusterReveal G S A := by
  simp only [clusterRecord, Prod.mk.injEq]
  refine ⟨fun ⟨hR, hA⟩ => by rwa [hR] at hA, fun hagree => ?_⟩
  have hR : actualMultiClusterReveal G S B = actualMultiClusterReveal G S A :=
    Finset.ext fun e => by
      unfold actualMultiClusterReveal
      rw [Finset.mem_filter, Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, actualMultiClusterConnected]
      exact ⟨fun ⟨u, hu, s, hs, hc⟩ => ⟨u, hu, s, hs, (seed_connection_iff_of_multi_agree G S A B hagree hs u).mp hc⟩,
        fun ⟨u, hu, s, hs, hc⟩ => ⟨u, hu, s, hs, (seed_connection_iff_of_multi_agree G S A B hagree hs u).mpr hc⟩⟩
  exact ⟨hR, by rwa [hR]⟩

private def distinctConnections (G : SimpleGraph V) (x y : ℕ → V) (j : ℕ) : Set (Configuration G) :=
  {A | (∀ i < j, ActualConnected G A (x i) (y i)) ∧
    ∀ i < j, ∀ k < j, i ≠ k → ¬ ActualConnected G A (x i) (x k)}

private def prefixSeeds (x : ℕ → V) (j : ℕ) : Finset V := (Finset.range j).image x

private def nextDistinctConnection (G : SimpleGraph V) (x y : ℕ → V) (j : ℕ) : Set (Configuration G) :=
  {A | ActualConnected G A (x j) (y j) ∧ ∀ i < j, ¬ ActualConnected G A (x i) (x j)}

private theorem distinctConnections_probability_le_pow (G : SimpleGraph V) (θ : Parameters)
    (x y : ℕ → V) (c : ℝ) (hc0 : 0 ≤ c)
    (hcomp : ∀ j : ℕ, 1 ≤ j → ∀ A ∈ distinctConnections G x y j,
      ∀ (hx : x j ∈ actualMultiClusterComplementSet G (prefixSeeds x j) A)
        (hy : y j ∈ actualMultiClusterComplementSet G (prefixSeeds x j) A),
      (measure (G.induce (actualMultiClusterComplementSet G (prefixSeeds x j) A)) θ
        (BoundaryCondition.free ∅) (connectivityEvent _ ⟨x j, hx⟩ ⟨y j, hy⟩)).toReal ≤ c)
    (r : ℕ) (hr : 1 ≤ r) :
    (measure G θ (BoundaryCondition.free ∅) (distinctConnections G x y r)).toReal ≤ c ^ (r - 1) := by
  have hsupp (A : Configuration G) : A ∈ (law G θ (BoundaryCondition.free ∅)).support := by
    rw [law_support]; trivial
  rw [fk_measureReal_eq_expectation]
  induction r, hr using Nat.le_induction with
  | base =>
    simp only [Nat.sub_self, pow_zero]
    exact (expectation_mono _ _ (fun _ => 1) fun A => by
      by_cases ha : A ∈ distinctConnections G x y 1 <;> simp [ha]).trans_eq (expectation_const _ _)
  | succ r hr ih =>
    have hsucc : distinctConnections G x y (r + 1) = distinctConnections G x y r ∩ nextDistinctConnection G x y r := by
      ext A; refine ⟨fun ⟨hc, hd⟩ => ⟨⟨fun i hi => hc i (by omega), fun i hi k hk hik => hd i (by omega) k (by omega) hik⟩,
          hc r (by omega), fun i hi => hd i (by omega) r (by omega) (by omega)⟩,
        fun ⟨⟨hc, hd⟩, hn, hdis⟩ => ⟨fun i hi => if hij : i = r then hij ▸ hn else hc i (by omega),
          fun i hi k hk hik => ?_⟩⟩
      by_cases hij : i = r
      · subst i; exact fun h => hdis k (by omega) h.symm
      · by_cases hkj : k = r
        · subst k; exact hdis i (by omega)
        · exact hd i (by omega) k (by omega) hik
    have hmeas (A B : Configuration G)
        (h : clusterRecord G (prefixSeeds x r) B = clusterRecord G (prefixSeeds x r) A) :
        B ∈ distinctConnections G x y r ↔ A ∈ distinctConnections G x y r := by
      have hag := (clusterRecord_eq_iff_frozen G (prefixSeeds x r) A B).1 h
      have hc (i : ℕ) (hi : i < r) (v : V) : ActualConnected G B (x i) v ↔ ActualConnected G A (x i) v :=
        seed_connection_iff_of_multi_agree G _ A B hag (Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩) v
      exact ⟨fun ⟨h₁, h₂⟩ => ⟨fun i hi => (hc i hi _).1 (h₁ i hi), fun i hi k hk hik hh => h₂ i hi k hk hik ((hc i hi _).2 hh)⟩,
        fun ⟨h₁, h₂⟩ => ⟨fun i hi => (hc i hi _).2 (h₁ i hi), fun i hi k hk hik hh => h₂ i hi k hk hik ((hc i hi _).1 hh)⟩⟩
    have hcond (A : Configuration G) (hA : A ∈ distinctConnections G x y r) :
        expectation (recordConditional (law G θ (BoundaryCondition.free ∅)) hsupp (clusterRecord G (prefixSeeds x r)) A)
          ((nextDistinctConnection G x y r).indicator fun _ => (1 : ℝ)) ≤ c := by
      let S := prefixSeeds x r
      let T := actualMultiClusterComplementSet G S A
      let P := recordConditional (law G θ (BoundaryCondition.free ∅)) hsupp (clusterRecord G S) A
      have hout (B : Configuration G) (hB : B ∈ P.support) (v : V) :
          v ∈ actualMultiClusterComplementSet G S B ↔ v ∈ T := by
        have hag := (clusterRecord_eq_iff_frozen G S A B).1 ((PMF.mem_support_filter_iff _).1 hB).1
        exact not_congr ⟨fun ⟨s, hs, hc⟩ => ⟨s, hs, (seed_connection_iff_of_multi_agree G S A B hag hs v).mp hc⟩,
          fun ⟨s, hs, hc⟩ => ⟨s, hs, (seed_connection_iff_of_multi_agree G S A B hag hs v).mpr hc⟩⟩
      have hnext_out {B : Configuration G} (h : B ∈ nextDistinctConnection G x y r) :
          x r ∈ actualMultiClusterComplementSet G S B ∧ y r ∈ actualMultiClusterComplementSet G S B :=
        ⟨fun ⟨s, hs, hc⟩ => by obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hs; exact h.2 i (Finset.mem_range.1 hi) hc,
         fun ⟨s, hs, hc⟩ => by obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hs; exact h.2 i (Finset.mem_range.1 hi) (hc.trans h.1.symm)⟩
      by_cases hx : x r ∈ T
      · by_cases hy : y r ∈ T
        · let u : T := ⟨x r, hx⟩; let v : T := ⟨y r, hy⟩
          let H := G.induce T; let emb := inducedVertexEmbedding T
          let hHG := inducedVertexGraph_le G T
          let res := embeddedConfigurationRestriction H G emb hHG
          have hedg : edgeRestriction G (actualMultiClusterReveal G S A) = H.map emb := by
            ext a b; constructor
            · intro hab
              obtain ⟨hAdj, hNot⟩ : G.Adj a b ∧ s(a, b) ∉ openEdges G (actualMultiClusterReveal G S A) := by
                simpa [edgeRestriction] using hab
              have hna : a ∈ T := fun ⟨s, hs, hc⟩ => hNot (by
                simpa using (coe_mem_openEdges_iff G (actualMultiClusterReveal G S A) ⟨s(a, b), G.mem_edgeSet.mpr hAdj⟩).mpr
                  (Finset.mem_filter.mpr ⟨Finset.mem_univ _, a, Sym2.mem_iff'.2 (Or.inl rfl), s, hs, hc⟩))
              have hnb : b ∈ T := fun ⟨s, hs, hc⟩ => hNot (by
                simpa using (coe_mem_openEdges_iff G (actualMultiClusterReveal G S A) ⟨s(a, b), G.mem_edgeSet.mpr hAdj⟩).mpr
                  (Finset.mem_filter.mpr ⟨Finset.mem_univ _, b, Sym2.mem_iff'.2 (Or.inr rfl), s, hs, hc⟩))
              exact (SimpleGraph.map_adj emb H a b).2 ⟨⟨a, hna⟩, ⟨b, hnb⟩, SimpleGraph.induce_adj.mpr hAdj, rfl, rfl⟩
            · intro hab
              obtain ⟨a', b', hInd, rfl, rfl⟩ := (SimpleGraph.map_adj emb H a b).1 hab
              have hAdj : G.Adj a'.val b'.val := SimpleGraph.induce_adj.mp hInd
              rw [edgeRestriction, SimpleGraph.deleteEdges_adj]
              refine ⟨hAdj, fun hm => ?_⟩
              have hR := (coe_mem_openEdges_iff G (actualMultiClusterReveal G S A) ⟨s(a'.val, b'.val), G.mem_edgeSet.mpr hAdj⟩).mp hm
              obtain ⟨_, ⟨z, hz, s, hs, hc⟩⟩ := Finset.mem_filter.mp hR
              rcases Sym2.mem_iff'.mp hz with rfl | rfl
              · exact a'.2 ⟨s, hs, hc⟩
              · exact b'.2 ⟨s, hs, hc⟩
          have hrem : actualMultiClusterReveal G S A = subgraphRemovedEdges (H.map emb) G := by
            ext e; rw [mem_subgraphRemovedEdges]
            have hg := congrArg SimpleGraph.edgeSet hedg; rw [edgeRestriction_edgeSet] at hg
            rw [← hg]; simp [Set.mem_sdiff, e.property, coe_mem_openEdges_iff]
          let K' : RemovedConfiguration G (subgraphRemovedEdges (H.map emb) G) :=
            ⟨A ∩ actualMultiClusterReveal G S A, hrem ▸ Finset.inter_subset_right⟩
          have hPeq : P = (law G θ (BoundaryCondition.free ∅)).filter
              (frozenStateEvent (subgraphRemovedEdges (H.map emb) G) K')
              (frozenStateEvent_support θ (BoundaryCondition.free ∅) _ K') := by
            ext B; dsimp only [P]; unfold recordConditional
            rw [PMF.filter_apply, PMF.filter_apply]
            have hev : {B | clusterRecord G S B = clusterRecord G S A} = frozenStateEvent (subgraphRemovedEdges (H.map emb) G) K' := by
              ext C'; rw [Set.mem_ofPred_eq, clusterRecord_eq_iff_frozen]
              change C' ∩ actualMultiClusterReveal G S A = A ∩ actualMultiClusterReveal G S A ↔
                C' ∩ subgraphRemovedEdges (H.map emb) G = A ∩ actualMultiClusterReveal G S A
              rw [← hrem]
            rw [hev]
          have hmap : P.map res = law H θ (BoundaryCondition.free ∅) := by
            rw [hPeq, law_filter_frozen_map_embeddedRestriction H G emb hHG θ (BoundaryCondition.free ∅) K']
            apply law_eq_of_boundary_partition_eq
            apply Setoid.ext; intro a b
            change (componentSetoid G (BoundaryCondition.free ∅) (A ∩ actualMultiClusterReveal G S A)).r a.val b.val ↔ a = b
            rw [componentSetoid_free]
            change (openGraph G (A ∩ actualMultiClusterReveal G S A)).Reachable a.val b.val ↔ a = b
            refine ⟨fun ⟨p⟩ => ?_, fun h => h ▸ SimpleGraph.Reachable.refl _⟩
            by_cases hp : p.Nil
            · exact Subtype.ext hp.eq
            · have hadj := p.adj_snd hp
              have hadjA := openGraph_mono (Finset.inter_subset_left (s₂ := actualMultiClusterReveal G S A)) hadj
              obtain ⟨e, he, hep⟩ := (openGraph_adj G _ a.val _).mp hadj
              obtain ⟨_, ⟨z, hze, s, hs, hsz⟩⟩ := Finset.mem_filter.mp (Finset.mem_inter.mp he).2
              rw [hep] at hze
              rcases Sym2.mem_iff'.mp hze with rfl | rfl
              · exact (a.2 ⟨s, hs, hsz⟩).elim
              · exact (a.2 ⟨s, hs, hsz.trans hadjA.symm.reachable⟩).elim
          have hstep : expectation P ((nextDistinctConnection G x y r).indicator fun _ => (1 : ℝ)) ≤
              expectation P (fun B => (connectivityEvent H u v).indicator (fun _ => (1 : ℝ)) (res B)) :=
            expectation_le_on_support P _ _ fun B hB => by
              by_cases hn : B ∈ nextDistinctConnection G x y r
              · have hcl : ∀ a ∈ T, ∀ b, (openGraph G B).Adj a b → b ∈ T := fun a ha b hab hb => by
                  have hbB : ¬ b ∈ actualMultiClusterComplementSet G S B := fun hnB => ((hout B hB b).mp hnB) hb
                  obtain ⟨s, hs, hconn⟩ := Classical.not_not.1 hbB
                  exact ((hout B hB a).2 ha) ⟨s, hs, hconn.trans hab.symm.reachable⟩
                have hcH : res B ∈ connectivityEvent H u v := (actualConnected_inducedRestriction G T B hcl u v).2 hn.1
                simp [Set.indicator_of_mem hn, Set.indicator_of_mem hcH]
              · simp only [Set.indicator_of_notMem hn]
                by_cases hh : res B ∈ connectivityEvent H u v <;> simp [hh]
          refine hstep.trans ?_
          rw [← expectation_map, hmap, ← fk_measureReal_eq_expectation]
          exact hcomp r hr A hA hx hy
        · have hz : expectation P ((nextDistinctConnection G x y r).indicator fun _ => (1 : ℝ)) = 0 := by
            rw [← expectation_const P 0]
            exact expectation_congr_on_support P _ _ fun B hB =>
              Set.indicator_of_notMem (fun hh => hy ((hout B hB (y r)).1 (hnext_out hh).2)) _
          exact hz ▸ hc0
      · have hz : expectation P ((nextDistinctConnection G x y r).indicator fun _ => (1 : ℝ)) = 0 := by
          rw [← expectation_const P 0]
          exact expectation_congr_on_support P _ _ fun B hB =>
            Set.indicator_of_notMem (fun hh => hx ((hout B hB (x r)).1 (hnext_out hh).1)) _
        exact hz ▸ hc0
    rw [hsucc]
    exact (record_step_le _ hsupp _ _ _ hmeas c hcond).trans
      ((mul_le_mul_of_nonneg_left ih hc0).trans_eq (by rw [mul_comm, ← pow_succ, show r - 1 + 1 = r + 1 - 1 by omega]))

end FiniteGraph

/-! ### 3. Planar Unrolling Free-Limit and Reflection Comparison -/

section PlanarComparison
variable {V : Type*} [Finite V]
local instance {G : SimpleGraph V} : Fintype G.edgeSet := Fintype.ofFinite _

private theorem finiteFree_connectivity_sq_le_diagonal (G : SimpleGraph V) (θ : Parameters)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (f : V ↪ RotatedVertex) (hG : G.map f ≤ rotatedLattice)
    (u v : V) (k : ℕ) (hk : (f v).val.2 - (f u).val.2 = (k : ℤ)) :
    (measure G θ (BoundaryCondition.free ∅) (connectivityEvent G u v)).toReal ^ 2 ≤
      μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite (2 * k))) := by
  let g : V ↪ LatticeVertex := f.trans rotatedVertexEquiv.toEmbedding
  have hg : G.map g ≤ squareLattice := fun a b hab => by
    obtain ⟨c, d, hcd, rfl, rfl⟩ := (SimpleGraph.map_adj _ _ _ _).1 hab
    exact (rotatedLattice_adj_iff_square (f c) (f d)).1 (hG ((SimpleGraph.map_adj _ _ _ _).2 ⟨c, d, hcd, rfl, rfl⟩))
  let E := connectivityEvent G u v
  let cyl : Set LatticeConfiguration :=
    ⋃ A ∈ Finset.univ.filter (fun A : Configuration G => A ∈ E),
      LatticeConfiguration.allOpen (A.map (embeddedEdgeEmbedding G squareLattice g hg))
  have hclopen : IsClopen cyl := isClopen_biUnion_finset fun _ _ => LatticeConfiguration.allOpen_isClopen _
  have hconn_le : (measure G θ (BoundaryCondition.free ∅) E).toReal ≤ μ.real (CorrLength.connectionEvent (g u) (g v)) := by
    let : Fintype V := Fintype.ofFinite _
    choose R0 hR0 using fun w : V => origin_latticeBox_exhaustive (g w)
    let R := Finset.univ.sup R0
    have hR (w : V) : g w ∈ latticeBox (0, 0) R := latticeBox_mono (0, 0) (Finset.le_sup (f := R0) (Finset.mem_univ w)) (hR0 w)
    let ν := Classical.choose (freeBoxLimit_existsUnique θ)
    have hν := (Classical.choose_spec (freeBoxLimit_existsUnique θ)).1
      (fun _ => (0, 0)) (fun n => n) origin_latticeBox_nested origin_latticeBox_exhaustive
    have htr := (NNReal.continuous_coe.continuousAt.tendsto).comp
      (ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hν hclopen)
    have hbox_le : (measure G θ (BoundaryCondition.free ∅) E).toReal ≤ μ.real cyl := by
      rw [Duality.free_limit_eq_selected θ μ hμ]
      change (measure G θ (BoundaryCondition.free ∅) E).toReal ≤ ((ν cyl : NNReal) : ℝ)
      refine ge_of_tendsto htr ?_
      filter_upwards [eventually_ge_atTop R] with n hn
      have hbn (w : V) : g w ∈ latticeBox (0, 0) n := latticeBox_mono (0, 0) hn (hR w)
      let embBox : V ↪ BoxVertex (0, 0) n := ⟨fun w => ⟨g w, hbn w⟩, fun _ _ hw => g.injective (congrArg Subtype.val hw)⟩
      have hGbox : G.map embBox ≤ boxGraph (0, 0) n := fun a b hab => by
        obtain ⟨x, y, hxy, rfl, rfl⟩ := (SimpleGraph.map_adj _ _ _ _).1 hab
        exact hg ((SimpleGraph.map_adj _ _ _ _).2 ⟨x, y, hxy, rfl, rfl⟩)
      let I := E.indicator (fun _ => (1 : ℝ))
      have hI0 (A) : 0 ≤ I A := by by_cases ha : A ∈ E <;> simp [I, ha]
      have hImono : Monotone I := fun A B hAB => by
        by_cases ha : A ∈ E
        · have hb : B ∈ E := actualConnected_mono hAB ha
          simp [I, ha, hb]
        · simpa [I, ha] using hI0 B
      have hc := embedded_free_expectation_le G (boxGraph (0, 0) n) embBox hGbox θ ∅ ∅ I hI0 hImono
      simp only [Function.comp_apply]
      rw [fk_measureReal_eq_expectation]
      refine hc.trans ?_
      have hm := expectation_mono (law (boxGraph (0, 0) n) θ (BoundaryCondition.free ∅))
        (fun A => I (embeddedConfigurationRestriction G (boxGraph (0, 0) n) embBox hGbox A))
        (fun A => cyl.indicator (fun _ => (1 : ℝ)) (boxConfiguration (0, 0) n A)) fun A => by
          by_cases ha : embeddedConfigurationRestriction G (boxGraph (0, 0) n) embBox hGbox A ∈ E
          · have hmem : boxConfiguration (0, 0) n A ∈ cyl := by
              simp only [cyl, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
              refine ⟨_, ha, fun e he => ?_⟩
              obtain ⟨d, hd, rfl⟩ := Finset.mem_map.1 he
              have hcomm : boxEdgeEmbedding (0, 0) n (embeddedEdgeEmbedding G (boxGraph (0, 0) n) embBox hGbox d) =
                  embeddedEdgeEmbedding G squareLattice g hg d := by
                apply Subtype.ext; change Sym2.map Subtype.val (Sym2.map embBox d.val) = Sym2.map g d.val
                rw [Sym2.map_map]; rfl
              rw [← hcomm, boxConfiguration_at]
              exact decide_eq_true ((mem_embeddedConfigurationRestriction _ _ _ _ _ _).1 hd)
            simp [I, ha, hmem]
          · simp only [I, Set.indicator_of_notMem ha]
            by_cases hb : boxConfiguration (0, 0) n A ∈ cyl <;> simp [hb]
      refine hm.trans_eq ?_
      have hb : (boxProbabilityMeasure θ (0, 0) n : Measure LatticeConfiguration) cyl =
          measure (boxGraph (0, 0) n) θ (BoundaryCondition.free ∅) ((boxConfiguration (0, 0) n) ⁻¹' cyl) := by
        change ((law (boxGraph (0, 0) n) θ (BoundaryCondition.free ∅)).map _).toMeasure _ = _
        rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top hclopen.isOpen.measurableSet]; rfl
      rw [← ProbabilityMeasure.measureReal_eq_coe_coeFn, Measure.real_def, hb, fk_measureReal_eq_expectation]; rfl
    have := hμ.1
    have hcorr_eq (a b : LatticeVertex) : CorrLength.connectionEvent a b = Duality.connectionEvent a b :=
      Set.ext fun ω => CorrLength.connectionEvent_iff_rcInfiniteReachable a b ω
    refine hbox_le.trans ?_; rw [hcorr_eq]
    refine measureReal_mono fun ω hω => ?_
    simp only [cyl, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hω
    obtain ⟨A, hA, hopen⟩ := hω
    refine (Duality.mem_connectionEvent_iff_finite_witness ω (g u) (g v)).2
      ⟨A.map (embeddedEdgeEmbedding G squareLattice g hg), ?_, hopen⟩
    have hh := (actualConnected_isolatedExtension G g A u v).2 hA
    unfold ActualConnected at hh
    rw [← openGraph_subgraphConfigurationEmbedding hg] at hh
    change ActualConnected squareLattice (embeddedConfigurationEmbedding G squareLattice g hg A) _ _ at hh
    rwa [embeddedConfigurationEmbedding_eq_map] at hh
  let x : LatticeVertex := g v - g u
  have ht := isRCInfiniteVolumeLimit_connection_translation_invariant θ.toP θ.toQ θ.property μ hμ (-(g u)) (g u) (g v)
  rw [show latticeTranslate (-(g u)) (g u) = (0, 0) by ext <;> simp [latticeTranslate],
    show latticeTranslate (-(g u)) (g v) = x by ext <;> simp [x, latticeTranslate, sub_eq_add_neg]] at ht
  rw [← ht] at hconn_le
  have hcorr_eq (a b : LatticeVertex) : CorrLength.connectionEvent a b = Duality.connectionEvent a b :=
    Set.ext fun ω => CorrLength.connectionEvent_iff_rcInfiniteReachable a b ω
  have hrefl : μ.real (CorrLength.connectionEvent (0, 0) x) ^ 2 ≤
      μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite (2 * k))) := by
    have hswap : Duality.twoPoint μ (x.2, x.1) = Duality.twoPoint μ x := by
      have hq := Duality.twoPoint_quarterTurn θ μ hμ (x.1, -x.2)
      simp only [neg_neg] at hq; exact hq.trans (Duality.twoPoint_flipY θ μ hμ x)
    have hmul := Duality.twoPoint_mul_le θ μ hμ x (x.2, x.1)
    rw [hswap, ← pow_two, show x + (x.2, x.1) = (x.1 + x.2, x.1 + x.2) by ext <;> simp [add_comm]] at hmul
    have hu_sum : (rotatedVertexEquiv (f u)).1 + (rotatedVertexEquiv (f u)).2 = (f u).val.2 :=
      congrArg (fun w : RotatedVertex => w.val.2) (squareToRotated_rotatedToSquare (f u))
    have hv_sum : (rotatedVertexEquiv (f v)).1 + (rotatedVertexEquiv (f v)).2 = (f v).val.2 :=
      congrArg (fun w : RotatedVertex => w.val.2) (squareToRotated_rotatedToSquare (f v))
    have hxsum : x.1 + x.2 = (k : ℤ) := by
      change ((rotatedVertexEquiv (f v)).1 - (rotatedVertexEquiv (f u)).1) +
        ((rotatedVertexEquiv (f v)).2 - (rotatedVertexEquiv (f u)).2) = _
      omega
    rw [CorrLength.diagonalSite_even, ← hxsum]
    change μ.real (Duality.connectionEvent (0, 0) x) ^ 2 ≤
      μ.real (Duality.connectionEvent (0, 0) (x.1 + x.2, x.1 + x.2)) at hmul
    simpa only [hcorr_eq] using hmul
  exact (pow_le_pow_left₀ ENNReal.toReal_nonneg hconn_le 2).trans hrefl

end PlanarComparison

/-! ### 4. Cylinder Topology, Seam Closure, Intersection Zero, and Planar Lift -/

section TorusCylinder
variable {N M : ℕ}

private inductive IndexedWalk (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    FaceVertex N M true → FaceVertex N M true → Type
  | nil (u) : IndexedWalk hN hM A u u
  | forward (e : OpenDiamondEdge A) {v}
      (p : IndexedWalk hN hM A (faceEndpoint hN hM true e.val true) v) :
      IndexedWalk hN hM A (faceEndpoint hN hM true e.val false) v
  | backward (e : OpenDiamondEdge A) {v}
      (p : IndexedWalk hN hM A (faceEndpoint hN hM true e.val false) v) :
      IndexedWalk hN hM A (faceEndpoint hN hM true e.val true) v

private def IndexedWalk.chain {hN : Even N} {hM : Even M} {A : RCConfig N M} :
    {u v : FaceVertex N M true} → IndexedWalk hN hM A u v → OpenDiamondEdge A → ℚ
  | _, _, .nil _ => 0
  | _, _, .forward e p => Pi.single e 1 + p.chain
  | _, _, .backward e p => -Pi.single e 1 + p.chain

private def IndexedWalk.winding {hN : Even N} {hM : Even M} {A : RCConfig N M} :
    {u v : FaceVertex N M true} → IndexedWalk hN hM A u v → ℤ
  | _, _, .nil _ => 0
  | _, _, .forward e p => (if e.val.2.val = 0 then -1 else 0) + p.winding
  | _, _, .backward e p => -(if e.val.2.val = 0 then -1 else 0) + p.winding

private lemma IndexedWalk.chain_integral {hN : Even N} {hM : Even M} {A : RCConfig N M}
    {u v : FaceVertex N M true} (p : IndexedWalk hN hM A u v) (e : OpenDiamondEdge A) :
    ∃ z : ℤ, p.chain e = z := by
  induction p with
  | nil => exact ⟨0, rfl⟩
  | forward d p ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨(if e = d then 1 else 0) + z, ?_⟩
    simp only [IndexedWalk.chain, Pi.add_apply, Pi.single_apply, hz]; split_ifs <;> push_cast <;> rfl
  | backward d p ih =>
    obtain ⟨z, hz⟩ := ih
    refine ⟨-(if e = d then 1 else 0) + z, ?_⟩
    simp only [IndexedWalk.chain, Pi.add_apply, Pi.neg_apply, Pi.single_apply, hz]; split_ifs <;> push_cast <;> rfl

private lemma IndexedWalk.boundary_chain {hN : Even N} {hM : Even M} {A : RCConfig N M}
    {u v : FaceVertex N M true} (p : IndexedWalk hN hM A u v) :
    diamondBoundary hN hM A p.chain = Pi.single v 1 - Pi.single u 1 := by
  induction p with
  | nil => simp [IndexedWalk.chain]
  | forward e p ih =>
    rw [IndexedWalk.chain, map_add, diamondBoundary_single, ih]; ext w
    simp only [Pi.add_apply, Pi.sub_apply]; ring
  | backward e p ih =>
    rw [IndexedWalk.chain, map_add, map_neg, diamondBoundary_single, ih]; ext w
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]; ring

private lemma IndexedWalk.winding_chain {hN : Even N} {hM : Even M} {A : RCConfig N M}
    {u v : FaceVertex N M true} (p : IndexedWalk hN hM A u v) :
    diamondWindingY A p.chain = (p.winding : ℚ) := by
  induction p with
  | nil => simp [IndexedWalk.chain, IndexedWalk.winding, diamondWindingY]
  | forward e p ih =>
    change (∑ d, diamondSeamCrossY d.val * ((Pi.single e (1 : ℚ) : OpenDiamondEdge A → ℚ) d + p.chain d)) = _
    simp_rw [mul_add]; rw [Finset.sum_add_distrib]
    change (∑ d, diamondSeamCrossY d.val * (Pi.single e (1 : ℚ) : OpenDiamondEdge A → ℚ) d) + diamondWindingY A p.chain = _
    rw [ih]; simp [Pi.single_apply, mul_ite, diamondSeamCrossY, IndexedWalk.winding]
  | backward e p ih =>
    change (∑ d, diamondSeamCrossY d.val * (-((Pi.single e (1 : ℚ) : OpenDiamondEdge A → ℚ) d) + p.chain d)) = _
    simp_rw [mul_add, mul_neg]; rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
    change -(∑ d, diamondSeamCrossY d.val * (Pi.single e (1 : ℚ) : OpenDiamondEdge A → ℚ) d) + diamondWindingY A p.chain = _
    rw [ih]; simp [Pi.single_apply, mul_ite, diamondSeamCrossY, IndexedWalk.winding]

private lemma IndexedWalk.chain_supported {hN : Even N} {hM : Even M} {A : RCConfig N M}
    {u v : FaceVertex N M true} (p : IndexedWalk hN hM A u v) (e : OpenDiamondEdge A)
    (he : diamondEdgeCluster hN hM A e ≠ (diamondOpenGraph hN hM true A).connectedComponentMk u) :
    p.chain e = 0 := by
  induction p with
  | nil => rfl
  | @forward d _ p ih =>
    have hcomp := SimpleGraph.ConnectedComponent.sound (diamond_endpoints_reachable hN hM A d.val d.property)
    have hed : e ≠ d := fun h => he (h ▸ rfl)
    simp only [IndexedWalk.chain, Pi.add_apply, Pi.single_apply, hed, ite_false, zero_add, ih (by rwa [← hcomp])]
  | @backward d _ p ih =>
    have hcomp := SimpleGraph.ConnectedComponent.sound (diamond_endpoints_reachable hN hM A d.val d.property)
    have hed : e ≠ d := fun h => he (h ▸ hcomp)
    simp only [IndexedWalk.chain, Pi.add_apply, Pi.neg_apply, Pi.single_apply, hed, ite_false, neg_zero, zero_add, ih (by rwa [hcomp])]

private lemma exists_indexedWalk_of_reachable (hN : Even N) (hM : Even M) (A : RCConfig N M)
    {u v : FaceVertex N M true} (h : (diamondOpenGraph hN hM true A).Reachable u v) :
    Nonempty (IndexedWalk hN hM A u v) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact ⟨.nil _⟩
  | @cons u v w hadj p ih =>
    obtain ⟨p'⟩ := ih
    rw [diamondOpenGraph, SimpleGraph.fromEdgeSet_adj] at hadj
    obtain ⟨⟨e, he, hep⟩, _⟩ := hadj
    rcases Sym2.eq_iff.1 hep with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨.forward ⟨e, he⟩ p'⟩
    · exact ⟨.backward ⟨e, he⟩ p'⟩

private def seamOnlyConfig (N M : ℕ) : RCConfig N M := fun e => decide (e.2.val = 0)

private def seamCycleVertex (hN : Even N) (hM : Even M) (hMp : 0 < M) (i : Fin N) : FaceVertex N M true :=
  if checker (i, (⟨0, hMp⟩ : Fin M)) then faceEndpoint hN hM true (i, ⟨0, hMp⟩) false
  else faceEndpoint hN hM true (i, ⟨0, hMp⟩) true

private theorem top_bottom_seam_reachable (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMp : 0 < M) (u v : FaceVertex N M true)
    (hu : u.val.2.val = 0) (hv : v.val.2.val + 1 = M) :
    (diamondOpenGraph hN hM true (seamOnlyConfig N M)).Reachable v u := by
  have hprv (N' : ℕ) (hN' : Even N') (i : Fin N') :
      (diamondOpenGraph hN' hM true (seamOnlyConfig N' M)).Reachable
        (seamCycleVertex hN' hM hMp i) (seamCycleVertex hN' hM hMp (prv i)) := by
    have hh := diamond_endpoints_reachable hN' hM (seamOnlyConfig N' M) (i, ⟨0, hMp⟩) (by simp [seamOnlyConfig])
    have hpc := checker_prv_x hN' i (⟨0, hMp⟩ : Fin M)
    cases hc : checker (i, (⟨0, hMp⟩ : Fin M))
    · have hp : checker (prv i, (⟨0, hMp⟩ : Fin M)) = true := by simpa [hc] using hpc
      simpa only [seamCycleVertex, hc, hp, faceEndpoint, faceEndpointRaw, Bool.false_eq_true, ite_true, ite_false] using hh.symm
    · have hp : checker (prv i, (⟨0, hMp⟩ : Fin M)) = false := by simpa [hc] using hpc
      simpa only [seamCycleVertex, hc, hp, faceEndpoint, faceEndpointRaw, Bool.false_eq_true, ite_true, ite_false] using hh
  have hreach : (diamondOpenGraph hN hM true (seamOnlyConfig N M)).Reachable
      (seamCycleVertex hN hM hMp v.val.1) (seamCycleVertex hN hM hMp u.val.1) := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hNp.ne'
    have hroot (i : Fin (n + 1)) :
        (diamondOpenGraph hN hM true (seamOnlyConfig (n + 1) M)).Reachable
          (seamCycleVertex hN hM hMp i) (seamCycleVertex hN hM hMp 0) := by
      induction i using Fin.induction with
      | zero => exact SimpleGraph.Reachable.refl _
      | succ i ih =>
        have hp : prv i.succ = i.castSucc := Fin.ext (by rw [prv_val_of_pos i.succ (by simp)]; simp)
        exact (hp ▸ hprv (n + 1) hN i.succ).trans ih
    exact (hroot v.val.1).trans (hroot u.val.1).symm
  have hbot : seamCycleVertex hN hM hMp u.val.1 = u := by
    have hy : u.val.2 = (⟨0, hMp⟩ : Fin M) := Fin.ext hu
    have hc : checker (u.val.1, (⟨0, hMp⟩ : Fin M)) = true := by simpa [← hy] using u.property
    apply Subtype.ext
    simp only [seamCycleVertex, hc, ite_true, faceEndpoint, faceEndpointRaw, Subtype.coe_mk]
    exact Prod.ext rfl hy.symm
  have htop : seamCycleVertex hN hM hMp v.val.1 = v := by
    have hy : v.val.2 = prv (⟨0, hMp⟩ : Fin M) := Fin.ext (by have := prv_val_zero (⟨0, hMp⟩ : Fin M) rfl; omega)
    have hp := checker_prv_y hM v.val.1 (⟨0, hMp⟩ : Fin M)
    have ht : checker (v.val.1, prv (⟨0, hMp⟩ : Fin M)) = true := by simpa [← hy] using v.property
    have hc : checker (v.val.1, (⟨0, hMp⟩ : Fin M)) = false := by
      rw [ht] at hp; cases h : checker (v.val.1, (⟨0, hMp⟩ : Fin M)) <;> simp_all
    apply Subtype.ext
    simp only [seamCycleVertex, hc, ite_true, faceEndpoint, faceEndpointRaw]
    exact Prod.ext rfl hy.symm
  rwa [hbot, htop] at hreach

private def closedWalkPair (hN : Even N) (hM : Even M) {A B : RCConfig N M} {u v : FaceVertex N M true}
    (p : IndexedWalk hN hM A u v) (s : IndexedWalk hN hM B v u) :
    diamondCycleSpace hN hM (openRCConfig N M) :=
  ⟨fullDiamondChainExtension A p.chain + fullDiamondChainExtension B s.chain, by
    have hb_ext (C : RCConfig N M) (f : OpenDiamondEdge C → ℚ) :
        diamondBoundary hN hM (openRCConfig N M) (fullDiamondChainExtension C f) = diamondBoundary hN hM C f := by
      funext w
      have h := sum_ribbonHalfFlow_corners_eq_neg_boundary hN hM (openRCConfig N M) (fullDiamondChainExtension C f) w
      simp_rw [ribbonHalfFlow_fullExtension] at h
      rw [sum_ribbonHalfFlow_corners_eq_neg_boundary] at h
      exact neg_injective h.symm
    change diamondBoundary hN hM (openRCConfig N M) _ = 0
    rw [map_add, hb_ext, hb_ext, IndexedWalk.boundary_chain, IndexedWalk.boundary_chain]
    ext w; simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply]; ring⟩

private def fullFlowAt (f : OpenDiamondEdge (openRCConfig N M) → ℚ) (v : Fin N × Fin M) : ℚ := f ⟨v, rfl⟩

private def bottomSeamPotential (f : OpenDiamondEdge (openRCConfig N M) → ℚ) (v : FaceVertex N M true) : ℚ :=
  if v.val.2.val = 0 then fullFlowAt f v.val else 0

private theorem cylinder_exterior_intersection_zero (hN : Even N) (hM : Even M)
    (f g : diamondCycleSpace hN hM (openRCConfig N M))
    (hg : ∀ e : OpenDiamondEdge (openRCConfig N M), g.val e ≠ 0 →
      e.val.2.val ≠ 0 ∧ ∀ b : Bool, ∀ p : Port,
        (faceCorner (faceEndpoint hN hM true e.val b).val p).1.2.val ≠ 0 →
        fullFlowAt f.val (faceCorner (faceEndpoint hN hM true e.val b).val p).1 = 0) :
    ribbonIntersection hN hM (openRCConfig N M) f g = 0 := by
  have hhalf (v : FaceVertex N M true) (p : Port) :
      ribbonHalfFlow hN hM (openRCConfig N M) f.val (ribbonCornerEquiv hN hM (v, p)) =
        match p with
        | .east => fullFlowAt f.val v.val
        | .north => fullFlowAt f.val (nxt v.val.1, v.val.2)
        | .west => -fullFlowAt f.val (nxt v.val.1, nxt v.val.2)
        | .south => -fullFlowAt f.val (v.val.1, nxt v.val.2) := by
    cases p <;> simp only [ribbonHalfFlow_raw, ribbonCornerEquiv_val, faceCorner,
      ribbonEndSide, extendDiamondChain, openRCConfig, fullFlowAt, Bool.false_eq_true, ite_true, ite_false] <;> rfl
  have hprim (d : DirectedDart (checkerArrows N M)) :
      ribbonCornerPrimitive hN hM (openRCConfig N M) f d =
        match d.val.2 with
        | .east => 0
        | .north => -fullFlowAt f.val (nxt (leftFace d.val).1, (leftFace d.val).2)
        | .west => -fullFlowAt f.val (nxt (leftFace d.val).1, (leftFace d.val).2) +
            fullFlowAt f.val (nxt (leftFace d.val).1, nxt (leftFace d.val).2)
        | .south => fullFlowAt f.val (leftFace d.val) := by
    obtain ⟨⟨v, p⟩, rfl⟩ := (ribbonCornerEquiv hN hM).surjective d
    rw [ribbonCornerPrimitive_corner]; simp_rw [hhalf]
    cases p <;> simp only [cornerPrimitiveValue, ribbonCornerEquiv_val, faceCorner, leftFace,
      nxt, prv, Equiv.symm_apply_apply, sub_neg_eq_add]
  have hbelow (e : OpenDiamondEdge (openRCConfig N M)) :
      ribbonIntersectionCoefficient hN hM (openRCConfig N M) f e =
        (if checker e.val then -1 else 1) * fullFlowAt f.val (e.val.1, prv e.val.2) := by
    unfold ribbonIntersectionCoefficient; rw [hprim, hprim]
    cases hc : checker e.val <;>
      simp only [ribbonEndEquiv_val, ribbonEnd, hc, Bool.false_eq_true, ite_false, ite_true,
        leftFace, fullFlowAt, nxt, prv, Equiv.apply_symm_apply, neg_one_mul, one_mul] <;> ring
  have heq : ribbonIntersection hN hM (openRCConfig N M) f g =
      ∑ e, diamondCoboundary hN hM (openRCConfig N M) (bottomSeamPotential f.val) e * g.val e :=
    Finset.sum_congr rfl fun e _ => by
      by_cases hz : g.val e = 0
      · simp [hz]
      · obtain ⟨he, hf⟩ := hg e hz
        congr 1
        have hyf : (faceEndpoint hN hM true e.val false).val.2.val ≠ 0 := by
          cases hc : checker e.val <;>
            simpa only [faceEndpoint, faceEndpointRaw, hc, Bool.false_eq_true, ite_true, ite_false] using he
        have hyt : nxt (faceEndpoint hN hM true e.val true).val.2 = e.val.2 := by
          cases hc : checker e.val <;>
            simp only [faceEndpoint, faceEndpointRaw, hc, Bool.false_eq_true, ite_true, ite_false, nxt, prv, Equiv.apply_symm_apply]
        let vt := faceEndpoint hN hM true e.val true
        have hx : fullFlowAt f.val vt.val = bottomSeamPotential f.val vt := by
          by_cases hy : vt.val.2.val = 0
          · simp [bottomSeamPotential, hy]
          · simpa [bottomSeamPotential, hy, faceCorner] using hf true .east hy
        have hn : -fullFlowAt f.val (nxt vt.val.1, vt.val.2) = bottomSeamPotential f.val vt := by
          by_cases hy : vt.val.2.val = 0
          · have hnxt : (nxt vt.val.2).val ≠ 0 := by dsimp only [vt]; rwa [hyt]
            have hw : fullFlowAt f.val (nxt vt.val.1, nxt vt.val.2) = 0 := hf true .west hnxt
            have hs : fullFlowAt f.val (vt.val.1, nxt vt.val.2) = 0 := hf true .south hnxt
            have hc := sum_ribbonHalfFlow_corners hN hM (openRCConfig N M) f vt
            rw [sum_port] at hc; simp only [hhalf] at hc; rw [hw, hs] at hc
            simp only [bottomSeamPotential, hy, ite_true]; linarith
          · have hh := hf true .north (by simpa [faceCorner] using hy)
            change fullFlowAt f.val (nxt vt.val.1, vt.val.2) = 0 at hh
            simp only [bottomSeamPotential, hy, ite_false, hh, neg_zero]
        rw [hbelow, diamondCoboundary_apply]
        simp only [bottomSeamPotential, hyf, ite_false, sub_zero]
        cases hc : checker e.val
        · simpa only [bottomSeamPotential, hc, ite_false, one_mul, vt, faceEndpoint, faceEndpointRaw,
            Bool.false_eq_true, ite_true, ite_false] using hx
        · simpa only [bottomSeamPotential, hc, ite_true, neg_one_mul, vt, faceEndpoint, faceEndpointRaw,
            Bool.false_eq_true, ite_true, ite_false, nxt, prv, Equiv.apply_symm_apply] using hn
  rw [heq]
  have hp := diamondBoundary_pairing hN hM (openRCConfig N M) (bottomSeamPotential f.val) g.val
  rw [g.property] at hp
  simpa only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] using hp.symm

private def integerSeamCrossX (e : Fin N × Fin M) : ℤ :=
  if e.1.val = 0 then (if checker e then -1 else 1) else 0

private def unexploredCylinderConfig (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (u : FaceVertex N M true) : RCConfig N M := fun e =>
  decide (e.2.val ≠ 0 ∧ ∀ b : Bool,
    (diamondOpenGraph hN hM true (TorusRC.torusRCSeamClosed A)).connectedComponentMk (faceEndpoint hN hM true e b) ≠
      (diamondOpenGraph hN hM true (TorusRC.torusRCSeamClosed A)).connectedComponentMk u)

private def potentialLift (hN : Even N) (F : FaceVertex N M true → ℤ) (v : FaceVertex N M true) : RotatedVertex :=
  ⟨((v.val.1.val : ℤ) + (N : ℤ) * F v, v.val.2.val), by
    have hv : Even ((v.val.1.val : ℤ) + (v.val.2.val : ℤ)) := by
      exact_mod_cast Nat.even_iff.mpr (by simpa only [checker, decide_eq_true_eq] using v.property)
    have hN' : Even (N : ℤ) := by exact_mod_cast hN
    convert hv.add (hN'.mul_right (F v)) using 1; ring⟩

private theorem exists_unexploredCylinder_embedding (hN : Even N) (hM : Even M)
    (hNp : 0 < N) (hMlarge : 1 < M) {A : RCConfig N M}
    {u v : FaceVertex N M true} (hu : u.val.2.val = 0) (hv : v.val.2.val + 1 = M)
    (hp : (diamondOpenGraph hN hM true (TorusRC.torusRCSeamClosed A)).Reachable u v) :
    ∃ f : FaceVertex N M true ↪ RotatedVertex,
      (∀ w, (f w).val.2 = (w.val.2.val : ℤ)) ∧
      ∀ a b, (diamondOpenGraph hN hM true (unexploredCylinderConfig hN hM A u)).Adj a b →
        rotatedLattice.Adj (f a) (f b) := by
  let D := unexploredCylinderConfig hN hM A u
  have hD (e : OpenDiamondEdge D) : e.val.2.val ≠ 0 ∧ ∀ b : Bool,
      (diamondOpenGraph hN hM true (TorusRC.torusRCSeamClosed A)).connectedComponentMk (faceEndpoint hN hM true e.val b) ≠
        (diamondOpenGraph hN hM true (TorusRC.torusRCSeamClosed A)).connectedComponentMk u := by
    simpa only [D, unexploredCylinderConfig, decide_eq_true_eq] using e.property
  have hwinding : ∀ g : diamondCycleSpace hN hM D, diamondWindingX D g.val = 0 := fun g => by
    obtain ⟨p⟩ := exists_indexedWalk_of_reachable hN hM (TorusRC.torusRCSeamClosed A) hp
    obtain ⟨s⟩ := exists_indexedWalk_of_reachable hN hM _ (top_bottom_seam_reachable hN hM hNp (by omega) u v hu hv)
    let f := closedWalkPair hN hM p s
    let G := fullDiamondCycleExtension hN hM D g
    have hi : ribbonIntersection hN hM (openRCConfig N M) f G = 0 := by
      refine cylinder_exterior_intersection_zero hN hM f G fun e he => ?_
      have hed : D e.val = true := by
        cases hd : D e.val with
        | true => rfl
        | false => exact False.elim (he (extendDiamondChain_closed D g.val e.val hd))
      refine ⟨(hD ⟨e.val, hed⟩).1, fun b c hc => ?_⟩
      let w := faceEndpoint hN hM true e.val b
      have hw := (hD ⟨e.val, hed⟩).2 b
      have hp0 : fullDiamondChainExtension _ p.chain ⟨(faceCorner w.val c).1, rfl⟩ = 0 := by
        change extendDiamondChain _ p.chain _ = 0
        cases hce : TorusRC.torusRCSeamClosed A (faceCorner w.val c).1 with
        | false => exact extendDiamondChain_closed _ _ _ hce
        | true =>
          rw [extendDiamondChain_open _ _ _ hce]
          refine p.chain_supported (e := ⟨(faceCorner w.val c).1, hce⟩) ?_
          let d := ribbonCornerEquiv hN hM (w, c)
          obtain ⟨⟨w', b'⟩, hd⟩ := (ribbonEndEquiv hN hM).surjective d
          have hw' : w' = (faceCorner w.val c).1 := by
            simpa only [d, ribbonEndEquiv_val, ribbonEnd, ribbonCornerEquiv_val] using
              congrArg (fun x : DirectedDart (checkerArrows N M) => x.val.1) hd
          subst w'
          have hh := ribbonCornerCluster_end hN hM _ ⟨(faceCorner w.val c).1, hce⟩ b'
          rw [hd] at hh
          rwa [hh.symm.trans (ribbonCornerCluster_corner hN hM _ w c)]
      have hs0 : seamOnlyConfig N M (faceCorner w.val c).1 = false := decide_eq_false hc
      change fullDiamondChainExtension _ p.chain _ + fullDiamondChainExtension _ s.chain _ = 0
      rw [hp0]; change 0 + extendDiamondChain (seamOnlyConfig N M) s.chain _ = 0
      rw [extendDiamondChain_closed _ _ _ hs0, add_zero]
    have hGy : diamondWindingY (openRCConfig N M) G.val = 0 := by
      rw [show G.val = fullDiamondChainExtension D g.val from rfl]
      unfold diamondWindingY; rw [sum_fullDiamondChainExtension]
      exact sum_eq_zero fun e _ => by simp [diamondSeamCrossY, (hD e).1]
    have hfy : diamondWindingY (openRCConfig N M) f.val = 1 := by
      have hpY : diamondWindingY (TorusRC.torusRCSeamClosed A) p.chain = 0 :=
        sum_eq_zero fun e _ => by
          have he : e.val.2.val ≠ 0 := fun h => by have := e.property; simp [TorusRC.torusRCSeamClosed, h] at this
          simp [diamondSeamCrossY, he]
      have hsY : diamondWindingY (seamOnlyConfig N M) s.chain = 1 := by
        have hb := diamondBoundary_pairing hN hM (seamOnlyConfig N M) (fun w => (w.val.2.val : ℚ)) s.chain
        rw [IndexedWalk.boundary_chain] at hb
        simp only [Pi.sub_apply, mul_sub, sum_sub_distrib, Pi.single_apply, mul_ite, mul_one,
          mul_zero, sum_ite_eq', mem_univ, ite_true] at hb
        have hsr (e : OpenDiamondEdge (seamOnlyConfig N M)) : e.val.2.val = 0 := by
          simpa only [seamOnlyConfig, decide_eq_true_eq] using e.property
        have hc (e : OpenDiamondEdge (seamOnlyConfig N M)) :
            diamondCoboundary hN hM (seamOnlyConfig N M) (fun w => (w.val.2.val : ℚ)) e = (M : ℚ) - 1 := by
          rw [diamondCoordinateY_coboundary]; simp only [diamondSeamCrossY, hsr, ite_true]; ring
        simp_rw [hc] at hb; rw [← mul_sum, hu, Nat.cast_zero] at hb
        have hyv : (v.val.2.val : ℚ) + 1 = M := by exact_mod_cast hv
        have hMu : (M : ℚ) - 1 ≠ 0 := by exact_mod_cast (show (M : ℤ) - 1 ≠ 0 by omega)
        have hsum : (∑ e, s.chain e) = -1 := mul_left_cancel₀ hMu (by linarith)
        unfold diamondWindingY; simp_rw [diamondSeamCrossY, hsr, ite_true, neg_one_mul]
        rw [sum_neg_distrib, hsum]; norm_num
      change (∑ e : OpenDiamondEdge (openRCConfig N M), diamondSeamCrossY e.val *
        (fullDiamondChainExtension _ p.chain e + fullDiamondChainExtension _ s.chain e)) = 1
      simp_rw [mul_add]; rw [sum_add_distrib]
      rw [sum_fullDiamondChainExtension, sum_fullDiamondChainExtension]
      change diamondWindingY _ p.chain + diamondWindingY _ s.chain = 1
      rw [hpY, hsY, zero_add]
    have hd := ribbonIntersection_mul_area hN hM hNp (by omega) f G
    rw [hi, ← diamondWindingX_mul_period hN hM _ f, ← diamondWindingY_mul_period hN hM _ G,
      ← diamondWindingY_mul_period hN hM _ f, ← diamondWindingX_mul_period hN hM _ G, hGy, hfy] at hd
    have hz : (M : ℚ) * (N : ℚ) * diamondWindingX (openRCConfig N M) G.val = 0 := by
      simpa only [mul_zero, zero_mul, mul_one, zero_sub, neg_eq_zero, mul_assoc] using hd.symm
    have hGx := (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by positivity) (by positivity))
    unfold diamondWindingX; rw [← sum_fullDiamondChainExtension D g.val diamondSeamCrossX]; exact hGx
  obtain ⟨Gpot, hGpot⟩ := exists_diamondPotential_of_cycle_annihilator hN hM D
    (fun e => diamondSeamCrossX e.val) hwinding
  let F : FaceVertex N M true → ℤ := fun w => ⌊Gpot w⌋
  have hcast (e : Fin N × Fin M) : (integerSeamCrossX e : ℚ) = diamondSeamCrossX e := by
    unfold integerSeamCrossX diamondSeamCrossX; split_ifs <;> norm_num
  have hF (e : OpenDiamondEdge D) :
      F (faceEndpoint hN hM true e.val true) - F (faceEndpoint hN hM true e.val false) = integerSeamCrossX e.val := by
    have he := congrFun hGpot e
    change Gpot (faceEndpoint hN hM true e.val true) - Gpot (faceEndpoint hN hM true e.val false) = diamondSeamCrossX e.val at he
    rw [← hcast] at he
    have he' : Gpot (faceEndpoint hN hM true e.val true) =
        Gpot (faceEndpoint hN hM true e.val false) + (integerSeamCrossX e.val : ℚ) := by linarith
    dsimp [F]; rw [he', Int.floor_add_intCast]; omega
  have hinj : Function.Injective (potentialLift hN F) := fun a b hab => by
    have hx := congrArg (fun w : RotatedVertex => w.val.1 % (N : ℤ)) hab
    have hy := congrArg (fun w : RotatedVertex => w.val.2) hab
    have hmod (w : FaceVertex N M true) : (potentialLift hN F w).val.1 % (N : ℤ) = w.val.1.val := by
      change ((w.val.1.val : ℤ) + (N : ℤ) * F w) % (N : ℤ) = _
      rw [Int.add_emod, Int.mul_emod]
      simp only [Int.emod_self, zero_mul, Int.zero_emod, add_zero, Int.emod_emod]
      exact Int.emod_eq_of_lt (by omega) (by exact_mod_cast w.val.1.isLt)
    rw [hmod, hmod] at hx
    exact Subtype.ext (Prod.ext (Fin.ext (by exact_mod_cast hx))
      (Fin.ext (by change (a.val.2.val : ℤ) = (b.val.2.val : ℤ) at hy; exact_mod_cast hy)))
  refine ⟨⟨potentialLift hN F, hinj⟩, fun _ => rfl, fun a b hab => ?_⟩
  rw [diamondOpenGraph, SimpleGraph.fromEdgeSet_adj] at hab
  obtain ⟨⟨e, he, hep⟩, _⟩ := hab
  let ed : OpenDiamondEdge D := ⟨e, he⟩
  have hse : ed.val.2.val ≠ 0 := (hD ed).1
  have hadj_t : rotatedLattice.Adj (potentialLift hN F (faceEndpoint hN hM true e true))
      (potentialLift hN F (faceEndpoint hN hM true e false)) := by
    have hex : (potentialLift hN F (faceEndpoint hN hM true e true)).val.1 -
        (potentialLift hN F (faceEndpoint hN hM true e false)).val.1 = if checker e then -1 else 1 := by
      have hf : (F (faceEndpoint hN hM true e true) : ℚ) - (F (faceEndpoint hN hM true e false) : ℚ) = diamondSeamCrossX e := by
        rw [← hcast]; exact_mod_cast hF ed
      have hx := diamondCoordinateX_coboundary hN hM D ed
      rw [diamondCoboundary_apply] at hx; dsimp only [ed] at hx
      apply Int.cast_injective (α := ℚ)
      dsimp only [potentialLift]
      simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_mul]
      cases hc : checker e <;> simp only [hc, Bool.false_eq_true, ite_true, ite_false, Int.cast_neg, Int.cast_one] at * <;>
        linear_combination hx + (N : ℚ) * hf
    have hey : (potentialLift hN F (faceEndpoint hN hM true e true)).val.2 -
        (potentialLift hN F (faceEndpoint hN hM true e false)).val.2 = -1 := by
      have hy := diamondCoordinateY_coboundary hN hM D ed
      simp only [diamondSeamCrossY, hse, ite_false, mul_zero, sub_zero, diamondCoboundary_apply] at hy
      change ((faceEndpoint hN hM true e true).val.2.val : ℤ) - ((faceEndpoint hN hM true e false).val.2.val : ℤ) = -1
      exact_mod_cast hy
    change |_ - _| = 1 ∧ |_ - _| = 1
    rw [hex, hey]; cases hc : checker e <;> norm_num [hc]
  rcases Sym2.eq_iff.1 hep with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hadj_t.symm
  · exact hadj_t

/-! ### 5. Cylinder Bridge, Seam-Law Bound, Union Bound, and Equation (3.16) -/

private def fullCylinderGraph (hN : Even N) (hM : Even M) : SimpleGraph (FaceVertex N M true) :=
  diamondOpenGraph hN hM true (TorusRC.torusRCSeamClosed (openRCConfig N M))

private lemma fullCylinderGraph_le_full (hN : Even N) (hM : Even M) :
    fullCylinderGraph hN hM ≤ fullDiamondGraph hN hM := fun u v huv => by
  rw [fullCylinderGraph, diamondOpenGraph, SimpleGraph.fromEdgeSet_adj] at huv
  obtain ⟨⟨e, _, he⟩, hne⟩ := huv
  rw [fullDiamondGraph, diamondOpenGraph, SimpleGraph.fromEdgeSet_adj]
  exact ⟨⟨e, rfl, he⟩, hne⟩

private lemma indexedEdge_mem_cylinder_iff (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (e : Fin N × Fin M) :
    (torusIndexedEdgeEmbedding hN hM hN4 hM4 e).val ∈ (fullCylinderGraph hN hM).edgeSet ↔ e.2.val ≠ 0 := by
  rw [fullCylinderGraph, diamondOpenGraph, SimpleGraph.edgeSet_fromEdgeSet]
  refine ⟨fun ⟨⟨d, hd, hpair⟩, _⟩ => ?_, fun he0 => ⟨⟨e, by simp [TorusRC.torusRCSeamClosed, he0, openRCConfig], rfl⟩,
    fun hd => ((fullDiamondGraph hN hM).mem_edgeSet.1 (torusIndexedEdgeEmbedding hN hM hN4 hM4 e).property).ne
      (Sym2.mk_isDiag_iff.1 (Sym2.mem_diagSet.1 hd))⟩⟩
  have heq : d = e := (torusIndexedEdgeEmbedding hN hM hN4 hM4).injective (Subtype.ext hpair.symm)
  subst d; exact fun he0 => by simp [TorusRC.torusRCSeamClosed, he0] at hd

private def cylinderIndexedConfiguration (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (C : Configuration (fullCylinderGraph hN hM)) : RCConfig N M :=
  (torusRCConfigurationEquiv hN hM hN4 hM4).symm
    (subgraphConfigurationEmbedding (fullCylinderGraph_le_full hN hM) C)

private lemma cylinderIndexedConfiguration_eq_seamClosed (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (C : Configuration (fullCylinderGraph hN hM)) :
    TorusRC.torusRCSeamClosed (cylinderIndexedConfiguration hN hM hN4 hM4 C) =
      cylinderIndexedConfiguration hN hM hN4 hM4 C := by
  funext e
  by_cases he : e.2.val = 0
  · have hfalse : cylinderIndexedConfiguration hN hM hN4 hM4 C e = false := by
      cases hc : cylinderIndexedConfiguration hN hM hN4 hM4 C e with
      | false => rfl
      | true =>
        have hm := (mem_torusRCConfigurationEquiv hN hM hN4 hM4 _ e).2 hc
        change torusIndexedEdgeEmbedding hN hM hN4 hM4 e ∈
          torusRCConfigurationEquiv hN hM hN4 hM4 ((torusRCConfigurationEquiv hN hM hN4 hM4).symm _) at hm
        rw [Equiv.apply_symm_apply] at hm
        obtain ⟨d, _, hd⟩ := Finset.mem_map.1 hm
        exact ((indexedEdge_mem_cylinder_iff hN hM hN4 hM4 e).1 (congrArg Subtype.val hd ▸ d.property) he).elim
    simp [TorusRC.torusRCSeamClosed, he, hfalse]
  · simp [TorusRC.torusRCSeamClosed, he]

private lemma openGraph_cylinderIndexedConfiguration (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (C : Configuration (fullCylinderGraph hN hM)) :
    openGraph (fullCylinderGraph hN hM) C =
      diamondOpenGraph hN hM true (TorusRC.torusRCSeamClosed (cylinderIndexedConfiguration hN hM hN4 hM4 C)) := by
  rw [cylinderIndexedConfiguration_eq_seamClosed, ← openGraph_simpleConfiguration,
    simpleConfiguration_eq_torusRCConfigurationEquiv hN hM hN4 hM4]
  unfold cylinderIndexedConfiguration
  rw [Equiv.apply_symm_apply, openGraph_subgraphConfigurationEmbedding]

private def torusRCSeamRowClosed (hM : 0 < M) : Set (RCConfig N M) :=
  {A | ∀ i : Fin N, A (i, (⟨0, hM⟩ : Fin M)) = false}

private def torusRCSeamClosedCrossingEvent (hN : Even N) (hM : Even M) (r : ℕ) : Set (RCConfig N M) :=
  {A | torusRCSeamClosedCylinderCrossings hN hM r (torusRCSeamClosed A)}

private theorem seamClosedCylinderCrossings_of_le_U
    (hN : Even N) (hM : Even M) (hMp : 0 < M) (r : ℕ) (A : RCConfig N M)
    (hr : r ≤ rcVerticalWinding hN hM ⟨0, hMp⟩ A) :
    torusRCSeamClosedCylinderCrossings hN hM r (torusRCSeamClosed A) := by
  let reachesTop (u : FaceVertex N M true) : Prop :=
    ∃ v, v.val.2.val + 1 = M ∧ (diamondOpenGraph hN hM true (torusRCSeamClosed A)).Reachable u v
  have hsubG : diamondOpenGraph hN hM true (torusRCSeamClosed A) ≤ diamondOpenGraph hN hM true A := fun u v huv => by
    rw [diamondOpenGraph, SimpleGraph.fromEdgeSet_adj] at huv ⊢
    obtain ⟨⟨e, he, hep⟩, hne⟩ := huv
    have hy : e.2.val ≠ 0 := fun h => by simp [torusRCSeamClosed, h] at he
    exact ⟨⟨e, by simpa only [torusRCSeamClosed, hy, ite_false] using he, hep⟩, hne⟩
  let P := TorusTopology.positiveVerticalLoops hN hM ⟨0, hMp⟩ A
  have hex (q : P) :
      let b := (loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) ⟨0, hMp⟩ q.val).toNat
      ∃ x : Fin b → FaceVertex N M true,
        (∀ i, (x i).val.2.val = 0 ∧
          (diamondOpenGraph hN hM true A).connectedComponentMk (x i) = TorusLoops.loopPrimalCluster hN hM A q.val ∧
          reachesTop (x i)) ∧
        ∀ i k, i ≠ k → ¬ (diamondOpenGraph hN hM true (torusRCSeamClosed A)).Reachable (x i) (x k) := by
    have hq := (Finset.mem_filter.1 q.property).2
    let b := (loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) ⟨0, hMp⟩ q.val).toNat
    have hb : 0 < b := by dsimp [b]; omega
    let _ : NeZero b := ⟨hb.ne'⟩
    have hbcast : (b : ℤ) = loopVertical _ _ (checkerArrows_compatible hN hM (rcSmoothing A)) ⟨0, hMp⟩ q.val :=
      Int.toNat_of_nonneg hq.le
    let c := TorusLoops.loopPrimalCluster hN hM A q.val
    obtain ⟨u₀, hu₀⟩ : ∃ u : FaceVertex N M true, (diamondOpenGraph hN hM true A).connectedComponentMk u = c := by
      induction c using Quot.inductionOn with | h u => exact ⟨u, rfl⟩
    let pwalk (u : {u : FaceVertex N M true // (diamondOpenGraph hN hM true A).connectedComponentMk u = c}) :=
      Classical.choice (exists_indexedWalk_of_reachable hN hM A (SimpleGraph.ConnectedComponent.eq.1 (hu₀.trans u.property.symm)))
    let g : FaceVertex N M true → ZMod b := fun u =>
      if hu : (diamondOpenGraph hN hM true A).connectedComponentMk u = c then ((pwalk ⟨u, hu⟩).winding : ℤ) else 0
    have hg (e : OpenDiamondEdge A) (hec : diamondEdgeCluster hN hM A e = c) :
        g (faceEndpoint hN hM true e.val true) - g (faceEndpoint hN hM true e.val false) =
          if e.val.2.val = 0 then -1 else 0 := by
      have ht : (diamondOpenGraph hN hM true A).connectedComponentMk (faceEndpoint hN hM true e.val true) = c :=
        (SimpleGraph.ConnectedComponent.sound (diamond_endpoints_reachable hN hM A e.val e.property)).symm.trans hec
      let pu := pwalk ⟨faceEndpoint hN hM true e.val false, hec⟩
      let pv := pwalk ⟨faceEndpoint hN hM true e.val true, ht⟩
      let fc : diamondCycleSpace hN hM A := ⟨pu.chain + Pi.single e 1 - pv.chain, by
        change diamondBoundary hN hM A _ = 0
        rw [map_sub, map_add, pu.boundary_chain, pv.boundary_chain, diamondBoundary_single]
        ext w; simp only [Pi.sub_apply, Pi.add_apply, Pi.zero_apply]; ring⟩
      have hs : SupportedOnDiamondCluster hN hM A c fc := fun d hd => by
        have hd₀ : diamondEdgeCluster hN hM A d ≠ (diamondOpenGraph hN hM true A).connectedComponentMk u₀ := by rwa [hu₀]
        have hde : d ≠ e := fun h => hd (h ▸ hec)
        change pu.chain d + (Pi.single e (1 : ℚ) : OpenDiamondEdge A → ℚ) d - pv.chain d = 0
        rw [pu.chain_supported d hd₀, pv.chain_supported d hd₀]; simp [hde]
      have hint (d : OpenDiamondEdge A) : ∃ z : ℤ, fc.val d = z := by
        obtain ⟨zu, hzu⟩ := pu.chain_integral d; obtain ⟨zv, hzv⟩ := pv.chain_integral d
        refine ⟨zu + (if d = e then 1 else 0) - zv, ?_⟩
        change pu.chain d + (Pi.single e (1 : ℚ) : OpenDiamondEdge A → ℚ) d - pv.chain d = _
        simp only [hzu, hzv, Pi.single_apply]; split_ifs <;> push_cast <;> rfl
      obtain ⟨z, hz⟩ := TorusTopology.incident_vertical_winding_divides_integral_cycle hN hM
        ⟨0, TorusTopology.width_pos_of_loop hN hM A q.val⟩ ⟨0, hMp⟩ A q.val hq.ne' fc hs hint
      rw [← hbcast] at hz
      let sgn : ℤ := if e.val.2.val = 0 then -1 else 0
      have hw_fc : diamondWindingY A fc.val = ((pu.winding + sgn - pv.winding : ℤ) : ℚ) := by
        change diamondWindingY A (pu.chain + Pi.single e 1 - pv.chain) = _
        unfold diamondWindingY
        simp only [Pi.sub_apply, Pi.add_apply, mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
        change diamondWindingY A pu.chain + (∑ d, diamondSeamCrossY d.val * (Pi.single e (1 : ℚ) : OpenDiamondEdge A → ℚ) d) -
          diamondWindingY A pv.chain = _
        rw [pu.winding_chain, pv.winding_chain]; simp [Pi.single_apply, mul_ite, diamondSeamCrossY, sgn]
      have hz' : pu.winding + sgn - pv.winding = (b : ℤ) * z := by exact_mod_cast hw_fc.symm.trans hz
      have hcast := congrArg (fun x : ℤ => (x : ZMod b)) hz'
      simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul] at hcast
      have hf₀ : (diamondOpenGraph hN hM true A).connectedComponentMk (faceEndpoint hN hM true e.val false) = c := hec
      dsimp only [g]; rw [dite_eq_left ht, dite_eq_left hf₀]
      have hsub_g : ((pv.winding : ℤ) : ZMod b) - ((pu.winding : ℤ) : ZMod b) = (sgn : ZMod b) := by linear_combination -hcast
      rw [hsub_g]; dsimp [sgn]; split_ifs <;> simp
    let fB := TorusLoops.loopBoundaryCycle hN hM A q.val
    have hsB := TorusLoops.loopBoundaryCycle_supported hN hM A q.val
    have hwB : diamondWindingY A fB.val = (b : ℚ) := by
      rw [TorusTopology.loopBoundaryCycle_windingY hN hM hMp ⟨0, hMp⟩ A q.val]; exact_mod_cast hbcast.symm
    let pflux (k : ZMod b) : ℚ := ∑ e with e.val.2.val = 0 ∧ g (faceEndpoint hN hM true e.val false) = k, fB.val e
    have hflux_succ (k : ZMod b) : pflux (k + 1) = pflux k := by
      let Pk : FaceVertex N M true → ℚ := fun u => if g u = k then 1 else 0
      have hp := diamondBoundary_pairing hN hM A Pk fB.val
      rw [fB.property] at hp; simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hp
      have hterm (e : OpenDiamondEdge A) : diamondCoboundary hN hM A Pk e * fB.val e =
          (if e.val.2.val = 0 ∧ g (faceEndpoint hN hM true e.val false) = k + 1 then fB.val e else 0) -
          (if e.val.2.val = 0 ∧ g (faceEndpoint hN hM true e.val false) = k then fB.val e else 0) := by
        by_cases hc : diamondEdgeCluster hN hM A e = c
        · have he := hg e hc
          by_cases hy : e.val.2.val = 0
          · simp only [hy, ite_true] at he
            have heq : g (faceEndpoint hN hM true e.val true) = k ↔ g (faceEndpoint hN hM true e.val false) = k + 1 :=
              ⟨fun h => by rw [h] at he; linear_combination -he, fun h => by rw [h] at he; linear_combination he⟩
            simp only [diamondCoboundary_apply, Pk, heq, sub_mul, ite_mul, one_mul, zero_mul, hy, true_and]
          · simp only [hy, ite_false] at he; simp [diamondCoboundary_apply, Pk, sub_eq_zero.1 he, hy]
        · rw [hsB e hc]; simp
      apply sub_eq_zero.1; dsimp [pflux]; simp only [Finset.sum_filter]
      rw [← Finset.sum_sub_distrib]; simp_rw [← hterm]; exact hp.symm
    have hflux_all (k : ZMod b) : pflux k = -1 := by
      have hn (n : ℕ) : pflux (n : ZMod b) = pflux 0 := by
        induction n with | zero => simp | succ n ih => rw [Nat.cast_succ, hflux_succ, ih]
      have hall (t : ZMod b) : pflux t = pflux 0 := by rw [← ZMod.natCast_zmod_val t]; exact hn t.val
      have htot : (∑ t : ZMod b, pflux t) = -diamondWindingY A fB.val := by
        dsimp [pflux]; simp only [Finset.sum_filter]; rw [Finset.sum_comm]
        calc _ = ∑ e : OpenDiamondEdge A, if e.val.2.val = 0 then fB.val e else 0 :=
              Finset.sum_congr rfl fun e _ => by by_cases hy : e.val.2.val = 0 <;> simp [hy]
          _ = -diamondWindingY A fB.val := by
              unfold diamondWindingY; rw [← Finset.sum_neg_distrib]
              exact Finset.sum_congr rfl fun e _ => by by_cases hy : e.val.2.val = 0 <;> simp [diamondSeamCrossY, hy]
      simp_rw [hall] at htot
      rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, hwB] at htot
      have h0 : pflux 0 = -1 := mul_left_cancel₀ (by positivity : (b : ℚ) ≠ 0) (by simpa only [mul_neg_one] using htot)
      rw [hall, h0]
    have hphase_ex (k : ZMod b) : ∃ u : FaceVertex N M true, u.val.2.val = 0 ∧
        (diamondOpenGraph hN hM true A).connectedComponentMk u = c ∧ g u = k ∧ reachesTop u := by
      by_contra hn
      let Pk : FaceVertex N M true → ℚ := fun u => if g u = k ∧ reachesTop u then 1 else 0
      have hp := diamondBoundary_pairing hN hM A Pk fB.val
      rw [fB.property] at hp; simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hp
      have hterm (e : OpenDiamondEdge A) : diamondCoboundary hN hM A Pk e * fB.val e =
          if e.val.2.val = 0 ∧ g (faceEndpoint hN hM true e.val false) = k + 1 then fB.val e else 0 := by
        by_cases hc : diamondEdgeCluster hN hM A e = c
        · have he := hg e hc
          by_cases hy : e.val.2.val = 0
          · simp only [hy, ite_true] at he
            have hfy : (faceEndpoint hN hM true e.val false).val.2.val = 0 := by rw [TorusTopology.faceEndpoint_false_y]; exact hy
            have hty : (faceEndpoint hN hM true e.val true).val.2.val + 1 = M := by
              obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hMp.ne'
              have hz : e.val.2 = 0 := Fin.ext hy
              have hep : (faceEndpoint hN hM true e.val true).val.2 = prv e.val.2 := by
                cases hcheck : checker e.val <;> simp [faceEndpoint, faceEndpointRaw, hcheck]
              rw [hep, hz, prv_zero]; simp
            have hrt : reachesTop (faceEndpoint hN hM true e.val true) := ⟨_, hty, SimpleGraph.Reachable.refl _⟩
            have hfalse : Pk (faceEndpoint hN hM true e.val false) = 0 := by
              dsimp [Pk]; split_ifs with h
              · exact (hn ⟨_, hfy, hc, h.1, h.2⟩).elim
              · rfl
            have heq : g (faceEndpoint hN hM true e.val true) = k ↔ g (faceEndpoint hN hM true e.val false) = k + 1 :=
              ⟨fun h => by rw [h] at he; linear_combination -he, fun h => by rw [h] at he; linear_combination he⟩
            rw [diamondCoboundary_apply, hfalse]
            simp only [Pk, hrt, and_true, heq, sub_zero, ite_mul, one_mul, zero_mul, hy, true_and]
          · simp only [hy, ite_false] at he
            have hopen : torusRCSeamClosed A e.val = true := by simp [torusRCSeamClosed, hy, e.property]
            have hr_ep := diamond_endpoints_reachable hN hM (torusRCSeamClosed A) e.val hopen
            have htop : reachesTop (faceEndpoint hN hM true e.val true) ↔ reachesTop (faceEndpoint hN hM true e.val false) :=
              ⟨fun ⟨v, hv, hvR⟩ => ⟨v, hv, hr_ep.trans hvR⟩, fun ⟨v, hv, hvR⟩ => ⟨v, hv, hr_ep.symm.trans hvR⟩⟩
            simp [diamondCoboundary_apply, Pk, sub_eq_zero.1 he, propext htop, hy]
        · rw [hsB e hc]; simp
      have hz : pflux (k + 1) = 0 := by dsimp [pflux]; rw [Finset.sum_filter]; simp_rw [← hterm]; exact hp.symm
      rw [hflux_all (k + 1)] at hz; norm_num at hz
    choose x hx using fun i : Fin b => hphase_ex (i.val : ZMod b)
    refine ⟨x, fun i => ⟨(hx i).1, (hx i).2.1, (hx i).2.2.2⟩, fun i k hik hr_ik => ?_⟩
    have hconst {u v : FaceVertex N M true}
        (hu : (diamondOpenGraph hN hM true A).connectedComponentMk u = c)
        (hreach : (diamondOpenGraph hN hM true (torusRCSeamClosed A)).Reachable u v) : g u = g v := by
      rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
      induction hreach with
      | refl => rfl
      | @tail w z hr' hwz ih =>
        have hw : (diamondOpenGraph hN hM true A).connectedComponentMk w = c :=
          (SimpleGraph.ConnectedComponent.sound (((SimpleGraph.reachable_iff_reflTransGen u w).2 hr').mono hsubG)).symm.trans hu
        rw [diamondOpenGraph, SimpleGraph.fromEdgeSet_adj] at hwz
        obtain ⟨⟨e, he, hep⟩, _⟩ := hwz
        have hy : e.2.val ≠ 0 := fun h => by simp [torusRCSeamClosed, h] at he
        have hAe : A e = true := by simpa only [torusRCSeamClosed, hy, ite_false] using he
        have hstep : g w = g z := by
          rcases Sym2.eq_iff.1 hep with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · have hv := hg ⟨e, hAe⟩ hw; simp only [hy, ite_false] at hv; exact (sub_eq_zero.1 hv).symm
          · have hc : diamondEdgeCluster hN hM A ⟨e, hAe⟩ = c :=
              (SimpleGraph.ConnectedComponent.sound (diamond_endpoints_reachable hN hM A e hAe)).trans hw
            have hv := hg ⟨e, hAe⟩ hc; simp only [hy, ite_false] at hv; exact sub_eq_zero.1 hv
        exact ih.trans hstep
    have hlabel : (i.val : ZMod b) = (k.val : ZMod b) :=
      (hx i).2.2.1.symm.trans ((hconst (hx i).2.1 hr_ik).trans (hx k).2.2.1)
    have hv := congrArg ZMod.val hlabel
    simp only [ZMod.val_natCast] at hv
    rw [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt k.isLt] at hv
    exact hik (Fin.ext hv)
  choose x hx using hex
  let X (s : TorusTopology.VerticalPhaseIndex hN hM ⟨0, hMp⟩ A) := x s.1 s.2
  have hinj : Function.Injective (fun s =>
      (diamondOpenGraph hN hM true (torusRCSeamClosed A)).connectedComponentMk (X s)) := by
    rintro ⟨q, i⟩ ⟨r', k⟩ he
    have hreach := SimpleGraph.ConnectedComponent.eq.1 he
    have hqr : q = r' := TorusTopology.positive_vertical_loops_primalCluster_injective hN hM ⟨0, hMp⟩ A
      (((hx q).1 i).2.1.symm.trans ((SimpleGraph.ConnectedComponent.sound (hreach.mono hsubG)).trans ((hx r').1 k).2.1))
    subst r'
    have hik : i = k := by by_contra hn; exact (hx q).2 i k hn hreach
    subst k; rfl
  obtain ⟨emb⟩ : Nonempty (Fin r ↪ TorusTopology.VerticalPhaseIndex hN hM ⟨0, hMp⟩ A) :=
    Function.Embedding.nonempty_of_card_le (by rw [Fintype.card_fin, TorusTopology.card_verticalPhaseIndex]; exact hr)
  exact ⟨fun i => X (emb i), fun i => ((hx (emb i).1).1 (emb i).2).1,
    fun i => ((hx (emb i).1).1 (emb i).2).2.2,
    fun i j hij hreach => hij (emb.injective (hinj (SimpleGraph.ConnectedComponent.sound hreach)))⟩

private theorem torusRCVerticalTail_close_seam_le_unconditional
    (hN : Even N) (hM : Even M) (hMp : 0 < M) (q : Set.Ici (1 : ℝ)) (r : ℕ) :
    (1 - (rcCriticalParameter q).val) ^ N * torusRCProbability hN hM q (torusRCVerticalTail hN hM ⟨0, hMp⟩ r) ≤
      torusRCProbability hN hM q (torusRCSeamClosedCrossingEvent hN hM r ∩ torusRCSeamRowClosed hMp) := by
  let S : Finset (Fin N × Fin M) := Finset.univ.image fun i : Fin N => (i, (⟨0, hMp⟩ : Fin M))
  let E := torusRCSeamClosedCrossingEvent hN hM r
  have hstable (v : Fin N × Fin M) (hv : v ∈ S) (A : RCConfig N M) : A ∈ E ↔ toggleEdge A v ∈ E := by
    obtain ⟨i, _, hEq⟩ := Finset.mem_image.mp hv
    have hv0 : v.2.val = 0 := by rw [← hEq]
    have htog : torusRCSeamClosed (toggleEdge A v) = torusRCSeamClosed A := funext fun e => by
      by_cases he : e.2.val = 0
      · simp [torusRCSeamClosed, he]
      · simp only [torusRCSeamClosed, he, ite_false]
        exact toggleEdge_away A fun h => he (h ▸ hv0)
    change torusRCSeamClosedCylinderCrossings hN hM r (torusRCSeamClosed A) ↔
      torusRCSeamClosedCylinderCrossings hN hM r (torusRCSeamClosed (toggleEdge A v))
    rw [htog]
  have hfinite := TorusLoops.torusRCProbability_close_finite_set hN hM q S E hstable
  change (1 - (rcCriticalParameter q).val) ^ S.card * TorusLoops.phi_T_probability hN hM q E ≤
    TorusLoops.phi_T_probability hN hM q (E ∩ {A | ∀ v ∈ S, A v = false}) at hfinite
  have hcard : S.card = N := by
    rw [Finset.card_image_iff.mpr fun i _ j _ hij => congrArg Prod.fst hij]; simp
  have hclosed : (E ∩ {A | ∀ v ∈ S, A v = false}) = E ∩ torusRCSeamRowClosed hMp := by
    ext A; refine ⟨fun ⟨hE, hcl⟩ => ⟨hE, fun i => hcl _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)⟩,
      fun ⟨hE, hcl⟩ => ⟨hE, fun v hv => by obtain ⟨i, _, hEq⟩ := Finset.mem_image.mp hv; rw [← hEq]; exact hcl i⟩⟩
  rw [hclosed, hcard] at hfinite
  have hmono := torusRCProbability_mono hN hM q
    (show torusRCVerticalTail hN hM ⟨0, hMp⟩ r ⊆ E from fun A hA => seamClosedCylinderCrossings_of_le_U hN hM hMp r A hA)
  exact (mul_le_mul_of_nonneg_left hmono (pow_nonneg (sub_pos.mpr (criticalParameter_lt_one q)).le N)).trans
    (by simpa [E, TorusLoops.phi_T_probability] using hfinite)

local instance (hN : Even N) (hM : Even M) : DecidableEq (fullDiamondGraph hN hM).edgeSet := Classical.decEq _

private theorem torus_seam_joint_le_cylinder (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (hMp : 0 < M) (q : Set.Ici (1 : ℝ)) (r : ℕ) :
    torusRCProbability hN hM q (torusRCSeamClosedCrossingEvent hN hM r ∩ torusRCSeamRowClosed hMp) ≤
      (measure (fullCylinderGraph hN hM) (torusRCBridgeParameters q) (BoundaryCondition.free ∅)
        {C | torusRCSeamClosedCylinderCrossings hN hM r (cylinderIndexedConfiguration hN hM hN4 hM4 C)}).toReal := by
  let G := fullCylinderGraph hN hM; let H := fullDiamondGraph hN hM
  let _ : Fintype G.edgeSet := Fintype.ofFinite _
  let _ : Fintype H.edgeSet := Fintype.ofFinite _
  let hGH : G ≤ H := fullCylinderGraph_le_full hN hM
  let E : Set (Configuration G) := {C | torusRCSeamClosedCylinderCrossings hN hM r (cylinderIndexedConfiguration hN hM hN4 hM4 C)}
  let T := frozenStateEvent (subgraphRemovedEdges G H) (closedSubgraphRecord G H)
  rw [torusRCProbability_eq_fk_image hN hM hN4 hM4 q]
  have hsub : torusRCConfigurationEquiv hN hM hN4 hM4 ''
      (torusRCSeamClosedCrossingEvent hN hM r ∩ torusRCSeamRowClosed hMp) ⊆
      T ∩ (subgraphRemainderRead hGH) ⁻¹' E := by
    rintro C ⟨A, ⟨hcross, hclosed⟩, rfl⟩
    have hT : torusRCConfigurationEquiv hN hM hN4 hM4 A ∈ T := by
      change _ ∩ _ = ∅
      refine Finset.eq_empty_iff_forall_notMem.2 fun e he => ?_
      obtain ⟨heA, heR⟩ := Finset.mem_inter.1 he
      have hn := (mem_subgraphRemovedEdges (G := G) (H := H) e).1 heR
      obtain ⟨d, hd⟩ := (torusIndexedEdgeEquiv hN hM hN4 hM4).surjective e
      have hdA : A d = true := (mem_torusRCConfigurationEquiv hN hM hN4 hM4 A d).1
        (by change torusIndexedEdgeEquiv hN hM hN4 hM4 d ∈ _; rwa [hd])
      have hrow : d.2.val ≠ 0 := fun hz => by
        have hy : d.2 = (⟨0, hMp⟩ : Fin M) := Fin.ext hz
        have hc := hclosed d.1; rw [← hy] at hc
        exact Bool.noConfusion (hdA.symm.trans hc)
      exact hn (hd ▸ (indexedEdge_mem_cylinder_iff hN hM hN4 hM4 d).2 hrow)
    refine ⟨hT, ?_⟩
    have hidx : cylinderIndexedConfiguration hN hM hN4 hM4 (subgraphRemainderRead hGH (torusRCConfigurationEquiv hN hM hN4 hM4 A)) = A := by
      unfold cylinderIndexedConfiguration; rw [closedSubgraph_reconstruct hGH _ hT, Equiv.symm_apply_apply]
    change torusRCSeamClosedCylinderCrossings hN hM r _; rw [hidx]
    have hseam : torusRCSeamClosed A = A := by
      funext e; by_cases hz : e.2.val = 0
      · have hy : e.2 = (⟨0, hMp⟩ : Fin M) := Fin.ext hz
        simp only [torusRCSeamClosed, hz, ite_true]
        simpa only [← hy, Prod.eta] using (hclosed e.1).symm
      · simp [torusRCSeamClosed, hz]
    change torusRCSeamClosedCylinderCrossings hN hM r (torusRCSeamClosed A) at hcross
    rwa [hseam] at hcross
  refine (measureReal_mono hsub).trans ?_
  rw [Measure.real_def, fk_measureReal_eq_expectation, fk_measureReal_eq_expectation]
  exact closedSubgraph_joint_le hGH (torusRCBridgeParameters q) E

private abbrev BottomVertex (N M : ℕ) := {v : FaceVertex N M true // v.val.2.val = 0}
private abbrev TopVertex (N M : ℕ) := {v : FaceVertex N M true // v.val.2.val + 1 = M}

local instance : DecidableEq (FaceVertex N M true) := Classical.decEq _

private theorem cylinderCrossings_probability_le (hN : Even N) (hM : Even M)
    (hN4 : 4 ≤ N) (hM4 : 4 ≤ M) (θ : Parameters)
    (μ : Measure LatticeConfiguration) (hμ : IsRCInfiniteVolumeLimit θ.toP θ.toQ 0 μ)
    (r : ℕ) (hr : 1 ≤ r) :
    (measure (fullCylinderGraph hN hM) θ (BoundaryCondition.free ∅)
      {C | TorusRC.torusRCSeamClosedCylinderCrossings hN hM r
        (cylinderIndexedConfiguration hN hM hN4 hM4 C)}).toReal ≤
      (N : ℝ) ^ (2 * r) *
        (Real.sqrt (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite (2 * (M - 1)))))) ^ (r - 1) := by
  let G := fullCylinderGraph hN hM
  let _ : Fintype G.edgeSet := Fintype.ofFinite _
  let ν := measure G θ (BoundaryCondition.free ∅)
  let Z := (Fin r → BottomVertex N M) × (Fin r → TopVertex N M)
  let c := Real.sqrt (μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite (2 * (M - 1)))))
  let per {α : Type} (x : Fin r → α) (n : ℕ) : α := x ⟨n % r, Nat.mod_lt n (by omega)⟩
  let epEvent (z : Z) : Set (Configuration G) :=
    distinctConnections G (fun n => (per z.1 n).val) (fun n => (per z.2 n).val) r
  have hsub : {C | TorusRC.torusRCSeamClosedCylinderCrossings hN hM r (cylinderIndexedConfiguration hN hM hN4 hM4 C)} ⊆
      ⋃ z : Z, epEvent z := fun C ⟨x, hx, hy, hd⟩ => by
    choose y hyTop hyConn using hy
    let z : Z := (fun i => ⟨x i, hx i⟩, fun i => ⟨y i, hyTop i⟩)
    refine Set.mem_iUnion.2 ⟨z, ?_⟩
    have hg := openGraph_cylinderIndexedConfiguration hN hM hN4 hM4 C
    rw [cylinderIndexedConfiguration_eq_seamClosed] at hg
    refine ⟨fun i hi => ?_, fun i hi k hk hik hc => ?_⟩
    · have hc := hyConn ⟨i, hi⟩; rw [← hg] at hc
      simpa only [FK.ActualConnected, z, per, Nat.mod_eq_of_lt hi, Subtype.coe_mk] using hc
    · apply hd ⟨i, hi⟩ ⟨k, hk⟩ (fun h => hik (congrArg Fin.val h))
      rw [← hg]
      simpa only [FK.ActualConnected, z, per, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hk, Subtype.coe_mk] using hc
  have hcardB : Fintype.card (BottomVertex N M) ≤ N := by
    simpa using Fintype.card_le_of_injective (fun v : BottomVertex N M => v.val.val.1) fun u v h =>
      Subtype.ext (Subtype.ext (Prod.ext h (Fin.ext (u.property.trans v.property.symm))))
  have hcardT : Fintype.card (TopVertex N M) ≤ N := by
    simpa using Fintype.card_le_of_injective (fun v : TopVertex N M => v.val.val.1) fun u v h =>
      Subtype.ext (Subtype.ext (Prod.ext h (Fin.ext (by have := u.property; have := v.property; omega))))
  have hcard : Fintype.card Z ≤ N ^ (2 * r) := by
    simp only [Z, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    exact (Nat.mul_le_mul (Nat.pow_le_pow_left hcardB r) (Nat.pow_le_pow_left hcardT r)).trans_eq
      (by rw [← pow_add]; congr 1; omega)
  have hdist (z : Z) : ν.real (epEvent z) ≤ c ^ (r - 1) := by
    let x := fun n => (per z.1 n).val; let y := fun n => (per z.2 n).val
    refine distinctConnections_probability_le_pow G θ x y c (Real.sqrt_nonneg _) (fun j hj C hC hx hy => ?_) r hr
    let A := cylinderIndexedConfiguration hN hM hN4 hM4 C
    have hg := openGraph_cylinderIndexedConfiguration hN hM hN4 hM4 C
    have hst : (diamondOpenGraph hN hM true (TorusRC.torusRCSeamClosed A)).Reachable (x 0) (y 0) :=
      hg ▸ hC.1 0 (by omega)
    obtain ⟨f, hfy, hf⟩ := exists_unexploredCylinder_embedding hN hM (by omega) (by omega)
      (per z.1 0).property (per z.2 0).property hst
    let T := actualMultiClusterComplementSet G (prefixSeeds x j) C
    let g : T ↪ RotatedVertex := (inducedVertexEmbedding T).trans f
    have hfirst : x 0 ∈ prefixSeeds x j := Finset.mem_image.2 ⟨0, Finset.mem_range.2 (by omega), rfl⟩
    have hn (w : T) : (diamondOpenGraph hN hM true (TorusRC.torusRCSeamClosed A)).connectedComponentMk w.val ≠
        (diamondOpenGraph hN hM true (TorusRC.torusRCSeamClosed A)).connectedComponentMk (x 0) := fun he =>
      w.property ⟨x 0, hfirst, by unfold ActualConnected; rw [hg]; exact SimpleGraph.ConnectedComponent.exact he.symm⟩
    have hg_map : (G.induce T).map g ≤ rotatedLattice := fun a b hab => by
      obtain ⟨u, v, huv, rfl, rfl⟩ := (SimpleGraph.map_adj _ _ _ _).1 hab
      apply hf u.val v.val
      have hfull : (fullCylinderGraph hN hM).Adj u.val v.val := SimpleGraph.induce_adj.mp huv
      rw [fullCylinderGraph, diamondOpenGraph, SimpleGraph.fromEdgeSet_adj] at hfull
      obtain ⟨⟨e, he, hep⟩, hne⟩ := hfull
      have hrow : e.2.val ≠ 0 := fun hz => by simp [TorusRC.torusRCSeamClosed, hz] at he
      have hend : ∀ b : Bool,
          (diamondOpenGraph hN hM true (TorusRC.torusRCSeamClosed A)).connectedComponentMk (faceEndpoint hN hM true e b) ≠
            (diamondOpenGraph hN hM true (TorusRC.torusRCSeamClosed A)).connectedComponentMk (x 0) := by
        rcases Sym2.eq_iff.1 hep with ⟨he0, he1⟩ | ⟨he0, he1⟩ <;> intro b <;> cases b
        · rw [← show u.val = faceEndpoint hN hM true e false from he0]; exact hn u
        · rw [← show v.val = faceEndpoint hN hM true e true from he1]; exact hn v
        · rw [← show v.val = faceEndpoint hN hM true e false from he1]; exact hn v
        · rw [← show u.val = faceEndpoint hN hM true e true from he0]; exact hn u
      rw [diamondOpenGraph, SimpleGraph.fromEdgeSet_adj]
      exact ⟨⟨e, decide_eq_true ⟨hrow, hend⟩, hep⟩, hne⟩
    have hk : (g ⟨y j, hy⟩).val.2 - (g ⟨x j, hx⟩).val.2 = ((M - 1 : ℕ) : ℤ) := by
      change (f (y j)).val.2 - (f (x j)).val.2 = _
      have hyj : (y j).val.2.val + 1 = M := (per z.2 j).property
      rw [hfy, hfy, (per z.1 j).property, Nat.cast_zero, sub_zero]
      exact_mod_cast (show (y j).val.2.val = M - 1 by omega)
    exact Real.le_sqrt_of_sq_le (finiteFree_connectivity_sq_le_diagonal (G.induce T) θ μ hμ g hg_map
      ⟨x j, hx⟩ ⟨y j, hy⟩ (M - 1) hk)
  calc _ ≤ ν.real (⋃ z : Z, epEvent z) := measureReal_mono hsub
    _ ≤ ∑ z : Z, ν.real (epEvent z) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _z : Z, c ^ (r - 1) := Finset.sum_le_sum fun z _ => hdist z
    _ = (Fintype.card Z : ℝ) * c ^ (r - 1) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

private theorem windingTail_probability_pos (hN : Even N) (hM : Even M) (j : Fin M)
    (q : Set.Ici (1 : ℝ)) (r : ℕ) (hr : r ≤ N / 2) :
    0 < torusRCProbability hN hM q (torusRCVerticalTail hN hM j r) := by
  let negA : ArrowConfig N M := ⟨fun _ => false, fun _ => false⟩
  obtain ⟨s, hs⟩ := (exists_compatibleConfig_iff negA).2 fun _ => rfl
  let A := smoothingRC s
  have hA : CompatibleConfig negA (rcSmoothing A) := by simpa only [A, rcSmoothing_smoothingRC] using hs
  have habs : negA.absUp = 0 := by unfold ArrowConfig.absUp; split_ifs <;> simp [ArrowConfig.rowUp, negA]
  have hU := sector_le_rcVerticalWinding hN hM j A negA hA (r := N / 2) (by rw [habs, zero_add])
  have hm := torusRCProbability_mono hN hM q
    (Set.singleton_subset_iff.2 (show A ∈ torusRCVerticalTail hN hM j r from hr.trans hU))
  rw [torusRCProbability_singleton] at hm
  exact (torusRCMass_pos hN hM q A).trans_le hm

end TorusCylinder

/-- The exact contract `RCMProof.contract_eq316` is discharged by the proved equation (3.16). -/
theorem contract_eq316 : PottsDiscontinuity.RCMProof.contract_eq316 := by
  intro q μ hμ ξinv hRate r hr
  have hpEv : Tendsto positiveEvenPeriod atTop atTop :=
    tendsto_atTop.2 fun k => by filter_upwards [eventually_ge_atTop k] with m hm; dsimp [positiveEvenPeriod]; omega
  have hshEv : Tendsto (fun m => 2 * (positiveEvenPeriod m - 1)) atTop atTop :=
    tendsto_atTop.2 fun k => by filter_upwards [eventually_ge_atTop k] with m hm; dsimp [positiveEvenPeriod]; omega
  let D : ℕ → ℝ := fun k => μ.real (CorrLength.connectionEvent (0, 0) (diagonalSite k))
  have hDpos (k : ℕ) : 0 < D k := isRCInfiniteVolumeLimit_connection_positive (criticalParameters q) μ hμ (0, 0) (diagonalSite k)
  have hsqrt_rate : Tendsto (fun m => Real.log (Real.sqrt (D (2 * (positiveEvenPeriod m - 1)))) /
      (positiveEvenPeriod m : ℝ)) atTop (𝓝 (-ξinv)) := by
    have hinv : Tendsto (fun m => 1 / (positiveEvenPeriod m : ℝ)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_one_div_atTop_nhds_zero_nat.comp hpEv
    have hratio : Tendsto (fun m => ((2 * (positiveEvenPeriod m - 1) : ℕ) : ℝ) / (2 * (positiveEvenPeriod m : ℝ))) atTop (𝓝 (1 : ℝ)) := by
      refine (by simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub hinv : Tendsto _ _ _).congr fun m => ?_
      have hm : 1 ≤ positiveEvenPeriod m := by dsimp [positiveEvenPeriod]; omega
      have hmn : (positiveEvenPeriod m : ℝ) ≠ 0 := by exact_mod_cast (show positiveEvenPeriod m ≠ 0 by omega)
      rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hm, Nat.cast_one]; field_simp
    refine (by simpa only [mul_one] using (hRate.comp hshEv).neg.mul hratio : Tendsto _ _ _).congr fun m => ?_
    simp only [Function.comp_apply]; rw [Real.log_sqrt (hDpos _).le]
    have hmn : (positiveEvenPeriod m : ℝ) ≠ 0 := by exact_mod_cast (positiveEvenPeriod_pos m).ne'
    have hin : ((2 * (positiveEvenPeriod m - 1) : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (show 2 * (positiveEvenPeriod m - 1) ≠ 0 by dsimp [positiveEvenPeriod]; omega)
    dsimp only [D]; field_simp
  have he : ∀ᶠ n : ℕ in atTop,
      limsup (fun m : ℕ => positiveEvenVerticalTailRateE q r n m) atTop ≤
        ((-((r - 1 : ℕ) : ℝ) * ξinv : ℝ) : EReal) := by
    filter_upwards [eventually_ge_atTop (r + 1)] with n hn
    have hN4 : 4 ≤ positiveEvenPeriod n := by dsimp [positiveEvenPeriod]; omega
    have hrN : r ≤ positiveEvenPeriod n / 2 := by dsimp [positiveEvenPeriod]; omega
    let N := positiveEvenPeriod n
    let p : ℕ → ℝ := fun m => torusRCProbability (positiveEvenPeriod_even n) (positiveEvenPeriod_even m) q
      (torusRCVerticalTail (positiveEvenPeriod_even n) (positiveEvenPeriod_even m) ⟨0, positiveEvenPeriod_pos m⟩ r)
    let K := (N : ℝ) ^ (2 * r) / (1 - (rcCriticalParameter q).val) ^ N
    have hK : 0 < K := div_pos (pow_pos (by exact_mod_cast positiveEvenPeriod_pos n) _)
      (pow_pos (sub_pos.2 (criticalParameter_lt_one q)) _)
    let F : ℕ → ℝ := fun m => Real.log K / (positiveEvenPeriod m : ℝ) +
      ((r - 1 : ℕ) : ℝ) * (Real.log (Real.sqrt (D (2 * (positiveEvenPeriod m - 1)))) / (positiveEvenPeriod m : ℝ))
    have hF : Tendsto F atTop (𝓝 (-((r - 1 : ℕ) : ℝ) * ξinv)) := by
      simpa only [Function.comp_def, zero_add, mul_neg, neg_mul] using
        ((tendsto_const_div_atTop_nhds_zero_nat (Real.log K)).comp hpEv).add (hsqrt_rate.const_mul ((r - 1 : ℕ) : ℝ))
    have hFE : Tendsto (fun m => (F m : EReal)) atTop (𝓝 ((-((r - 1 : ℕ) : ℝ) * ξinv : ℝ) : EReal)) :=
      EReal.tendsto_coe.mpr hF
    change limsup (fun m => ((Real.log (p m) / (positiveEvenPeriod m : ℝ) : ℝ) : EReal)) atTop ≤ _
    rw [← hFE.limsup_eq]
    refine limsup_le_limsup ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    apply EReal.coe_le_coe_iff.mpr
    have hp_pos : 0 < p m := windingTail_probability_pos (positiveEvenPeriod_even n) (positiveEvenPeriod_even m)
      ⟨0, positiveEvenPeriod_pos m⟩ q r hrN
    have hp_le : p m ≤ K * (Real.sqrt (D (2 * (positiveEvenPeriod m - 1)))) ^ (r - 1) := by
      have hM4 : 4 ≤ positiveEvenPeriod m := by dsimp [positiveEvenPeriod]; omega
      have hden : 0 < (1 - (rcCriticalParameter q).val) ^ N := pow_pos (sub_pos.2 (criticalParameter_lt_one q)) N
      have hc := torusRCVerticalTail_close_seam_le_unconditional (positiveEvenPeriod_even n) (positiveEvenPeriod_even m)
        (positiveEvenPeriod_pos m) q r
      have hs := torus_seam_joint_le_cylinder (positiveEvenPeriod_even n) (positiveEvenPeriod_even m)
        hN4 hM4 (positiveEvenPeriod_pos m) q r
      have hb := cylinderCrossings_probability_le (positiveEvenPeriod_even n) (positiveEvenPeriod_even m)
        hN4 hM4 (torusRCBridgeParameters q) μ hμ r hr
      dsimp [K, p, D]; rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ hden).2 (by simpa only [mul_comm] using hc.trans (hs.trans hb))
    have hsqrt := Real.sqrt_pos.2 (hDpos (2 * (positiveEvenPeriod m - 1)))
    have hlog := Real.log_le_log hp_pos hp_le
    rw [Real.log_mul hK.ne' (pow_pos hsqrt (r - 1)).ne', Real.log_pow] at hlog
    simpa only [F, add_div, mul_div_assoc] using div_le_div_of_nonneg_right hlog (Nat.cast_nonneg _)
  simpa using limsup_le_limsup (v := fun _ : ℕ => ((-((r - 1 : ℕ) : ℝ) * ξinv : ℝ) : EReal)) he

end
end PottsDiscontinuity.TorusExploration
