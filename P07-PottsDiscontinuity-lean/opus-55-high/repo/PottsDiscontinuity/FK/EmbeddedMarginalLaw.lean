/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.IsolatedBoundaryLaw
public import PottsDiscontinuity.FK.SubgraphComparison

public section

namespace PottsDiscontinuity.FK

noncomputable section

variable {V W : Type*} [Finite V] [Finite W]
  (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W)
  (hGH : G.map f ≤ H)

local instance embeddedMarginalOuterEdgeDecidableEq : DecidableEq H.edgeSet := Classical.decEq _

omit [Finite V] in
theorem embeddedConfigurationRestriction_union_subgraphRemoved
    (K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H))
    (A : Configuration H) :
    embeddedConfigurationRestriction G H f hGH (A ∪ K.val) =
      embeddedConfigurationRestriction G H f hGH A := by
  have hmapped (e : G.edgeSet) :
      (embeddedEdgeEmbedding G H f hGH e).val ∈ (G.map f).edgeSet := by
    rw [embeddedEdgeEmbedding_coe]
    exact (isolatedExtensionEdgeEquiv G f e).property
  have hnot (e : G.edgeSet) : embeddedEdgeEmbedding G H f hGH e ∉ K.val := by
    intro heK
    have heR :=
      K.property heK
    exact ((mem_subgraphRemovedEdges (embeddedEdgeEmbedding G H f hGH e)).mp heR)
      (hmapped e)
  apply Finset.ext
  intro e
  rw [mem_embeddedConfigurationRestriction, mem_embeddedConfigurationRestriction,
    Finset.mem_union]
  constructor
  · tauto
  · grind

section
variable (q : Parameters)
theorem remainingLaw_map_embeddedRestriction
    (B : BoundaryCondition W)
    (K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H)) :
    (remainingLaw H q (frozenBoundary B K.val)
      (subgraphRemovedEdges (G.map f) H)).map
        (fun C => embeddedConfigurationRestriction G H f hGH
          (C.val ∪ K.val)) =
      law G q (isolatedExtensionPullbackBoundary f (frozenBoundary B K.val)) := by
  let R := subgraphRemovedEdges (G.map f) H
  let E : Configuration (G.map f) ≃ RemainingConfiguration H R :=
    subgraphRemainingConfigurationEquiv hGH
  let I := isolatedExtensionConfigurationEquiv G f
  have hsub : (law (G.map f) q (frozenBoundary B K.val)).map E =
      remainingLaw H q (frozenBoundary B K.val) R :=
    law_subgraphRemaining_map hGH q (frozenBoundary B K.val)
  have hrem :
      (remainingLaw H q (frozenBoundary B K.val) R).map E.symm =
        law (G.map f) q (frozenBoundary B K.val) := by
    calc
      _ = ((law (G.map f) q (frozenBoundary B K.val)).map E).map E.symm := by simp_all
      _ = law (G.map f) q (frozenBoundary B K.val) := by
        rw [PMF.map_comp]
        have hcomp : E.symm ∘ E = id := by
          simp
        rw [hcomp, PMF.map_id]
  have hiso : (law G q (isolatedExtensionPullbackBoundary f
      (frozenBoundary B K.val))).map I =
        law (G.map f) q (frozenBoundary B K.val) :=
    law_isolatedExtension_map_boundary_pullback G f q (frozenBoundary B K.val)
  have hback : (law (G.map f) q (frozenBoundary B K.val)).map I.symm =
      law G q (isolatedExtensionPullbackBoundary f (frozenBoundary B K.val)) := by
    calc
      _ = ((law G q (isolatedExtensionPullbackBoundary f
          (frozenBoundary B K.val))).map I).map I.symm := by simp_all
      _ = law G q (isolatedExtensionPullbackBoundary f
          (frozenBoundary B K.val)) := by
        rw [PMF.map_comp]
        have hcomp : I.symm ∘ I = id := by
          simp
        rw [hcomp, PMF.map_id]
  have hfun : (fun C : RemainingConfiguration H R => I.symm (E.symm C)) =
      (fun C => embeddedConfigurationRestriction G H f hGH (C.val ∪ K.val)) := by
    funext C
    rw [embeddedConfigurationRestriction_union_subgraphRemoved G H f hGH K C.val]
    rfl
  calc
    (remainingLaw H q (frozenBoundary B K.val) R).map
        (fun C => embeddedConfigurationRestriction G H f hGH (C.val ∪ K.val)) =
      (remainingLaw H q (frozenBoundary B K.val) R).map
        (fun C => I.symm (E.symm C)) := by simp_all
    _ = ((remainingLaw H q (frozenBoundary B K.val) R).map E.symm).map I.symm := by
      calc
        _ = (remainingLaw H q (frozenBoundary B K.val) R).map
            (I.symm ∘ E.symm) := by
              rfl
        _ = _ := by rw [PMF.map_comp]
    _ = law G q (isolatedExtensionPullbackBoundary f (frozenBoundary B K.val)) := by
      simp_all

/-- The true outer FK law, restricted to the embedded graph, is the mixture of
the exact inner FK laws induced by each actual removed-edge state. -/
theorem law_embeddedConfigurationRestriction_eq_bind_frozenMarginal
    (ξ : BoundaryCondition W) :
    (law H q ξ).map (embeddedConfigurationRestriction G H f hGH) =
      (frozenMarginalLaw q ξ (subgraphRemovedEdges (G.map f) H)).bind
        (fun K => law G q (isolatedExtensionPullbackBoundary f
          (frozenBoundary ξ K.val))) := by
  let R := subgraphRemovedEdges (G.map f) H
  let split :=
    fun C => (configurationSplitEquiv H R C).1
  let S :=
    fun C => (isolatedExtensionConfigurationEquiv G f).symm
      ((subgraphRemainingConfigurationEquiv hGH).symm C)
  have hcompose : (fun C : Configuration H => S (split C)) =
      embeddedConfigurationRestriction G H f hGH := by
    funext C
    dsimp [S, split, R]
    rw [subgraphRemainingConfigurationEquiv_symm_split]
    rfl
  calc
    (law H q ξ).map (embeddedConfigurationRestriction G H f hGH) =
        (law H q ξ).map (S ∘ split) := by
          tauto
    _ = ((law H q ξ).map split).map S := by
      rw [PMF.map_comp]
    _ = (frozenMarginalLaw q ξ R).bind
        (fun K => (remainingLaw H q (frozenBoundary ξ K.val) R).map S) := by
      rw [law_map_remaining_eq_bind_frozen, PMF.map_bind]
    _ = (frozenMarginalLaw q ξ R).bind
        (fun K => law G q (isolatedExtensionPullbackBoundary f
          (frozenBoundary ξ K.val))) := by
      apply congrArg (PMF.bind (frozenMarginalLaw q ξ R))
      funext K
      have hS : S = (fun C : RemainingConfiguration H R =>
          embeddedConfigurationRestriction G H f hGH (C.val ∪ K.val)) := by
        funext C
        change embeddedConfigurationRestriction G H f hGH C.val =
          embeddedConfigurationRestriction G H f hGH (C.val ∪ K.val)
        simp [embeddedConfigurationRestriction_union_subgraphRemoved]
      grind [remainingLaw_map_embeddedRestriction]
end

end
end PottsDiscontinuity.FK
