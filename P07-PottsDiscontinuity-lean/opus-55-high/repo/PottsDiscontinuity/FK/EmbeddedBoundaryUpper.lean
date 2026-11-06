/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import Mathlib.Tactic
public import PottsDiscontinuity.FK.ConditionalEmbeddedBoundaryUpper
public import PottsDiscontinuity.FK.EmbeddedMarginalLaw

public section

namespace PottsDiscontinuity.FK

open scoped BigOperators
noncomputable section

variable {V W : Type*} [Finite V] [Finite W]
  (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W)
  (hGH : G.map f ≤ H)

local instance embeddedUpperOuterEdgeFintype : Fintype H.edgeSet := Fintype.ofFinite _
local instance embeddedUpperOuterEdgeDecidableEq : DecidableEq H.edgeSet := Classical.decEq _

section
variable (q : Parameters)
/-- An increasing event read from the exact embedded restriction has outer
probability at most its inner FK probability whenever every frozen outside
state induces a boundary partition dominated by the specified inner boundary. -/
theorem embeddedConfigurationRestriction_preimage_measure_le_of_frozen_partition
    (ξ : BoundaryCondition W) (η : BoundaryCondition V)
    (S : Set (Configuration G)) (hS : IsUpperSet S)
    (hpart : ∀ K : RemovedConfiguration H
        (subgraphRemovedEdges (G.map f) H),
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition ≤
        η.partition) :
    (measure H q ξ
      {A | embeddedConfigurationRestriction G H f hGH A ∈ S}).toReal ≤
      (measure G q η S).toReal := by
  let R := subgraphRemovedEdges (G.map f) H
  let restr :=
    embeddedConfigurationRestriction G H f hGH
  let marg := frozenMarginalLaw q ξ R
  let cond : RemovedConfiguration H R → PMF (Configuration G) := fun K =>
    law G q (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val))
  let mix := (law H q ξ).map restr
  let T := {A | restr A ∈ S}
  let ind := S.indicator (fun _ => (1 : ℝ))
  have hmix : mix = marg.bind cond := by
    simpa [mix, marg, cond, R, restr] using
      law_embeddedConfigurationRestriction_eq_bind_frozenMarginal
        G H f hGH q ξ
  have houter :
      (measure H q ξ T).toReal = FiniteProbability.expectation mix ind := by
    calc
      (measure H q ξ T).toReal =
          FiniteProbability.expectation (law H q ξ)
            (T.indicator (fun _ => (1 : ℝ))) :=
              fkLaw_measure_toReal_eq_expectation q ξ T
      _ = FiniteProbability.expectation (law H q ξ)
          (fun A => ind (restr A)) := by
            rfl
      _ = FiniteProbability.expectation mix ind := by
            simpa [mix, ind] using
              (FiniteProbability.expectation_map (law H q ξ) restr ind).symm
  have hconditional : ∀ K : RemovedConfiguration H R,
      FiniteProbability.expectation (cond K) ind ≤
        FiniteProbability.expectation (law G q η) ind := by
    intro K
    have hbound := filteredConditionalEmbeddedEvent_measure_le_boundary
      G H f hGH q ξ K η (hpart K) S hS
    have hfilter := law_filter_frozen_map_embeddedRestriction
      G H f hGH q ξ K
    have hmeasure :
        (measure G q
          (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)) S).toReal ≤
          (measure G q η S).toReal := by
      simpa only [measure, ← hfilter] using hbound
    rw [← fkLaw_measure_toReal_eq_expectation q
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)) S,
      ← fkLaw_measure_toReal_eq_expectation q η S]
    omega
  have havg := FiniteProbability.expectation_bind_le marg cond ind
    (FiniteProbability.expectation (law G q η) ind) hconditional
  have hinner :
      FiniteProbability.expectation (law G q η) ind =
        (measure G q η S).toReal := by
    grind [fkLaw_measure_toReal_eq_expectation]
  simpa [T] using calc
    (measure H q ξ T).toReal = FiniteProbability.expectation mix ind := houter
    _ = FiniteProbability.expectation (marg.bind cond) ind := by
      grind
    _ = FiniteProbability.expectation marg (fun K =>
          FiniteProbability.expectation (cond K) ind) :=
            FiniteProbability.expectation_bind marg cond ind
    _ ≤ FiniteProbability.expectation (law G q η) ind := by
          simpa only [FiniteProbability.expectation_bind] using havg
    _ = (measure G q η S).toReal := hinner
end

end
end PottsDiscontinuity.FK
