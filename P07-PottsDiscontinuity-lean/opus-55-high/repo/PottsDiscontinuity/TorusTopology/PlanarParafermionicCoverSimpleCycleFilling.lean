/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceChainUniqueness
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceOrientedBoundary

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

section
variable {n : ℕ}
theorem coverCycle_spanningCoe_even_degree {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    ∀ v : ParafermionicCoverBoxVertex n,
      Even ((p.toSubgraph.spanningCoe).neighborSet v).ncard := by
  classical
  let H := p.toSubgraph.spanningCoe
  intro v
  let q := p.transfer H (by
    aesop)
  have hqtrail : q.IsTrail := by
    simpa [q] using hp.isTrail
  have hqedges : q.edgeSet = H.edgeSet := by
    aesop
  have heuler := hqtrail.isEulerian_iff.mpr hqedges
  have hdegree : Even (H.degree v) :=
    (heuler.even_degree_iff).2 (by simp)
  rw [← H.card_neighborSet_eq_degree, Set.fintypeCard_eq_ncard] at hdegree
  exact hdegree

theorem parafermionicCoverSimpleCycle_unique_face_filling (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    ∃! S : Finset (ParafermionicCoverFiniteFaceTopIndex n),
      (∃ L : List (ParafermionicCoverFiniteFaceTopIndex n),
        L.Nodup ∧ L.toFinset = S ∧
          faceSymmDiffList
            (fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) L =
              p.toSubgraph.spanningCoe) ∧
      S.Nonempty ∧
      ∀ a b : ParafermionicCoverBoxVertex n,
        parafermionicCoverFaceBoundaryCoefficient S a b ≠ 0 ↔
          s(a,b) ∈ p.edges := by
  let H := p.toSubgraph.spanningCoe
  have hle :=
    p.toSubgraph.spanningCoe_le
  have heven : ∀ v : ParafermionicCoverBoxVertex n, Even (H.neighborSet v).ncard := by
    grind [coverCycle_spanningCoe_even_degree]
  obtain ⟨S, hS, hSunique⟩ :=
    parafermionicCoverFiniteFaceChain_unique_representation hn H hle heven
  obtain ⟨L, hL, hLS, hLH⟩ := hS
  have hHne : H ≠ ⊥ := by
    have hadj : H.Adj u p.snd :=
      p.toSubgraph_adj_snd hp.not_nil
    grind
  have hLne : L ≠ [] := by
    intro hnil
    subst L
    tauto
  have hSnonempty : S.Nonempty := by
    by_contra h
    have hLnil : L = [] := by
      cases L with
      | nil => rfl
      | cons a rest =>
        have ha : a ∈ (a :: rest).toFinset := by simp
        grind
    grind
  have hcoeff (a b : ParafermionicCoverBoxVertex n) :
      parafermionicCoverFaceBoundaryCoefficient S a b ≠ 0 ↔ s(a,b) ∈ p.edges := by
    have hboundary := parafermionicCoverFaceBoundaryCoefficient_ne_zero_iff
      S L hL hLS a b
    rw [hLH] at hboundary
    rw [SimpleGraph.Subgraph.edgeSet_spanningCoe,
      SimpleGraph.Walk.edgeSet_toSubgraph] at hboundary
    tauto
  refine ⟨S, ⟨⟨L, hL, hLS, hLH⟩, hSnonempty, hcoeff⟩, ?_⟩
  intro T hT
  have hTrep := hT.1
  exact (hSunique T hTrep)
end

end PottsDiscontinuity.TorusTopology.Planar.Medial

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

section
variable {n : ℕ} (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n} (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle)
noncomputable def parafermionicCoverSimpleCycleFillingSet  :
    Finset (ParafermionicCoverFiniteFaceTopIndex n) :=
  Classical.choose (parafermionicCoverSimpleCycle_unique_face_filling hn p hp).exists

theorem parafermionicCoverSimpleCycleFillingSet_spec  :
    (∃ L : List (ParafermionicCoverFiniteFaceTopIndex n),
      L.Nodup ∧ L.toFinset = parafermionicCoverSimpleCycleFillingSet hn p hp ∧
        faceSymmDiffList
          (fun i => parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2) L =
            p.toSubgraph.spanningCoe) ∧
    (parafermionicCoverSimpleCycleFillingSet hn p hp).Nonempty ∧
    ∀ a b : ParafermionicCoverBoxVertex n,
      parafermionicCoverFaceBoundaryCoefficient
          (parafermionicCoverSimpleCycleFillingSet hn p hp) a b ≠ 0 ↔
        s(a,b) ∈ p.edges :=
  Classical.choose_spec
    (parafermionicCoverSimpleCycle_unique_face_filling hn p hp).exists
end

end PottsDiscontinuity.TorusTopology.Planar.Medial
