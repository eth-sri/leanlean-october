/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceSetVertexIncidence
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSimpleCycleBoundaryCount
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSimpleCycleFillingEuler

public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open SimpleGraph
open Classical

theorem parafermionicCoverSimpleCycleFilling_euler_defect
    {n : ℕ} (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    Finset.sum (Finset.univ.filter (fun x : ParafermionicCoverBoxVertex n =>
        x ∈ parafermionicCoverFiniteFaceUnionCarrier
          (parafermionicCoverSimpleCycleFillingSet hn p hp))) (fun v =>
      (4 : ℤ) -
        ((parafermionicCoverFiniteFaceSelectedIncidentVertices
          (parafermionicCoverSimpleCycleFillingSet hn p hp) v).card : ℤ) -
        (if v ∈ (parafermionicCoverFiniteFaceSetBoundaryGraph
            (parafermionicCoverSimpleCycleFillingSet hn p hp)).support then (2 : ℤ) else 0)) = 4 := by
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  let C := parafermionicCoverFiniteFaceUnionCarrier S
  let B := parafermionicCoverFiniteFaceSetBoundaryGraph S
  let I := parafermionicCoverFiniteFaceSelectedIncidentVertices S
  let Cverts := Finset.univ.filter fun v : ParafermionicCoverBoxVertex n => v ∈ C
  have hincTotal : ∑ v : ParafermionicCoverBoxVertex n, (I v).card = 4 * S.card := by
    simpa using parafermionicCoverFiniteFaceSetVertexIncidence_count S
  have hincZero (v : ParafermionicCoverBoxVertex n) (hv : v ∉ C) : (I v).card = 0 := by
    by_contra hne
    exact hv ((parafermionicCoverFiniteFaceUnionCarrier_iff_incidentVertices_nonempty S v).mpr (Finset.card_pos.mp (Nat.pos_of_ne_zero hne)))
  have hinc : ∑ v ∈ Cverts, (I v).card = 4 * S.card := by
    calc
      _ = ∑ v : ParafermionicCoverBoxVertex n, (I v).card := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        grind
      _ = 4 * S.card := hincTotal
  have hCcard : Cverts.card = Nat.card C := by
    simp [Cverts, Nat.card_eq_fintype_card]
  have hboundarySubset : B.support ⊆ C := by
    simpa [B, S] using
      parafermionicCoverSimpleCycleFillingSet_boundarySupport_subset_unionCarrier hn p hp
  have hboundaryCards : Nat.card B.support =
      (parafermionicCoverFiniteFaceSetBoundaryEdges S).card := by
    rw [show Nat.card B.support = p.length by
      simpa [B, S] using
        parafermionicCoverSimpleCycleFillingSet_boundarySupport_card_eq_length hn p hp,
      parafermionicCoverSimpleCycleFillingSet_boundaryEdges_card_eq_length hn p hp]
  have hfilter : Cverts.filter (fun v => v ∈ B.support) =
      Finset.univ.filter (fun v : ParafermionicCoverBoxVertex n => v ∈ B.support) := by
    grind
  have hfilterCard : (Cverts.filter (fun v => v ∈ B.support)).card = Nat.card B.support := by
    rw [hfilter, Nat.card_eq_fintype_card]
    simp
  have hboundaryIndicator :
      ∑ v ∈ Cverts, (if v ∈ B.support then (1 : ℤ) else 0) =
        (Nat.card B.support : ℤ) := by
    rw [Finset.sum_boole, hfilterCard]
  have hincZ : ∑ v ∈ Cverts, ((I v).card : ℤ) =
      (4 : ℤ) * (S.card : ℤ) := by
    linarith
  have hEulerNat := parafermionicCoverSimpleCycleFilling_euler_count hn p hp
  have hEuler : (Nat.card C : ℤ) + (S.card : ℤ) =
      ((parafermionicCoverFiniteFaceSetEdgeSupport S).card : ℤ) + 1 := by
    linarith
  have hEdgeNat := parafermionicCoverFiniteFaceSetEdgeCount S
  have hEdge : (4 : ℤ) * (S.card : ℤ) +
      (parafermionicCoverFiniteFaceSetBoundaryEdges S).card =
      2 * (parafermionicCoverFiniteFaceSetEdgeSupport S).card := by
    omega
  have hBoundary : (Nat.card B.support : ℤ) =
      (parafermionicCoverFiniteFaceSetBoundaryEdges S).card := by
    omega
  have hnumeric : (4 : ℤ) * (Nat.card C : ℤ) -
      4 * (S.card : ℤ) - 2 * (Nat.card B.support : ℤ) = 4 := by
    omega
  change ∑ v ∈ Cverts,
      ((4 : ℤ) - ((I v).card : ℤ) -
        (if v ∈ B.support then (2 : ℤ) else 0)) = 4
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  have hconst : ∑ v ∈ Cverts, (4 : ℤ) = 4 * (Nat.card C : ℤ) := by
    rw [Finset.sum_const, nsmul_eq_mul, hCcard]
    ring
  have htwice :
      Finset.sum Cverts (fun v => if v ∈ B.support then (2 : ℤ) else 0) =
        2 * (Nat.card B.support : ℤ) := by
    calc
      _ = Finset.sum Cverts (fun v =>
          2 * (if v ∈ B.support then (1 : ℤ) else 0)) := by
        apply Finset.sum_congr rfl
        grind
      _ = 2 * Finset.sum Cverts (fun v =>
          if v ∈ B.support then (1 : ℤ) else 0) := by rw [Finset.mul_sum]
      _ = 2 * (Nat.card B.support : ℤ) := by omega
  rw [hconst, hincZ, htwice]
  omega

end PottsDiscontinuity.TorusTopology.Planar.Medial
