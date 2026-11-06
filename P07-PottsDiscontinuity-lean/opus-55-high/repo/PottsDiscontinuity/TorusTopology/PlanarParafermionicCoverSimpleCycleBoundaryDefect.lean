/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSimpleCycleEulerDefect
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverInteriorCorners
public import Mathlib.Tactic

public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open Classical

/-- The Euler defect is supported on the actual selected boundary: summing
`2 - incidence` over that boundary gives four. -/
theorem parafermionicCoverSimpleCycleFilling_boundary_defect
    {n : ℕ} (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    Finset.sum
      (Finset.univ.filter (fun v : ParafermionicCoverBoxVertex n =>
        v ∈ (parafermionicCoverFiniteFaceSetBoundaryGraph
          (parafermionicCoverSimpleCycleFillingSet hn p hp)).support))
      (fun v => (2 : ℤ) -
        ((parafermionicCoverFiniteFaceSelectedIncidentVertices
          (parafermionicCoverSimpleCycleFillingSet hn p hp) v).card : ℤ)) = 4 := by
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  let C := parafermionicCoverFiniteFaceUnionCarrier S
  let B := parafermionicCoverFiniteFaceSetBoundaryGraph S
  let I := parafermionicCoverFiniteFaceSelectedIncidentVertices S
  let Cverts := Finset.univ.filter fun v : ParafermionicCoverBoxVertex n => v ∈ C
  let Bverts := Finset.univ.filter fun v : ParafermionicCoverBoxVertex n => v ∈ B.support
  have hboundarySubset : B.support ⊆ C := by
    simpa [B, S] using
      parafermionicCoverSimpleCycleFillingSet_boundarySupport_subset_unionCarrier hn p hp
  have hfilter : Cverts.filter (fun v => v ∈ B.support) = Bverts := by
    grind
  have hEuler := parafermionicCoverSimpleCycleFilling_euler_defect hn p hp
  have hEuler' :
      Finset.sum Cverts (fun v =>
        (4 : ℤ) - ((I v).card : ℤ) -
          (if v ∈ B.support then (2 : ℤ) else 0)) = 4 := by
    omega
  have hpoint (v : ParafermionicCoverBoxVertex n) (hv : v ∈ Cverts) :
      (4 : ℤ) - ((I v).card : ℤ) -
          (if v ∈ B.support then (2 : ℤ) else 0) =
        if v ∈ B.support then (2 : ℤ) - ((I v).card : ℤ) else 0 := by
    by_cases hB : v ∈ B.support
    · grind
    · have hInterior :=
        parafermionicCoverFiniteFaceSelectedCorners_eq_univ_of_mem_unionCarrier_not_support
          S v (by grind) hB
      grind
  have hsumPoint :
      Finset.sum Cverts (fun v =>
        (4 : ℤ) - ((I v).card : ℤ) -
          (if v ∈ B.support then (2 : ℤ) else 0)) =
      Finset.sum Cverts (fun v =>
        if v ∈ B.support then (2 : ℤ) - ((I v).card : ℤ) else 0) := by
    apply Finset.sum_congr rfl
    omega
  have hsumBoundary :
      Finset.sum Cverts (fun v =>
        if v ∈ B.support then (2 : ℤ) - ((I v).card : ℤ) else 0) =
      Finset.sum Bverts (fun v => (2 : ℤ) - ((I v).card : ℤ)) := by
    calc
      _ = Finset.sum (Cverts.filter (fun v => v ∈ B.support))
          (fun v => (2 : ℤ) - ((I v).card : ℤ)) := by
        rw [← Finset.sum_filter]
      _ = _ := by grind
  calc
    _ = Finset.sum Cverts (fun v =>
        if v ∈ B.support then (2 : ℤ) - ((I v).card : ℤ) else 0) :=
      hsumBoundary.symm
    _ = Finset.sum Cverts (fun v =>
        (4 : ℤ) - ((I v).card : ℤ) -
          (if v ∈ B.support then (2 : ℤ) else 0)) := hsumPoint.symm
    _ = 4 := hEuler'

end PottsDiscontinuity.TorusTopology.Planar.Medial
