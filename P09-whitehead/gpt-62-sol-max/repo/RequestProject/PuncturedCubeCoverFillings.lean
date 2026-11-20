module

public import RequestProject.OrdinaryTruncatedBoundary
public import RequestProject.NerveThreeLegContraction

@[expose] public section

namespace FiniteChains.Davis
open RACG Mirror Comb Nerve
variable {V : Type} [DecidableEq V]

private theorem puncturedCube_fills (t : Cube V) (j : V) (b z : CubeCoord)
    (hb : b ≠ CubeCoord.free) (hz : z ≠ CubeCoord.free) (hbz : b ≠ z)
    (ht : t j = CubeCoord.free) :
    ∀ c ∈ Inc (PuncturedCubeFace t j b), Nerve.bdry c = 0 →
      ∃ y ∈ Inc (PuncturedCubeFace t j b), Nerve.bdry y = c :=
  exists_bdry_eq_of_cycle_threeLeg _ _ (punctureOpposite t j b z hz hbz ht)
    (punctureOpen_monotone t j b z hb hz hbz ht)
    (punctureProject_monotone t j b z hz hbz ht)
    (Or.inl fun c => coordinate_face_open j z c.1)
    (Or.inr fun c => coordinate_fix_face_open j z c.1)
    (Or.inl fun c => coordinateFix_face_opposite_facet j z c.2.1)

theorem ordinaryTruncatedBoundary_acyclic [Fintype V] {A : CommRel V}
    {L : ASC V} {s t : QOld A} (ht : t.1.sgn ≠ 0)
    (hi : qCubeToCoordinate t.1 ∈ spineInc L (Sum.inl (qCubeToCoordinate s.1))) :
    ∀ c ∈ Inc (OldPuncturedBoundary s t), Nerve.bdry c = 0 →
      ∃ y ∈ Inc (OldPuncturedBoundary s t), Nerve.bdry y = c := by
  obtain ⟨j, b, hb, htj, hs⟩ := exists_facet_coordinates_of_inc s t hi
  apply exists_bdry_eq_of_cycle_of_orderIso (ordinaryTruncatedBoundaryOrderIso ht j b hs)
  cases b with
  | free => exact (hb rfl).elim
  | pos => exact puncturedCube_fills _ j .pos .neg hb (by decide) (by decide) htj
  | neg => exact puncturedCube_fills _ j .neg .pos hb (by decide) (by decide) htj

end FiniteChains.Davis
