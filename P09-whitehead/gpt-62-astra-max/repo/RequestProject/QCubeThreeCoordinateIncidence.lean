module

public import RequestProject.QCubeCoordinateBoundaryChain
public import RequestProject.QCubeCubicalThreeBoundary

@[expose] public section

/-! The six-face coefficient orientation agrees with the collapse's actual incidences. -/

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [Fintype V] [LinearOrder V] {A : CommRel V}

variable (c : QThreeCube A)

theorem qThreeFace_coordinate_boundary_coefficient (i : Fin 3 × ZMod 2) :
    cubeBdry (qCubeToCoordinate c.1)
      (Sum.inl (qCubeToCoordinate
        (qThreeFaceSquare c i).1)) = threeFacetOrientation i := by
  change cubeBdry _
    (Sum.inl (qCubeToCoordinate (qCubeFacet c.1 (c.dirs i.1) i.2))) = _
  rw [cubeBdry_actual_facet c.1 _ (c.dirs i.1).2 i.2]
  obtain ⟨hw0, hv0, hu0⟩ := threeFacet_incidence_zero c.1 c.mid_lt c.lo_lt c.directions
  obtain ⟨hw1, hv1, hu1⟩ := threeFacet_incidence_one c.1 c.mid_lt c.lo_lt c.directions
  obtain ⟨e, s⟩ := i
  fin_cases e <;> fin_cases s <;>
    norm_num [threeFacetOrientation, fixedCoordinateSign, Fin.ext_iff] <;> first | exact hw0 | exact hw1 | exact hv0 | exact hv1 | exact hu0 | exact hu1

/-- Every coefficient of the actual indexed oriented face chain is the collapse's
ordinary boundary coefficient. -/
theorem qThreeOrientedFaces_coordinate_apply (g : Cube V) :
    Finsupp.mapDomain (fun i => qCubeToCoordinate
      (qThreeFaceSquare c i).1) threeOrientedFaces g =
      cubeBdry (qCubeToCoordinate c.1) (Sum.inl g) := by
  classical
  let f := fun i => qCubeToCoordinate
    (qThreeFaceSquare c i).1
  have hinj : Function.Injective f := by
    intro i j h
    grind [qThreeFaceSquare_injective, qCubeToCoordinate_injective]
  change Finsupp.mapDomain f threeOrientedFaces g = _
  by_cases hg : g ∈ Set.range f
  · obtain ⟨i, rfl⟩ := hg
    rw [Finsupp.mapDomain_apply_of_injective hinj, threeOrientedFaces_apply]
    grind [qThreeFace_coordinate_boundary_coefficient]
  · have hzero : cubeBdry (qCubeToCoordinate c.1) (Sum.inl g) = 0 := by
      apply cubeBdry_zero_off_actual_facets
      intro a ha s he
      obtain ⟨i, hi⟩ := c.dirs.surjective ⟨a, ha⟩
      apply hg; refine ⟨(i, s), ?_⟩
      change qCubeToCoordinate (qCubeFacet c.1 (c.dirs i) s) = _
      rw [hi]; exact he.symm
    simp_all [Finsupp.mapDomain_notin_range, hzero]

/-- Coordinate transport of the actual six-facet boundary is the finite ordinary
coordinate boundary used by the collapse. -/
theorem qThreeCubicalFaceBoundary_coordinate (c : QThreeCube A) :
    Finsupp.lmapDomain ℤ ℤ (fun s : QSquare A => qCubeToCoordinate s.1)
      (qThreeCubicalFaceBoundary c) = qCubeCoordinateFacetChain c.1 := by
  change Finsupp.mapDomain _
    (Finsupp.mapDomain _ threeOrientedFaces) = _
  rw [← Finsupp.mapDomain_comp]
  grind [qCubeCoordinateFacetChain_apply, qThreeOrientedFaces_coordinate_apply]

/-- Coordinate boundary naturality for all genuine finite cubical three-chains. -/
theorem qThreeCubicalBoundary_coordinate (r : QThreeCube A →₀ ℤ) :
    Finsupp.lmapDomain ℤ ℤ (fun s : QSquare A => qCubeToCoordinate s.1)
      (qThreeCubicalBoundary r) =
      Finsupp.linearCombination ℤ (fun c : QThreeCube A => qCubeCoordinateFacetChain c.1) r := by
  induction r using Finsupp.induction_linear with
  | zero => simp
  | add r s hr hs => simp [map_add, hr, hs]
  | single c n =>
      rw [qThreeCubicalBoundary, Finsupp.linearCombination_single, map_smul,
        qThreeCubicalFaceBoundary_coordinate, Finsupp.linearCombination_single]

/-- Ordinary coordinate transport of every dimension-bounded strict three-boundary is
an actual finite combination of the cube boundaries used by the collapse. -/
theorem qCube_three_coordinate_boundary_reconstruction (y : StrictOrdTet (QCube A) →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3)
    (hb : ∀ s ∈ (strictOrdBoundary3 y).support, s.1.2.2.spx.card ≤ 2) :
    ∃ r : QThreeCube A →₀ ℤ,
      Finsupp.lmapDomain ℤ ℤ (fun s : QSquare A => qCubeToCoordinate s.1)
        (qSquareCycleCoefficients (strictOrdBoundary3 y)) =
      Finsupp.linearCombination ℤ (fun c : QThreeCube A => qCubeCoordinateFacetChain c.1) r := by
  obtain ⟨r, hr⟩ := qCube_three_boundary_reconstruction y hy hb
  exact ⟨r, by rw [← hr, qSquare_coefficients_subdivision, qThreeCubicalBoundary_coordinate]⟩

end FiniteChains.Davis
