module

public import RequestProject.QCubeTruncatedBoundaryCollapse
public import RequestProject.FinsuppBasis

@[expose] public section

/-! Actual finite three-cube coefficients, ordinary boundary and positive cut coefficients. -/

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [Fintype V] [LinearOrder V] {A : CommRel V}

noncomputable def qThreeCoordinateChain : (QThreeCube A →₀ ℤ) →ₗ[ℤ] (Cube V →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun c  => qCubeToCoordinate c.1)

omit [LinearOrder V] in
theorem qThreeCutFaceChain_apply (r : QThreeCube A →₀ ℤ) (σ : Finset V) :
    qThreeCutFaceChain r σ = qThreeCoordinateChain r (posCube σ) := by
  classical
  finsupp_basis r
  intro c
  rw [qThreeCutFaceChain, Finsupp.linearCombination_single]
  simp only [qThreeCoordinateChain, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  by_cases hsgn : c.1.sgn = 0
  · by_cases hσ : σ = c.1.spx
    · subst σ
      simp [hsgn, Finsupp.single_apply, qCube_coordinate_pos_iff, eq_comm]
    · simp [hsgn, qCube_coordinate_pos_iff, hσ]
  · simp [hsgn, qCube_coordinate_pos_iff]

/-- The finite coordinate three-chain has precisely the ordinary boundary supplied by
its actual six-facet chains. -/
theorem qThreeCoordinateChain_boundary (r : QThreeCube A →₀ ℤ) (g : Cube V) :
    bdry (qThreeCoordinateChain r) g =
      Finsupp.linearCombination ℤ
        (fun c : QThreeCube A => qCubeCoordinateFacetChain c.1) r g := by
  classical
  finsupp_basis r [bdry]
  intro c
  rw [Finsupp.linearCombination_single, one_smul, qCubeCoordinateFacetChain_apply]
  simp only [qThreeCoordinateChain, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    bdry, cubeBdry_inl, Finsupp.single_apply, eq_comm]

/-- Vanishing of ordinary positive-square boundary coefficients makes the actual cut
coefficient chain a simplicial cycle. -/
theorem qThreeCutFaceChain_cycle (r : QThreeCube A →₀ ℤ)
    (hpos : ∀ σ : Finset V,
      Finsupp.linearCombination ℤ
        (fun c : QThreeCube A => qCubeCoordinateFacetChain c.1) r (posCube σ) = 0) :
    simpBdry (qThreeCutFaceChain r) = 0 := by
  funext σ
  have he := qThreeCoordinateChain_boundary r (posCube σ)
  simp_all [hpos σ, bdry_posCube, simpBdry, qThreeCutFaceChain_apply]

omit [LinearOrder V] in
/-- Nonzero cut coefficients occur only on actual three-vertex simplices. -/
theorem qThreeCutFaceChain_support (r : QThreeCube A →₀ ℤ) (σ : Finset V)
    (hσ : qThreeCutFaceChain r σ ≠ 0) : σ.card = 3 ∧ IsSimplex A σ := by
  classical
  rw [qThreeCutFaceChain_apply] at hσ
  have hmem := Finsupp.mem_support_iff.mpr hσ
  change posCube σ ∈
    (Finsupp.mapDomain (fun c : QThreeCube A => qCubeToCoordinate c.1) r).support at hmem
  obtain ⟨c, _, he⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hmem)
  have hs : c.1.spx = σ := by
    have h := congrArg freeSet he
    simpa using h
  rw [← hs]
  exact ⟨c.2, c.1.isSimplex⟩

end FiniteChains.Davis
