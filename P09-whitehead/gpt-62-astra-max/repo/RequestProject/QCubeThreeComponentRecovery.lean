module

public import RequestProject.QCubeThreeOrientationSubdivision
public import RequestProject.QCubeThreeBaseCycles

@[expose] public section

/-! Recovery of the actual cubical boundary of an isolated strict three-cube component. -/
open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

theorem qCube_three_component_boundary_scalar (c : QThreeCube A)
    (y : StrictOrdTet (QCube A) →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3)
    (hb : ∀ s ∈ (strictOrdBoundary3 y).support, s.1.2.2.spx.card ≤ 2) :
    ∃ k : ℤ, strictOrdBoundary3 (y.filter (fun t => t.1.2.2.2 = c.1)) =
      k • qSquareChainSubdivision (qThreeCubicalFaceBoundary c) := by
  obtain ⟨r, hcycle, hsupport, he⟩ := qCube_three_component_facet_boundary c.1 c.2 y hy hb
  have hr : ∀ s ∈ r.support, s.1 < c.1 := by
    intro s hmem
    obtain ⟨a, ha, h0 | h1⟩ := hsupport s hmem
    · rw [h0]
      apply qCubeFacet_lt <;> assumption
    · rw [h1]
      apply qCubeFacet_lt <;> assumption
  obtain ⟨k, hk⟩ := qThreeFacetCycle_scalar c r hr
    ((qSquareCubicalBoundary_zero_iff r).mpr hcycle)
  refine ⟨-k, ?_⟩
  rw [hk, map_smul] at he
  simpa only [neg_neg, neg_smul] using (congrArg Neg.neg he.symm)

end FiniteChains.Davis
