import RequestProject.QCubeThreeOrientationSubdivision
import RequestProject.QCubeThreeBaseCycles
import RequestProject.Tac


/-! Recovery of the actual cubical boundary of an isolated strict three-cube component. -/
open scoped Classical
bwd

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

theorem qCube_three_component_boundary_scalar c u v w
    huv (hvw : w < v) hs
    (y : StrictOrdTet (QCube A) →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3)
    (hb : ∀ s ∈ (strictOrdBoundary3 y).support, s.1.2.2.spx.card ≤ 2) :
    ∃ k : ℤ, strictOrdBoundary3 (y.filter (·.1.2.2.2 = c)) =
      k • cubeThreeSquareBoundary c u v w (Ne.symm huv.ne)
        (Ne.symm (hvw.trans huv).ne) (Ne.symm hvw.ne) hs := by
  obtain ⟨r, hcycle, hsupport, he⟩ := qCube_three_component_facet_boundary c
    (by grind) y hy hb
  have hr : ∀ s ∈ r.support, s.1 < c := by
    intro s hmem
    obtain ⟨a, ha, h0 | h1⟩ := hsupport s hmem
    · rw [h0]
      exact qCubeFacet_lt c a 0 ha
    · rw [h1]
      exact qCubeFacet_lt c a 1 ha
  obtain ⟨k, hk⟩ := qThreeFacetCycle_subdivision c u v w huv hvw hs r hr
    ((qSquareCubicalBoundary_zero_iff r).mpr hcycle)
  refine ⟨-k, ?_⟩
  simp_all
