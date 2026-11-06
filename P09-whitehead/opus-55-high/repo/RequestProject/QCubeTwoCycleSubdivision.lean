import RequestProject.QCubeSquareCycleRecovery
import RequestProject.QCubeSquareChainBoundary
import RequestProject.Tac


/-! Global recovery of actual two-dimensional strict cycles as finite cubical square chains. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V C : Type} [DecidableEq V] {A : CommRel V}
  (cell : C → QCube A) (left right : C → V)
  (hne : ∀ i, left i ≠ right i) (hspx : ∀ i, (cell i).spx = {left i, right i})

def squareCoefficientFlag (i : C) :=
  squareFlag _ _ _ (hne i) (hspx i) (false, 0, false)

theorem squareCoefficientFlag_injective (hcell : Function.Injective cell) :
    Function.Injective (squareCoefficientFlag cell left right hne hspx) := by
  intro i j h
  have ht := congrArg (·.1.2.2) h
  tauto

noncomputable def squareCycleCoefficients (hcell : Function.Injective cell) :
    ((strictOrderCx (QCube A)).F →₀ ℤ) →ₗ[ℤ] (C →₀ ℤ) :=
  Finsupp.lcomapDomain _
    (squareCoefficientFlag_injective cell left right hne hspx hcell)

theorem squareChainSubdivision_off_cells r
    t (ht : ∀ i, t.1.2.2 ≠ cell i) :
    squareChainSubdivision cell left right hne hspx r t = 0 := by
  lin_ind r i n =>
      rw [squareChainSubdivision, Finsupp.linearCombination_single, Finsupp.smul_apply,
        cubeSquareSubdivision_eq_zero_off_top _ _ _ _ _ _ (ht i), smul_zero]

/-- Every actual strict two-cycle of dimension at most two is the subdivision of its
finite recovered cubical coefficient chain. -/
theorem cubeTwoCycle_is_squareSubdivision hcell
    (hcover : ∀ c, c.spx.card = 2 → ∃ i, cell i = c)
    z
    (hz : ∀ t ∈ z.support, t.1.2.2.spx.card ≤ 2)
    (hcycle : Comb.bdry2 (strictOrderCx (QCube A)) z = 0) :
    z = squareChainSubdivision cell left right hne hspx
      (squareCycleCoefficients cell left right hne hspx hcell z) := by
  classical
  ext t
  by_cases hdim : t.1.2.2.spx.card = 2
  · cases' hcover t.1.2.2 hdim with i hi
    have hti := hi.symm
    have hl := congrArg (· t)
      (cubeTwoCycle_square_component _ _ _ (hne i) (hspx i)
        z hz hcycle)
    have hr := congrArg (· t)
      (squareChainSubdivision_filter_top cell left right hne hspx hcell
        (squareCycleCoefficients cell left right hne hspx hcell z) i)
    simp [Finsupp.filter_apply, hti, Finsupp.smul_apply] at hl hr
    exact hl.trans hr.symm
  · have hzt : z t = 0 := by
      by_contra hzt
      exact hdim (qCube_triangle_dimensions t (by simp_all)).2.2
    rw [hzt]
    symm
    apply squareChainSubdivision_off_cells
    grind

/-- The recovered cubical coefficients are genuine cycles for the facet boundary map. -/
theorem cubeTwoCycle_coefficients_cycle hcell
    (hcover : ∀ c, c.spx.card = 2 → ∃ i, cell i = c)
    z
    (hz : ∀ t ∈ z.support, t.1.2.2.spx.card ≤ 2)
    (hcycle : Comb.bdry2 (strictOrderCx (QCube A)) z = 0) :
    squareChainEdgeBoundary cell left right hne hspx
      (squareCycleCoefficients cell left right hne hspx hcell z) = 0 := by
  rw [← squareChainSubdivision_boundary,
    ← cubeTwoCycle_is_squareSubdivision cell left right hne hspx hcell hcover z hz hcycle]
  exact hcycle
