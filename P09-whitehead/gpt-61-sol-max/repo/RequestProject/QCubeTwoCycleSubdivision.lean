import Mathlib.Tactic

import RequestProject.QCubeSquareCycleRecovery
import RequestProject.QCubeSquareChainBoundary

/-! Global recovery of actual two-dimensional strict cycles as finite cubical square chains. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V C : Type} [DecidableEq V] {A : CommRel V}
  (cell : C → QCube A) (left right : C → V)
  (hne : ∀ i, left i ≠ right i) (hspx : ∀ i, (cell i).spx = {left i, right i})

def squareCoefficientFlag (i : C)  :=
  squareFlag (cell i) (left i) (right i) (hne i) (hspx i) (false, 0, false)

variable (hcell : Function.Injective cell)
include hcell in
theorem squareCoefficientFlag_injective  :
    Function.Injective (squareCoefficientFlag cell left right hne hspx) := by
  intro i j h
  have ht := congrArg (fun t : (strictOrderCx (QCube A)).F => t.1.2.2) h
  simp [squareCoefficientFlag] at ht
  exact hcell ht

include hcell in
noncomputable def squareCycleCoefficients  :
    ((strictOrderCx (QCube A)).F →₀ ℤ) →ₗ[ℤ] (C →₀ ℤ) :=
  Finsupp.lcomapDomain (squareCoefficientFlag cell left right hne hspx)
    (squareCoefficientFlag_injective cell left right hne hspx hcell)

theorem squareChainSubdivision_off_cells (r : C →₀ ℤ)
    (t : (strictOrderCx (QCube A)).F) (ht : ∀ i, t.1.2.2 ≠ cell i) :
    squareChainSubdivision cell left right hne hspx r t = 0 := by
  induction r using Finsupp.induction_linear <;> simp_all [squareChainSubdivision, cubeSquareSubdivision_eq_zero_off_top]

variable (hcover : ∀ c : QCube A, c.spx.card = 2 → ∃ i, cell i = c)
include hcover in
include hcell in
/-- Every actual strict two-cycle of dimension at most two is the subdivision of its
finite recovered cubical coefficient chain. -/
theorem cubeTwoCycle_is_squareSubdivision 
    
    (z : (strictOrderCx (QCube A)).F →₀ ℤ)
    (hz : ∀ t ∈ z.support, t.1.2.2.spx.card ≤ 2)
    (hcycle : Comb.bdry2 (strictOrderCx (QCube A)) z = 0) :
    z = squareChainSubdivision cell left right hne hspx
      (squareCycleCoefficients cell left right hne hspx hcell z) := by
  classical
  ext t
  by_cases hdim : t.1.2.2.spx.card = 2
  · obtain ⟨i, hi⟩ := hcover t.1.2.2 hdim
    have hti  := hi.symm
    have hl := congrArg (fun w : (strictOrderCx (QCube A)).F →₀ ℤ => w t)
      (cubeTwoCycle_square_component (cell i) (left i) (right i) (hne i) (hspx i)
        z hz hcycle)
    have hr := congrArg (fun w : (strictOrderCx (QCube A)).F →₀ ℤ => w t)
      (squareChainSubdivision_filter_top cell left right hne hspx hcell
        (squareCycleCoefficients cell left right hne hspx hcell z) i)
    simp only [Finsupp.filter_apply, hti, Finsupp.smul_apply] at hl hr
    exact hl.trans hr.symm
  · grind [FiniteChains.Davis.qCube_triangle_dimensions, FiniteChains.Davis.squareChainSubdivision_off_cells]

include hcover in
include hcell in
/-- The recovered cubical coefficients are genuine cycles for the facet boundary map. -/
theorem cubeTwoCycle_coefficients_cycle 
    
    (z : (strictOrderCx (QCube A)).F →₀ ℤ)
    (hz : ∀ t ∈ z.support, t.1.2.2.spx.card ≤ 2)
    (hcycle : Comb.bdry2 (strictOrderCx (QCube A)) z = 0) :
    squareChainEdgeBoundary cell left right hne hspx
      (squareCycleCoefficients cell left right hne hspx hcell z) = 0 := by
  rw [← squareChainSubdivision_boundary,
    ← cubeTwoCycle_is_squareSubdivision cell left right hne hspx hcell hcover z hz hcycle]
  exact hcycle

end FiniteChains.Davis
