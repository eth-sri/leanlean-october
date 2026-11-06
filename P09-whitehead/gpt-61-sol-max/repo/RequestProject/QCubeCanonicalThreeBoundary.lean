import Mathlib.Tactic

import RequestProject.QCubeThreeOrderedFrame

/-! Actual three-cube cells and their canonical decreasing boundary frames. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
open scoped Classical
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

abbrev QThreeCube (A : CommRel V) := {c : QCube A // c.spx.card = 3}

variable (c : QThreeCube A)
noncomputable def qThreeFrame  :
    {p : V × V × V // p.2.1 < p.1 ∧ p.2.2 < p.2.1 ∧ c.1.spx = {p.1, p.2.1, p.2.2}} := by
  apply Classical.choice
  obtain ⟨u, v, w, huv, hvw, hs⟩ := qCube_three_ordered_frame c.1 c.2
  exact ⟨⟨(u, v, w), huv, hvw, hs⟩⟩

noncomputable def qThreeUpper   := (qThreeFrame c).1.1
noncomputable def qThreeMiddle   := (qThreeFrame c).1.2.1
noncomputable def qThreeLower   := (qThreeFrame c).1.2.2

abbrev qThree_middle_lt_upper   :=
  (FiniteChains.Davis.qThreeFrame c).property.left

abbrev qThree_lower_lt_middle   :=
  (FiniteChains.Davis.qThreeFrame c).property.right.left

abbrev qThree_free_directions   :=
  (FiniteChains.Davis.qThreeFrame c).property.right.right

noncomputable def qThreeCubeBoundary   :=
  cubeThreeSquareBoundary c.1 (qThreeUpper c) (qThreeMiddle c) (qThreeLower c)
    (Ne.symm (qThree_middle_lt_upper c).ne)
    (Ne.symm ((qThree_lower_lt_middle c).trans (qThree_middle_lt_upper c)).ne)
    (Ne.symm (qThree_lower_lt_middle c).ne) (qThree_free_directions c)

noncomputable def qThreeChainBoundary : (QThreeCube A →₀ ℤ) →ₗ[ℤ]
    ((strictOrderCx (QCube A)).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ qThreeCubeBoundary

abbrev qThreeCube_component_boundary 
    (y : StrictOrdTet (QCube A) →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3)
    (hb : ∀ s ∈ (strictOrdBoundary3 y).support, s.1.2.2.spx.card ≤ 2)  :=
  qCube_three_component_boundary_scalar c.1 _ _ _ (qThree_middle_lt_upper c)
    (qThree_lower_lt_middle c) (qThree_free_directions c) y hy hb

end FiniteChains.Davis
