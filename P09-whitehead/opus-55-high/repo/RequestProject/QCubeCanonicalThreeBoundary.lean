import RequestProject.QCubeThreeOrderedFrame
noncomputable section


/-! Actual three-cube cells and their canonical decreasing boundary frames. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
open scoped Classical
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

abbrev QThreeCube (A : CommRel V) := {c : QCube A // c.spx.card = 3}

def qThreeFrame (c : QThreeCube A) :
    {p : V × V × V // p.2.1 < p.1 ∧ p.2.2 < p.2.1 ∧ c.1.spx = {p.1, p.2.1, p.2.2}} := by
  apply Classical.choice
  obtain ⟨u, v, w, huv, hvw, hs⟩ := qCube_three_ordered_frame c.1 c.2
  aesop

def qThreeUpper (c : QThreeCube A) := (qThreeFrame c).1.1
def qThreeMiddle (c : QThreeCube A) := (qThreeFrame c).1.2.1
def qThreeLower (c : QThreeCube A) := (qThreeFrame c).1.2.2

theorem qThree_middle_lt_upper (c : QThreeCube A) : qThreeMiddle c < qThreeUpper c :=
  (qThreeFrame c).2.1

theorem qThree_lower_lt_middle (c : QThreeCube A) : qThreeLower c < qThreeMiddle c :=
  (qThreeFrame c).2.2.1

theorem qThree_free_directions (c : QThreeCube A) :
    c.1.spx = {qThreeUpper c, qThreeMiddle c, qThreeLower c} := (qThreeFrame c).2.2.2

def qThreeCubeBoundary (c : QThreeCube A) :=
  cubeThreeSquareBoundary c.1 _ _ _
    (Ne.symm (qThree_middle_lt_upper c).ne)
    (Ne.symm ((qThree_lower_lt_middle c).trans (qThree_middle_lt_upper c)).ne)
    (Ne.symm (qThree_lower_lt_middle c).ne) (qThree_free_directions c)

def qThreeChainBoundary : (QThreeCube A →₀ ℤ) →ₗ[ℤ]
    ((strictOrderCx (QCube A)).F →₀ ℤ) :=
  Finsupp.linearCombination ℤ qThreeCubeBoundary

theorem qThreeCube_component_boundary c
    (y : StrictOrdTet (QCube A) →₀ ℤ)
    (hy : ∀ t ∈ y.support, t.1.2.2.2.spx.card ≤ 3)
    (hb : ∀ s ∈ (strictOrdBoundary3 y).support, s.1.2.2.spx.card ≤ 2) :
    ∃ k : ℤ, strictOrdBoundary3 (y.filter (·.1.2.2.2 = c.1)) =
      k • qThreeCubeBoundary c :=
  qCube_three_component_boundary_scalar c.1 _ _ _ (qThree_middle_lt_upper c)
    (qThree_lower_lt_middle c) _ y hy hb
