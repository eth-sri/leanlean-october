import RequestProject.QCubeTwoCycleSubdivision
import RequestProject.Tac
noncomputable section


/-! The actual square cells and their unconditional finite two-cycle subdivision dictionary. -/
bwd

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

abbrev QSquare (A : CommRel V) := {c : QCube A // c.spx.card = 2}

def qSquareFrame (c : QSquare A) :
    {p : V × V // p.2 < p.1 ∧ c.1.spx = {p.1, p.2}} := by
  apply Classical.choice
  obtain ⟨a, b, hne, hs⟩ := Finset.card_eq_two.mp c.2
  rcases lt_or_gt_of_ne hne with hab | hba
  · aesop
  aesop

def qSquareLeft (c : QSquare A) := (qSquareFrame c).1.1
def qSquareRight (c : QSquare A) := (qSquareFrame c).1.2

theorem qSquare_directions_ne (c : QSquare A) : qSquareLeft c ≠ qSquareRight c :=
  Ne.symm (qSquareFrame c).2.1.ne

theorem qSquare_directions_decreasing (c : QSquare A) : qSquareRight c < qSquareLeft c :=
  (qSquareFrame c).2.1

theorem qSquare_free_directions (c : QSquare A) : c.1.spx = {qSquareLeft c, qSquareRight c} :=
  (qSquareFrame c).2.2

def qSquareChainSubdivision : (QSquare A →₀ ℤ) →ₗ[ℤ]
    ((strictOrderCx (QCube A)).F →₀ ℤ) :=
  squareChainSubdivision Subtype.val qSquareLeft qSquareRight
    qSquare_directions_ne qSquare_free_directions

def qSquareCycleCoefficients : ((strictOrderCx (QCube A)).F →₀ ℤ) →ₗ[ℤ]
    (QSquare A →₀ ℤ) :=
  squareCycleCoefficients Subtype.val qSquareLeft qSquareRight
    qSquare_directions_ne qSquare_free_directions Subtype.val_injective

def qSquareFacetBoundary : (QSquare A →₀ ℤ) →ₗ[ℤ]
    ((strictOrderCx (QCube A)).E →₀ ℤ) :=
  squareChainEdgeBoundary Subtype.val qSquareLeft qSquareRight
    qSquare_directions_ne qSquare_free_directions

/-- Every actual strict two-cycle supported in cube dimension at most two is exactly the
subdivision of its finite integer chain on the actual square cells. -/
theorem qCube_twoCycle_reconstruction z
    (hz : ∀ t ∈ z.support, t.1.2.2.spx.card ≤ 2)
    (hcycle : Comb.bdry2 (strictOrderCx (QCube A)) z = 0) :
    qSquareChainSubdivision (qSquareCycleCoefficients z) = z :=
  (cubeTwoCycle_is_squareSubdivision Subtype.val qSquareLeft qSquareRight
    qSquare_directions_ne qSquare_free_directions Subtype.val_injective
    (by simp) z hz hcycle).symm

theorem qCube_twoCycle_coefficients_cycle z
    (hz : ∀ t ∈ z.support, t.1.2.2.spx.card ≤ 2)
    (hcycle : Comb.bdry2 (strictOrderCx (QCube A)) z = 0) :
    qSquareFacetBoundary (qSquareCycleCoefficients z) = 0 :=
  cubeTwoCycle_coefficients_cycle Subtype.val qSquareLeft qSquareRight
    qSquare_directions_ne qSquare_free_directions Subtype.val_injective
    (by simp) z hz hcycle

/-- Recovering coefficients is a left inverse on all finite chains of actual square cells. -/
theorem qSquare_coefficients_subdivision (r : QSquare A →₀ ℤ) :
    qSquareCycleCoefficients (qSquareChainSubdivision r) = r := by
  classical
  ext c
  change qSquareChainSubdivision r
    (squareFlag c.1 _ _ (qSquare_directions_ne c)
      (qSquare_free_directions c) (false, 0, false)) = r c
  have he := congrArg (fun z =>
      z (squareFlag c.1 _ _ (qSquare_directions_ne c)
        (qSquare_free_directions c) (false, 0, false)))
    (squareChainSubdivision_filter_top Subtype.val qSquareLeft qSquareRight
      qSquare_directions_ne qSquare_free_directions Subtype.val_injective r c)
  have hc := squareSubdivision_flag_coefficient c.1 _ _
    (qSquare_directions_ne c) (qSquare_free_directions c) (false, 0, false)
  simp_all [squareFlagSign, if_true, qSquareChainSubdivision, Finsupp.filter_apply, squareFlag_top, Finsupp.smul_apply, hc, smul_eq_mul, mul_one]
