module

public import RequestProject.QCubeTwoCycleSubdivision

@[expose] public section

/-! The actual square cells and their unconditional finite two-cycle subdivision dictionary. -/

noncomputable section

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

/-- A quotient cube with a prescribed number of free directions. -/
abbrev QCell (A : CommRel V) (n : ℕ) := {c : QCube A // c.spx.card = n}
abbrev QSquare (A : CommRel V) := QCell A 2
abbrev QThreeCube (A : CommRel V) := QCell A 3

/-- Enumerate the free coordinates of a cell in decreasing order. This same
frame orients the square and three-dimensional cellular boundary maps. -/
def QCell.dirs {n} (c : QCell A n) : Fin n ≃ c.1.spx :=
  Fin.revPerm.trans (c.1.spx.orderIsoOfFin c.2).toEquiv

theorem QCell.antitone {n} (c : QCell A n) : StrictAnti (fun i => (c.dirs i : V)) :=
  fun _ _ h => (c.1.spx.orderEmbOfFin c.2).strictMono (Fin.rev_lt_rev.mpr h)

variable (c : QSquare A)
def qSquareLeft : V := c.dirs 0
def qSquareRight : V := c.dirs 1

theorem qSquare_directions_decreasing : qSquareRight c < qSquareLeft c := c.antitone (by decide : (0 : Fin 2) < 1)
theorem qSquare_directions_ne : qSquareLeft c ≠ qSquareRight c := (qSquare_directions_decreasing c).ne'
theorem qSquare_free_directions : c.1.spx = {qSquareLeft c, qSquareRight c} := by
  ext v; constructor
  · intro hv
    obtain ⟨i, hi⟩ := c.dirs.surjective ⟨v, hv⟩
    have := congrArg Subtype.val hi
    fin_cases i <;> simp_all [qSquareLeft, qSquareRight]
  · simp only [Finset.mem_insert, Finset.mem_singleton]; rintro (rfl | rfl) <;> exact (c.dirs _).2

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

section

variable (z : (strictOrderCx (QCube A)).F →₀ ℤ)
    (hz : ∀ t ∈ z.support, t.1.2.2.spx.card ≤ 2)
    (hcycle : Comb.bdry2 (strictOrderCx (QCube A)) z = 0)
include hz hcycle

/-- Every actual strict two-cycle supported in cube dimension at most two is exactly the
subdivision of its finite integer chain on the actual square cells. -/
theorem qCube_twoCycle_reconstruction :
    qSquareChainSubdivision (qSquareCycleCoefficients z) = z :=
  (cubeTwoCycle_is_squareSubdivision Subtype.val qSquareLeft qSquareRight
    qSquare_directions_ne qSquare_free_directions Subtype.val_injective
    (fun c hc => ⟨⟨c, hc⟩, rfl⟩) z hz hcycle).symm

theorem qCube_twoCycle_coefficients_cycle :
    qSquareFacetBoundary (qSquareCycleCoefficients z) = 0 :=
  cubeTwoCycle_coefficients_cycle Subtype.val qSquareLeft qSquareRight
    qSquare_directions_ne qSquare_free_directions Subtype.val_injective
    (fun c hc => ⟨⟨c, hc⟩, rfl⟩) z hz hcycle

end

/-- Recovering coefficients is a left inverse on all finite chains of actual square cells. -/
theorem qSquare_coefficients_subdivision (r : QSquare A →₀ ℤ) :
    qSquareCycleCoefficients (qSquareChainSubdivision r) = r := by
  classical
  ext c
  change qSquareChainSubdivision r
    (squareFlag c.1 (qSquareLeft c) (qSquareRight c) (qSquare_directions_ne c)
      (qSquare_free_directions c) (false, 0, false)) = r c
  have he := congrArg (fun z : (strictOrderCx (QCube A)).F →₀ ℤ =>
      z (squareFlag c.1 (qSquareLeft c) (qSquareRight c) (qSquare_directions_ne c)
        (qSquare_free_directions c) (false, 0, false)))
    (squareChainSubdivision_filter_top Subtype.val qSquareLeft qSquareRight
      qSquare_directions_ne qSquare_free_directions Subtype.val_injective r c)
  have hc := squareSubdivision_flag_coefficient c.1 _ _
    (qSquare_directions_ne c) (qSquare_free_directions c) (false, 0, false)
  simp_all [squareFlagSign, if_true, qSquareChainSubdivision, Finsupp.filter_apply, squareFlag_top, Finsupp.smul_apply, hc, smul_eq_mul, mul_one]

end FiniteChains.Davis
