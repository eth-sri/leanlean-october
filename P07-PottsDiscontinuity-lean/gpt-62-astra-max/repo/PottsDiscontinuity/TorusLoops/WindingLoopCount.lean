module

public import PottsDiscontinuity.Torus.DiamondGraph
public import PottsDiscontinuity.TorusLoops.HorizontalHomology

/-!
# Bounds for loops with nonzero coordinate winding

For a directed smoothed loop, nonzero intersection with either coordinate seam
is its nonzero torus winding class. The source statistic `ell₀`, the number of loops that
are not retractable to a point on the torus, is formalized throughout as the number of loops
with nonzero homological winding, i.e. nonzero algebraic intersection with the vertical or the
horizontal seam. No homotopy classification is used.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- A nonzero sum on a loop has a nonzero dart contribution on that loop. -/
theorem exists_dart_of_loopSum_ne_zero {ω : ArrowConfig N M} {s : Smoothing N M}
    {h : CompatibleConfig ω s} {f : Dart N M → ℤ} (q : DirectedLoop h)
    (hsum : loopSum f q ≠ 0) :
    ∃ d, directedLoopOf h d = q ∧ f d.val ≠ 0 := by
  classical
  obtain ⟨d, hd, hfd⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  grind

variable (ω : ArrowConfig N M) (hN : Even N) (hM : Even M) (i : Fin N) (j : Fin M)
    (A : RCConfig N M)

include j in
/-- Directed darts crossing the chosen horizontal seam. -/
noncomputable def verticalCutDarts :
    Finset (DirectedDart ω) :=
  Finset.univ.filter fun d => verticalCross j d.val ≠ 0

private theorem dartEdge_eq_fixed_vertical {ω : ArrowConfig N M} {j : Fin M}
    (d : DirectedDart ω) (hd : verticalCross j d.val ≠ 0) :
    dartEdge d.val = ((d.val.1.1, j), true) := by
  rcases d with ⟨⟨⟨i, k⟩, p⟩, hout⟩
  cases p <;> simp [verticalCross, dartEdge] at hd ⊢ <;> assumption

/-- A fixed horizontal seam has at most one directed dart per indexed edge. -/
theorem verticalCutDarts_card_le :
    (verticalCutDarts ω j).card ≤ N := by
  classical
  let C := verticalCutDarts ω j
  have hinj : (C : Set (DirectedDart ω)).InjOn
      (fun d => d.val.1.1) := by
    intro d hd e he hcoord
    change d.val.1.1 = e.val.1.1 at hcoord
    have hEdge : dartEdge d.val = dartEdge e.val := by
      rw [dartEdge_eq_fixed_vertical d ((Finset.mem_filter.mp hd).2), dartEdge_eq_fixed_vertical e ((Finset.mem_filter.mp he).2), hcoord]
    have hdInv : edgeDirectedEquiv ω (dartEdge d.val) = d := Subtype.ext (arrowDart_dartEdge d)
    have heInv : edgeDirectedEquiv ω (dartEdge e.val) = e := Subtype.ext (arrowDart_dartEdge e)
    grind
  calc
    C.card ≤ Finset.univ.card :=
      Finset.card_le_card_of_injOn (t := Finset.univ)
        (fun d => d.val.1.1) (by simp) hinj
    _ = N := by simp

include i j in
/-- Loops with nonzero winding in either coordinate, measured at reference seams. -/
noncomputable def windingLoopSet :
    Finset (Loop hN hM (rcSmoothing A)) := {q | loopVertical j q ≠ 0 ∨ loopSum (horizontalCross i) q ≠ 0}

include hN hM i j A in
/-- Cardinality of the explicitly defined nonzero-winding loop set. -/
noncomputable def windingLoopCount : ℕ :=
  (windingLoopSet hN hM i j A).card

end PottsDiscontinuity.TorusLoops
