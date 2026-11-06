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

@[expose] public noncomputable section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus

variable {N M : ℕ}

section
variable (ω : ArrowConfig N M)
/-- A nonzero sum on a loop has a nonzero dart contribution on that loop. -/
theorem exists_dart_of_loopSum_ne_zero (s : Smoothing N M)
    (h : CompatibleConfig ω s) (f : Dart N M → ℤ) (q : DirectedLoop ω s h)
    (hsum : loopSum ω s h f q ≠ 0) :
    ∃ d : DirectedDart ω, directedLoopOf ω s h d = q ∧ f d.val ≠ 0 := by
  obtain ⟨d, hd, hfd⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  refine ⟨d, ?_, hfd⟩
  simpa using hd

/-- Directed darts crossing the chosen horizontal seam. -/
def verticalCutDarts (j : Fin M) :
    Finset (DirectedDart ω) :=
  Finset.univ.filter fun d => verticalCross j d.val ≠ 0

/-- Directed darts crossing the chosen vertical seam. -/
def horizontalCutDarts (i : Fin N) :
    Finset (DirectedDart ω) :=
  Finset.univ.filter fun d => horizontalCross i d.val ≠ 0
end

section
variable {ω : ArrowConfig N M}
theorem dartEdge_eq_fixed_vertical {j : Fin M}
    (d : DirectedDart ω) (hd : verticalCross j d.val ≠ 0) :
    dartEdge d.val = ((d.val.1.1, j), true) := by
  rcases d with ⟨⟨⟨i, k⟩, p⟩, hout⟩
  cases p <;> simp [verticalCross, dartEdge] at hd ⊢ <;> assumption

theorem dartEdge_eq_fixed_horizontal {i : Fin N}
    (d : DirectedDart ω) (hd : horizontalCross i d.val ≠ 0) :
    dartEdge d.val = ((i, d.val.1.2), false) := by
  rcases d with ⟨⟨⟨k, j⟩, p⟩, hout⟩
  cases p <;> simp [horizontalCross, dartEdge] at hd ⊢ <;> assumption
end

section
variable (ω : ArrowConfig N M)
/-- A fixed horizontal seam has at most one directed dart per indexed edge. -/
theorem verticalCutDarts_card_le (j : Fin M) :
    (verticalCutDarts ω j).card ≤ N := by
  let C := verticalCutDarts ω j
  have hinj : (C : Set (DirectedDart ω)).InjOn
      (fun d => d.val.1.1) := by
    intro d hd e he hcoord
    change d.val.1.1 = e.val.1.1 at hcoord
    have hEdge : dartEdge d.val = dartEdge e.val := by
      rw [dartEdge_eq_fixed_vertical d ((Finset.mem_filter.mp hd).2), dartEdge_eq_fixed_vertical e ((Finset.mem_filter.mp he).2), hcoord]
    have htransport := congrArg (edgeDirectedEquiv ω) hEdge
    grind [edgeDirectedEquiv, dartEdge]
  calc
    C.card ≤ (Finset.univ : Finset (Fin N)).card :=
      Finset.card_le_card_of_injOn
        (fun d => d.val.1.1) (by simp) hinj
    _ = N := by simp

/-- A fixed vertical seam has at most one directed dart per indexed edge. -/
theorem horizontalCutDarts_card_le (i : Fin N) :
    (horizontalCutDarts ω i).card ≤ M := by
  let C := horizontalCutDarts ω i
  have hinj : (C : Set (DirectedDart ω)).InjOn
      (fun d => d.val.1.2) := by
    intro d hd e he hcoord
    change d.val.1.2 = e.val.1.2 at hcoord
    have hEdge : dartEdge d.val = dartEdge e.val := by
      rw [dartEdge_eq_fixed_horizontal d ((Finset.mem_filter.mp hd).2), dartEdge_eq_fixed_horizontal e ((Finset.mem_filter.mp he).2), hcoord]
    have htransport := congrArg (edgeDirectedEquiv ω) hEdge
    grind [edgeDirectedEquiv, dartEdge]
  calc
    C.card ≤ (Finset.univ : Finset (Fin M)).card :=
      Finset.card_le_card_of_injOn
        (fun d => d.val.1.2) (by simp) hinj
    _ = M := by simp
end

section
variable (hN : Even N) (hM : Even M) (i : Fin N) (j : Fin M) (A : RCConfig N M)
/-- Loops with nonzero winding in either coordinate, measured at reference seams. -/
def windingLoopSet  :
    Finset (Loop hN hM (rcSmoothing A)) := by
  classical
  exact Finset.univ.filter fun q =>
      loopVertical (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM (rcSmoothing A)) j q ≠ 0 ∨
      loopSum (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM (rcSmoothing A)) (horizontalCross i) q ≠ 0

/-- Cardinality of the explicitly defined nonzero-winding loop set. -/
def windingLoopCount  : ℕ :=
  (windingLoopSet hN hM i j A).card

/-- Images of the two finite seam-crossing dart sets in the loop quotient. -/
def loopCutImages  :
    Finset (Loop hN hM (rcSmoothing A)) := by
  classical
  exact Finset.image (directedLoopOf (checkerArrows N M) (rcSmoothing A)
      (checkerArrows_compatible hN hM (rcSmoothing A)))
      (verticalCutDarts (checkerArrows N M) j) ∪
    Finset.image (directedLoopOf (checkerArrows N M) (rcSmoothing A)
      (checkerArrows_compatible hN hM (rcSmoothing A)))
      (horizontalCutDarts (checkerArrows N M) i)

/-- A nonzero winding loop contains a dart crossing one of the two reference seams. -/
theorem windingLoopSet_subset_cutImages  :
    windingLoopSet hN hM i j A ⊆ loopCutImages hN hM i j A := by
  classical
  intro q hq
  rcases ((Finset.mem_filter.mp hq).2) with hv | hh
  · obtain ⟨d, hloop, hcross⟩ := exists_dart_of_loopSum_ne_zero
      (checkerArrows N M) (rcSmoothing A)
      (checkerArrows_compatible hN hM (rcSmoothing A))
      (verticalCross j) q (by positivity)
    have hdmem : d ∈ verticalCutDarts (checkerArrows N M) j := by
      simp_all [verticalCutDarts]
    change _ ∈
      Finset.image (directedLoopOf (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM (rcSmoothing A)))
        (verticalCutDarts (checkerArrows N M) j) ∪ _
    grind
  · obtain ⟨d, hloop, hcross⟩ := exists_dart_of_loopSum_ne_zero
      (checkerArrows N M) (rcSmoothing A)
      (checkerArrows_compatible hN hM (rcSmoothing A))
      (horizontalCross i) q hh
    have hdmem : d ∈ horizontalCutDarts (checkerArrows N M) i := by
      simp_all [horizontalCutDarts]
    change _ ∈
      _ ∪ Finset.image (directedLoopOf (checkerArrows N M) (rcSmoothing A)
        (checkerArrows_compatible hN hM (rcSmoothing A)))
        (horizontalCutDarts (checkerArrows N M) i)
    grind

/-- The number of loops with nonzero coordinate winding is at most `N + M`.

This finite counting bound is independent of the still separate identification
between nonzero winding and the source's topological terminology.
-/
theorem windingLoopCount_le  :
    windingLoopCount hN hM i j A ≤ N + M := by
  classical
  calc
    (windingLoopSet hN hM i j A).card ≤
        (loopCutImages hN hM i j A).card :=
      Finset.card_le_card (windingLoopSet_subset_cutImages hN hM i j A)
    _ ≤ (verticalCutDarts (checkerArrows N M) j).card +
        (horizontalCutDarts (checkerArrows N M) i).card := by
      grind [loopCutImages, Finset.image, directedLoopOf, checkerArrows, rcSmoothing, verticalCutDarts, horizontalCutDarts]
    _ ≤ N + M := Nat.add_le_add
      (verticalCutDarts_card_le _ _) (horizontalCutDarts_card_le _ _)
end

end PottsDiscontinuity.TorusLoops
