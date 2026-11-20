module

public import PottsDiscontinuity.Torus.LoopHomology

/-!
# Horizontal intersection numbers of smoothed loops

This is the coordinate-swapped counterpart of the existing vertical homology
calculation. It records horizontal seam intersections and their lifted
displacement without assuming a topological classification of loop classes.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.TorusLoops

open PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- Signed intersection of a directed dart with the vertical seam at column `i`. -/
def horizontalCross (i : Fin N) : Dart N M → ℤ
  | ((k, _), .east) => if k = i then 1 else 0
  | ((k, _), .west) => if prv k = i then -1 else 0
  | _ => 0

/-- A column-indicator potential on the initial vertex of a dart. -/
def columnPotential (i : Fin N) (d : Dart N M) : ℤ :=
  if d.1.1 = i then 1 else 0

/-- Adjacent vertical-seam cocycles differ by a vertex coboundary. -/
theorem horizontalCross_sub_prv (s : Smoothing N M) (i : Fin N) (d : Dart N M) :
    horizontalCross i d - horizontalCross (prv i) d =
      columnPotential i d - columnPotential i (stepPerm s d) := by
  rcases d with ⟨⟨k, j⟩, p⟩
  have hn : nxt k = i ↔ k = prv i := (finRotate N).eq_symm_apply.symm
  have hp : prv k = prv i ↔ k = i := (finRotate N).symm.injective.eq_iff
  cases p <;> simp only [horizontalCross, columnPotential, stepPerm_apply, strandReverse, edgeReverse, hn] <;> split_ifs <;> omega

/-- A closed loop has equal intersection with two adjacent vertical seams. -/
theorem loopHorizontal_prv (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (i : Fin N) (q : DirectedLoop ω s h) :
    loopSum ω s h (horizontalCross i) q =
      loopSum ω s h (horizontalCross (prv i)) q := loopSum_eq_of_coboundary ω s h q (horizontalCross_sub_prv s i)

/-- The horizontal intersection number is independent of the chosen vertical seam. -/
theorem loopHorizontal_eq (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (i k : Fin N) (q : DirectedLoop ω s h) :
    loopSum ω s h (horizontalCross i) q =
      loopSum ω s h (horizontalCross k) q := by
  exact eq_of_prv_invariant (fun l => loopSum ω s h (horizontalCross l) q)
    (fun l => loopHorizontal_prv ω s h l q) i k

/-- Horizontal displacement of one directed dart in the integer lift. -/
def horizontalIncrement : Dart N M → ℤ
  | (_, .east) => 1
  | (_, .west) => -1
  | (_, .south) => 0
  | (_, .north) => 0

theorem sum_horizontalCross_columns (d : Dart N M) :
    ∑ i : Fin N, horizontalCross i d = horizontalIncrement d := by
  rcases d with ⟨⟨k, j⟩, p⟩
  cases p <;> simp [horizontalCross, horizontalIncrement]

/-- Summing seam intersections gives the lifted horizontal displacement. -/
theorem loop_horizontal_displacement (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (i : Fin N) (q : DirectedLoop ω s h) :
    loopSum ω s h horizontalIncrement q =
      (N : ℤ) * loopSum ω s h (horizontalCross i) q := by
  exact loopSum_displacement ω s h horizontalCross horizontalIncrement i q sum_horizontalCross_columns
    (fun k => loopHorizontal_eq ω s h k i q)

end PottsDiscontinuity.TorusLoops
