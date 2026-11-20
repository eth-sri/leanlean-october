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

section
variable (ω : ArrowConfig N M) (s : Smoothing N M) (h : CompatibleConfig ω s) (i : Fin N)
    (d : Dart N M)

include i in
/-- Signed intersection of a directed dart with the vertical seam at column `i`. -/
def horizontalCross : Dart N M → ℤ
  | ((k, _), .east) => if k = i then 1 else 0
  | ((k, _), .west) => if prv k = i then -1 else 0
  | _ => 0

include i d in
/-- A column-indicator potential on the initial vertex of a dart. -/
def columnPotential : ℤ :=
  if d.1.1 = i then 1 else 0

/-- Adjacent vertical-seam cocycles differ by a vertex coboundary. -/
theorem horizontalCross_sub_prv :
    horizontalCross i d - horizontalCross (prv i) d =
      columnPotential i d - columnPotential i (stepPerm s d) := by
  rcases d with ⟨⟨k, j⟩, p⟩
  have hn : nxt k = i ↔ k = prv i := by
    grind
  have hp : prv k = prv i ↔ k = i := (finRotate N).symm.injective.eq_iff
  have hh (a b : Prop) [Decidable a] [Decidable b] :
      ((if a then (-1 : ℤ) else 0) - if b then -1 else 0) =
        (if b then 1 else 0) - if a then 1 else 0 := by
    grind
  cases p <;>
    simp only [horizontalCross, columnPotential, stepPerm_apply, strandReverse,
      edgeReverse, hn, hp, sub_self]
  all_goals
    grind

/-- A closed loop has equal intersection with two adjacent vertical seams. -/
theorem loopHorizontal_prv (q : DirectedLoop h) :
    loopSum (horizontalCross i) q =
      loopSum (horizontalCross (prv i)) q := by
  have hb : loopSum
      (fun d => horizontalCross i d - horizontalCross (prv i) d) q = 0 := by
    simp_rw [horizontalCross_sub_prv s i]
    rw [loopSum_sub, loopSum_step, sub_self]
  grind [loopSum_sub]

/-- The horizontal intersection number is independent of the chosen vertical seam. -/
theorem loopHorizontal_eq (i k : Fin N) (q : DirectedLoop h) :
    loopSum (horizontalCross i) q =
      loopSum (horizontalCross k) q := by
  have hN := Fin.pos i
  have hz : ∀ l : Fin N,
      loopSum (horizontalCross l) q =
        loopSum (horizontalCross ⟨0, hN⟩) q := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    intro l
    induction l using Fin.induction with
    | zero => rfl
    | succ l ih =>
      grind [loopHorizontal_prv, prv_succ]
  grind

end

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
theorem loop_horizontal_displacement {ω : ArrowConfig N M} {s : Smoothing N M}
    (h : CompatibleConfig ω s) (i : Fin N) (q : DirectedLoop h) :
    loopSum horizontalIncrement q =
      (N : ℤ) * loopSum (horizontalCross i) q := by
  classical
  calc
    loopSum horizontalIncrement q =
        ∑ k : Fin N, loopSum (horizontalCross k) q := by
      unfold loopSum
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun d _ => (sum_horizontalCross_columns d.val).symm
    _ = ∑ _k : Fin N, loopSum (horizontalCross i) q :=
      Finset.sum_congr rfl fun k _ => loopHorizontal_eq ω s h k i q
    _ = (N : ℤ) * loopSum (horizontalCross i) q := by simp

end PottsDiscontinuity.TorusLoops
