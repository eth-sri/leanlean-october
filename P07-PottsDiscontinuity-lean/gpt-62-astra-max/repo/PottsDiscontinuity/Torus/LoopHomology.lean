module

public import PottsDiscontinuity.Torus.LoopCrossings

/-!
# Discrete vertical homology of the smoothed loop cycles

An elementary coboundary calculation shows that a closed orbit has the same signed
intersection with every horizontal reference row. Summing those intersections gives
its lifted vertical displacement. Thus the crossing statistic has its actual winding
meaning, independently of any turning-number classification.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

section
variable (ω : ArrowConfig N M) (s : Smoothing N M) (h : CompatibleConfig ω s) (j : Fin M)
    (f g : Dart N M → ℤ) (q : DirectedLoop h) (d : Dart N M)

theorem loopSum_sub :
    loopSum (fun d => f d - g d) q = loopSum f q - loopSum g q := by
  simp [Finset.sum_sub_distrib, loopSum]

/-- Reindexing a cyclic orbit by its path step does not change its sum. -/
theorem loopSum_step {ω : ArrowConfig N M} {s : Smoothing N M}
    {h : CompatibleConfig ω s} (f : Dart N M → ℤ) (q : DirectedLoop h) :
    loopSum (fun d => f (stepPerm s d)) q = loopSum f q := by
  classical
  unfold loopSum
  simp only [Finset.sum_filter]
  refine Fintype.sum_equiv (directedStep h) _ _ ?_
  simp [directedLoopOf_step]

include j d in
/-- A row-indicator potential on the initial vertex of a dart. -/
def rowPotential : ℤ := if d.1.2 = j then 1 else 0

/-- Adjacent reference-row cocycles differ by a vertex coboundary. -/
theorem verticalCross_sub_prv :
    verticalCross j d - verticalCross (prv j) d =
      rowPotential j d - rowPotential j (stepPerm s d) := by
  rcases d with ⟨⟨i, k⟩, p⟩
  have hn : nxt k = j ↔ k = prv j := by
    grind
  have hp : prv k = prv j ↔ k = j := (finRotate M).symm.injective.eq_iff
  have hh (a b : Prop) [Decidable a] [Decidable b] :
      ((if a then (-1 : ℤ) else 0) - if b then -1 else 0) =
        (if b then 1 else 0) - if a then 1 else 0 := by
    grind
  cases p <;>
    simp only [verticalCross, rowPotential, stepPerm_apply, strandReverse,
      edgeReverse, hn, hp, sub_self]
  all_goals
    grind

/-- A closed loop has equal intersection with two adjacent horizontal reference rows. -/
theorem loopVertical_prv :
    loopVertical j q = loopVertical (prv j) q := by
  have hb : loopSum (fun d => verticalCross j d - verticalCross (prv j) d) q = 0 := by
    simp_rw [verticalCross_sub_prv s j]
    rw [loopSum_sub, loopSum_step, sub_self]
  rw [loopSum_sub] at hb
  exact sub_eq_zero.mp hb

/-- The intersection number is independent of the chosen horizontal reference row. -/
theorem loopVertical_eq (j k : Fin M) (q : DirectedLoop h) :
    loopVertical j q = loopVertical k q := by
  have hM := Fin.pos j
  have hz : ∀ l : Fin M, loopVertical l q = loopVertical ⟨0, hM⟩ q := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
    intro l
    induction l using Fin.induction with
    | zero => rfl
    | succ l ih =>
      grind [loopVertical_prv, prv_succ]
  grind

end

/-- Vertical displacement in the integer lift of one directed torus edge. -/
def verticalIncrement : Dart N M → ℤ
  | (_, .north) => 1
  | (_, .south) => -1
  | (_, .west) => 0
  | (_, .east) => 0

theorem sum_verticalCross_rows (d : Dart N M) :
    ∑ j : Fin M, verticalCross j d = verticalIncrement d := by
  rcases d with ⟨⟨i, k⟩, p⟩
  cases p <;> simp [verticalCross, verticalIncrement]

/-- The winding is exactly the lifted vertical displacement divided by the vertical period:
this integral identity avoids division and has no zero-period fallback. -/
theorem loop_vertical_displacement {ω : ArrowConfig N M} {s : Smoothing N M}
    (h : CompatibleConfig ω s) (j : Fin M) (q : DirectedLoop h) :
    loopSum verticalIncrement q = (M : ℤ) * loopVertical j q := by
  classical
  calc
    loopSum verticalIncrement q =
        ∑ k : Fin M, loopVertical k q := by
      unfold loopVertical loopSum
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun d _ => (sum_verticalCross_rows d.val).symm
    _ = ∑ _k : Fin M, loopVertical j q :=
      Finset.sum_congr rfl fun k _ => loopVertical_eq ω s h k j q
    _ = (M : ℤ) * loopVertical j q := by simp

end PottsDiscontinuity.Torus
