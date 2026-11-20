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

variable
  (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s)

theorem loopSum_sub (f g : Dart N M → ℤ) (q : DirectedLoop ω s h) :
    loopSum ω s h (fun d => f d - g d) q = loopSum ω s h f q - loopSum ω s h g q := by
  classical
  unfold loopSum
  rw [Finset.sum_sub_distrib]

/-- Reindexing a cyclic orbit by its path step does not change its sum. -/
theorem loopSum_step (f : Dart N M → ℤ) (q : DirectedLoop ω s h) :
    loopSum ω s h (fun d => f (stepPerm s d)) q = loopSum ω s h f q := by
  classical
  unfold loopSum
  simp only [Finset.sum_filter]
  refine Fintype.sum_equiv (directedStep ω s h) _ _ ?_
  intro d
  rw [directedLoopOf_step]
  rfl

/-- A vertex coboundary cannot change the sum along a closed orbit. -/
theorem loopSum_eq_of_coboundary {f g P : Dart N M → ℤ} (q : DirectedLoop ω s h)
    (ht : ∀ d, f d - g d = P d - P (stepPerm s d)) :
    loopSum ω s h f q = loopSum ω s h g q := by
  apply sub_eq_zero.mp
  simp_rw [← loopSum_sub, ht, loopSum_sub, loopSum_step, sub_self]

/-- Summing a family of seam indicators whose loop sums agree records the
    total displacement, in either coordinate. -/
theorem loopSum_displacement {K : ℕ} (F : Fin K → Dart N M → ℤ) (g : Dart N M → ℤ)
    (i : Fin K) (q : DirectedLoop ω s h) (hg : ∀ d, ∑ j, F j d = g d)
    (he : ∀ j, loopSum ω s h (F j) q = loopSum ω s h (F i) q) :
    loopSum ω s h g q = (K : ℤ) * loopSum ω s h (F i) q := by
  classical
  calc
    _ = ∑ j, loopSum ω s h (F j) q := by
      simp_rw [loopSum, ← hg]
      exact Finset.sum_comm
    _ = _ := by simp [he]

/-- Invariance under one cyclic step implies independence of the choice of seam. -/
theorem eq_of_prv_invariant {K : ℕ} {Y : Type*} (f : Fin K → Y)
    (hf : ∀ i, f i = f (prv i)) (i j : Fin K) : f i = f j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero i.pos.ne'
  have hz (l : Fin (k + 1)) : f l = f 0 := by
    induction l using Fin.induction with
    | zero => rfl
    | succ l ih => rw [hf l.succ, prv_succ, ih]
  simp_all

end

/-- A row-indicator potential on the initial vertex of a dart. -/
def rowPotential (j : Fin M) (d : Dart N M) : ℤ := if d.1.2 = j then 1 else 0

/-- Adjacent reference-row cocycles differ by a vertex coboundary. -/
theorem verticalCross_sub_prv (s : Smoothing N M) (j : Fin M) (d : Dart N M) :
    verticalCross j d - verticalCross (prv j) d =
      rowPotential j d - rowPotential j (stepPerm s d) := by
  rcases d with ⟨⟨i, k⟩, p⟩
  have hn : nxt k = j ↔ k = prv j := (finRotate M).eq_symm_apply.symm
  have hp : prv k = prv j ↔ k = j := (finRotate M).symm.injective.eq_iff
  cases p <;> simp only [verticalCross, rowPotential, stepPerm_apply, strandReverse, edgeReverse, hn] <;> split_ifs <;> omega

section

variable
  (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s)

/-- A closed loop has equal intersection with two adjacent horizontal reference rows. -/
theorem loopVertical_prv (j : Fin M) (q : DirectedLoop ω s h) :
    loopVertical ω s h j q = loopVertical ω s h (prv j) q := loopSum_eq_of_coboundary ω s h q (verticalCross_sub_prv s j)

/-- The intersection number is independent of the chosen horizontal reference row. -/
theorem loopVertical_eq (j k : Fin M) (q : DirectedLoop ω s h) :
    loopVertical ω s h j q = loopVertical ω s h k q := by
  exact eq_of_prv_invariant (fun i => loopVertical ω s h i q)
    (fun i => loopVertical_prv ω s h i q) j k

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
theorem loop_vertical_displacement (ω : ArrowConfig N M) (s : Smoothing N M)
    (h : CompatibleConfig ω s) (j : Fin M) (q : DirectedLoop ω s h) :
    loopSum ω s h verticalIncrement q = (M : ℤ) * loopVertical ω s h j q := by
  exact loopSum_displacement ω s h verticalCross verticalIncrement j q sum_verticalCross_rows
    (fun k => loopVertical_eq ω s h k j q)

end PottsDiscontinuity.Torus
