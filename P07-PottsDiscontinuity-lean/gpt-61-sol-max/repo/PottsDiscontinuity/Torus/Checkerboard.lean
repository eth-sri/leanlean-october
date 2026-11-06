module
public import Mathlib

public import PottsDiscontinuity.Torus.Darts

/-!
# A canonical orientation of every smoothed loop

On an even medial torus the checkerboard arrow field has alternating types 5 and 6.
Both turning pairings are compatible at every vertex. It therefore gives a canonical
orientation and an actual cyclic-orbit carrier for the loops of every smoothing.
This does not impose any turning-number or homology condition on those loops.
-/

@[expose] public section

open PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- Checkerboard colour of a medial vertex. -/
def checker (v : Fin N × Fin M)  := decide ((v.1.val + v.2.val) % 2 = 0)

private theorem nxt_mod_two (hN : Even N) (i : Fin N) :
    (nxt i).val % 2 = 1 - i.val % 2 := by
  
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Fin.pos i).ne'
  rw [coe_finRotate]
  grind

theorem checker_nxt_x (hN : Even N) (i : Fin N) (j : Fin M) :
    checker (nxt i, j) = !checker (i, j) := by
  have hn := nxt_mod_two hN i
  by_cases ha : ((nxt i).val + j.val) % 2 = 0
  · grind +locals
  · grind +locals

theorem checker_nxt_y (hM : Even M) (i : Fin N) (j : Fin M) :
    checker (i, nxt j) = !checker (i, j) := by
  have hm := nxt_mod_two hM j
  by_cases ha : (i.val + (nxt j).val) % 2 = 0
  · grind +locals
  · grind +locals

theorem checker_prv_x (hN : Even N) (i : Fin N) (j : Fin M) :
    checker (prv i, j) = !checker (i, j) := by
  have h := checker_nxt_x hN (prv i) j
  grind

theorem checker_prv_y (hM : Even M) (i : Fin N) (j : Fin M) :
    checker (i, prv j) = !checker (i, j) := by
  have h := checker_nxt_y hM i (prv j)
  grind

/-- Orient each edge with its black checkerboard face on the same side. -/
def checkerArrows (N M : ℕ) : ArrowConfig N M where
  horiz v := checker v
  vert v := !checker v

/-- Both pairings are compatible with the canonical checkerboard orientation. -/
theorem checkerArrows_compatible (hN : Even N) (hM : Even M) (s : Smoothing N M) :
    CompatibleConfig (checkerArrows N M) s := by
  rintro ⟨i, j⟩
  change Compatible (s (i, j)) (checker (prv i, j)) (checker (i, j))
    (!checker (i, prv j))  !checker (i, j) 
  rw [checker_prv_x hN, checker_prv_y hM]
  cases s (i, j) <;> cases checker (i, j) <;> decide

/-- The canonically oriented loops of a smoothing, as cyclic classes of directed darts. -/
abbrev Loop (hN : Even N) (hM : Even M) (s : Smoothing N M) :=
  DirectedLoop (checkerArrows N M) s (checkerArrows_compatible hN hM s)

/-- Number of smoothed loops, with one canonical orientation per loop. -/
noncomputable def loopCount (hN : Even N) (hM : Even M) (s : Smoothing N M)  :=
  Fintype.card (Loop hN hM s)

end PottsDiscontinuity.Torus
