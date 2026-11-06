module

public import PottsDiscontinuity.TorusCrossing.Exact

/-!
# Indicator cochains: edges and collar paths

`ind A` is the `ZMod 2`-valued indicator of a finite set of medial vertices.  The degree of the
indicator of the single medial vertex `m` at a primal cell is `1` exactly at the two ends of the
primal edge at `m`.  A *collar interval* is the indicator of the medial vertices
`(a, r)` with `lo < a ≤ hi` on one row `r`; it has odd degree exactly at the two primal cells
`(lo, r')`, `(hi, r')` with `r' ∈ {r, r-1}` and even degree elsewhere (it is the zigzag path
running just outside a wired row).
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

/-- Indicator cochain of a finite set of medial vertices. -/
def ind (A : Finset Cell) : Cell → ZMod 2 := fun m => if m ∈ A then 1 else 0

section
variable {A : Finset Cell} {m : Cell}
theorem ind_apply_of_mem (h : m ∈ A) : ind A m = 1 := by
  simp_all [ind]

theorem ind_apply_of_not_mem (h : m ∉ A) : ind A m = 0 := by
  simp_all [ind]
end

theorem cdeg_add (f g : Cell → ZMod 2) (c : Cell) :
    cdeg (fun m => f m + g m) c = cdeg f c + cdeg g c := by
  unfold cdeg; ring


theorem zmod2_two (z : ZMod 2) : z + z = 0 := by grind

/-- The degree of the indicator of a single medial vertex at a primal cell. -/
theorem cdeg_ind_single (m c : Cell) (hc : IsPrimal c) :
    cdeg (ind {m}) c =
      (if c = (primalEnds m).1 then 1 else 0) + (if c = (primalEnds m).2 then 1 else 0) := by
  grind [cdeg, ind, primalEnds, IsPrimal, corners, decide]

/-- Row-interval collar cochain. -/
def collar (r lo hi : ℤ) : Finset Cell := Finset.Ioc lo hi ×ˢ {r}

theorem mem_collar {r lo hi : ℤ} {m : Cell} : m ∈ collar r lo hi ↔ lo < m.1 ∧ m.1 ≤ hi ∧ m.2 = r := by
  grind [collar]

/-- Degree of a collar interval at a primal cell whose row is `r` or `r - 1`. -/
theorem cdeg_collar (r lo hi : ℤ) (hlohi : lo ≤ hi) (r' : ℤ) (hr' : r' = r ∨ r' = r - 1)
    (hlo : IsPrimal (lo, r')) (hhi : IsPrimal (hi, r')) (c : Cell) (hc : IsPrimal c) :
    cdeg (ind (collar r lo hi)) c =
      (if c = (lo, r') then 1 else 0) + (if c = (hi, r') then 1 else 0) := by
  grind [cdeg, ind, mem_collar, IsPrimal, decide]

end PottsDiscontinuity.TorusCrossing
