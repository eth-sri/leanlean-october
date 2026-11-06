import Mathlib.Tactic

import RequestProject.BlockConnected

/-!
# A concrete attaching map: the cycle that spells a prescribed word

Everything in `RequestProject/BlockSpinePres.lean` and `RequestProject/BlockSpineSubst.lean` is
stated for an arbitrary nerve `L` and an arbitrary attaching map
`att : NeSpx A →o presModelPos ρ`.  This file produces such an `att` **concretely**, together
with the geometric loop of the cut surface along which it spells a prescribed word.

The nerve is the cycle `C_M` with `M = 2·|u|` vertices, `u` being the prescribed word: its
vertices alternate between *corner* vertices (even positions) and *midpoints of letters* (odd
positions), and its edges are the two halves of the letters.  The attaching map is the simplicial
map onto the subdivided rose of `RequestProject/PresPosetModel.lean` which sends a vertex and an
edge to the cell carrying the same label; going once around the cycle therefore spells exactly
the word `u`.

This file contains the combinatorial part: the cycle, its labels, the attaching map and its
monotonicity.  The loop and the application of the theorem are in
`RequestProject/AttCycleLoop.lean` and `RequestProject/AttCycleApply.lean`.
-/

namespace FiniteChains.Davis


open RACG Mirror Comb PresModel


/-! ### The cycle graph -/







/-! ### The labels -/

section

variable {α : Type u}

  (l : List (α × Bool))
/-- The label of the vertex at the position `p` of the cycle: even positions are corners of the
word and carry the base vertex of the rose, odd positions are midpoints of letters and carry the
midpoint of the loop of the corresponding generator. -/
def vertLab  (p : ℕ)  :=
  if p % 2 = 0 then Rose.base
  else
    match l[p / 2]? with
    | some q => Rose.mid q.1
    | none => Rose.base

/-- The label of the edge joining the positions `p` and `p+1` of the cycle: the first half of the
letter `p/2` for even `p`, its second half for odd `p`, the halves being taken in the order
prescribed by the sign of the letter. -/
def edgeLab  (p : ℕ)  :=
  match l[p / 2]? with
  | some q => Rose.edg q.1 (if p % 2 = 0 then !q.2 else q.2)
  | none => Rose.base

variable {l : List (α × Bool)}
  {p : ℕ}
@[simp] theorem vertLab_of_even   (hp : p % 2 = 0) :
    vertLab l p = Rose.base := if_pos hp

theorem vertLab_of_odd   {q : α × Bool} (hp : p % 2 = 1)
    (hq : l[p / 2]? = some q) : vertLab l p = Rose.mid q.1 := by
  simp [vertLab, hp, hq]

theorem edgeLab_eq   {q : α × Bool} (hq : l[p / 2]? = some q) :
    edgeLab l p = Rose.edg q.1 (if p % 2 = 0 then !q.2 else q.2) := by
  simp [edgeLab, hq]

theorem getElem?_half {l : List (α × Bool)} {p : ℕ} (hp : p < 2 * l.length) :
    ∃ q, l[p / 2]? = some q :=
  ⟨l[p / 2]'(by omega), List.getElem?_eq_getElem (by omega)⟩

/-- The vertex at a position lies under the edge that starts at it. -/
theorem vertLab_le_edgeLab   (hp : p < 2 * l.length) :
    vertLab l p ≤ edgeLab l p := by
  obtain ⟨q, hq⟩ := getElem?_half hp
  rcases Nat.even_or_odd p with he | ho
  · simp_all [Nat.even_iff, FiniteChains.Davis.edgeLab_eq]
  · aesop (add simp [vertLab_of_odd, edgeLab_eq])

/-- The vertex at the next position lies under the same edge. -/
theorem vertLab_succ_le_edgeLab   (hp : p + 1 < 2 * l.length) :
    vertLab l (p + 1) ≤ edgeLab l p := by
  obtain ⟨q, hq⟩ := getElem?_half (Nat.lt_of_succ_lt hp)
  rcases Nat.even_or_odd p with he | ho
  · grind [vertLab_of_odd, edgeLab_eq, Rose.mid_le_edg]
  · grind [FiniteChains.Davis.vertLab_of_even, FiniteChains.Davis.edgeLab_eq, FiniteChains.PresModel.Rose.base_le_edg]

/-- Every edge of the cycle carries a one-cell of the rose, so the base vertex lies under it. -/
theorem base_le_edgeLab   (hp : p < 2 * l.length) :
    (Rose.base : Rose α) ≤ edgeLab l p := by
  obtain ⟨q, hq⟩ := getElem?_half hp
  rw [edgeLab_eq hq]
  exact Rose.base_le_edg _ _

/-! ### The label of a simplex -/













end

/-! ### The attaching map -/













end FiniteChains.Davis

