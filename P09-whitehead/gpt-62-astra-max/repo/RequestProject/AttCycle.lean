module

public import RequestProject.BlockConnected

@[expose] public section

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

namespace FiniteChains
namespace Davis

open RACG Mirror Comb PresModel

universe u

/-! ### The cycle graph -/

variable (M : ℕ)

/-! ### The labels -/

section Labels

variable {α : Type u}

variable (l : List (α × Bool)) (p : ℕ)

/-- The label of the vertex at the position `p` of the cycle: even positions are corners of the
word and carry the base vertex of the rose, odd positions are midpoints of letters and carry the
midpoint of the loop of the corresponding generator. -/
def vertLab :=
  if p % 2 = 0 then Rose.base
  else
    match l[p / 2]? with
    | some q => Rose.mid q.1
    | none => Rose.base

/-- The label of the edge joining the positions `p` and `p+1` of the cycle: the first half of the
letter `p/2` for even `p`, its second half for odd `p`, the halves being taken in the order
prescribed by the sign of the letter. -/
def edgeLab : Rose α :=
  match l[p / 2]? with
  | some q => Rose.edg q.1 (if p % 2 = 0 then !q.2 else q.2)
  | none => Rose.base

variable {l : List (α × Bool)} {p : ℕ}

@[simp] theorem vertLab_of_even (hp : p % 2 = 0) :
    vertLab l p = Rose.base := if_pos hp

variable {q : α × Bool}

theorem vertLab_of_odd (hp : p % 2 = 1)
    (hq : l[p / 2]? = some q) : vertLab l p = Rose.mid q.1 := by
  simp [vertLab, hp, hq]

theorem edgeLab_eq (hq : l[p / 2]? = some q) :
    edgeLab l p = Rose.edg q.1 (if p % 2 = 0 then !q.2 else q.2) := by
  simp [edgeLab, hq]

section

variable (hp : p < 2 * l.length)
include hp

theorem getElem?_half :
    ∃ q, l[p / 2]? = some q :=
  ⟨l[p / 2]'(by omega), List.getElem?_eq_getElem _⟩

/-- The vertex at a position lies under the edge that starts at it. -/
theorem vertLab_le_edgeLab :
    vertLab l p ≤ edgeLab l p := by
  obtain ⟨q, hq⟩ := getElem?_half hp
  grind [vertLab_of_even, edgeLab_eq, Rose.base_le_edg, vertLab_of_odd, Rose.mid_le_edg]

end

/-- The vertex at the next position lies under the same edge. -/
theorem vertLab_succ_le_edgeLab (hp : p + 1 < 2 * l.length) :
    vertLab l (p + 1) ≤ edgeLab l p := by
  obtain ⟨q, hq⟩ := getElem?_half (Nat.lt_of_succ_lt hp)
  grind [vertLab_of_odd, edgeLab_eq, Rose.mid_le_edg, vertLab_of_even, Rose.base_le_edg]

/-- Every edge of the cycle carries a one-cell of the rose, so the base vertex lies under it. -/
theorem base_le_edgeLab (hp : p < 2 * l.length) :
    Rose.base ≤ edgeLab l p := by
  obtain ⟨q, hq⟩ := getElem?_half hp
  simp_all [edgeLab_eq]

/-! ### The label of a simplex -/

variable (l : List (α × Bool)) {M : ℕ}

section

variable {M : ℕ} {x y : Fin M} (hxy : x < y) (h : ({x, y} : Finset (Fin M)).Nonempty)
include hxy

end

end Labels

/-! ### The attaching map -/

section Att

variable {α : Type u}

variable (l : List (α × Bool)) (hl : 2 ≤ l.length)
include hl

end Att

end Davis
end FiniteChains
