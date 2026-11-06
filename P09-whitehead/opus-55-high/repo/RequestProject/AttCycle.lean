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

universe u

/-! ### The cycle graph -/




/-! ### The labels -/

section Labels

variable {α : Type u}

/-- The label of the vertex at the position `p` of the cycle: even positions are corners of the
word and carry the base vertex of the rose, odd positions are midpoints of letters and carry the
midpoint of the loop of the corresponding generator. -/
def vertLab (l : List (α × Bool)) (p : ℕ) : Rose α :=
  if p % 2 = 0 then Rose.base
  else
    match l[p / 2]? with
    | some q => Rose.mid q.1
    | none => Rose.base

/-- The label of the edge joining the positions `p` and `p+1` of the cycle: the first half of the
letter `p/2` for even `p`, its second half for odd `p`, the halves being taken in the order
prescribed by the sign of the letter. -/
def edgeLab (l : List (α × Bool)) (p : ℕ) : Rose α :=
  match l[p / 2]? with
  | some q => Rose.edg q.1 (if p % 2 = 0 then !q.2 else q.2)
  | none => Rose.base

@[simp] theorem vertLab_of_even {l : List (α × Bool)} {p} (hp : p % 2 = 0) :
    vertLab l p = Rose.base := if_pos hp

theorem vertLab_of_odd {p} {q : α × Bool} (hp : p % 2 = 1)
    (hq : l[p / 2]? = some q) : vertLab l p = Rose.mid q.1 := by
  simp [vertLab, hp, hq]

theorem edgeLab_eq {q : α × Bool} (hq : l[p / 2]? = some q) :
    edgeLab l p = Rose.edg q.1 (if p % 2 = 0 then !q.2 else q.2) := by
  simp [edgeLab, hq]

theorem getElem?_half {l : List (α × Bool)} {p} (hp : p < 2 * l.length) :
    ∃ q, l[p / 2]? = some q :=
  ⟨l[p / 2]'(by omega), by simp⟩

/-- The vertex at a position lies under the edge that starts at it. -/
theorem vertLab_le_edgeLab {l : List (α × Bool)} {p} (hp : p < 2 * l.length) :
    vertLab l p ≤ edgeLab l p := by
  cases' getElem?_half hp with q hq
  rcases p.even_or_odd with he | ho
  · have h0 := Nat.even_iff.1 he
    rw [vertLab_of_even h0, edgeLab_eq hq]
    simp
  · have h1 := Nat.odd_iff.1 ho
    rw [vertLab_of_odd h1 hq, edgeLab_eq hq]
    rfl

/-- The vertex at the next position lies under the same edge. -/
theorem vertLab_succ_le_edgeLab {l : List (α × Bool)} {p} (hp : p + 1 < 2 * l.length) :
    vertLab l (p + 1) ≤ edgeLab l p := by
  cases' getElem?_half (Nat.lt_of_succ_lt hp) with q hq
  rcases p.even_or_odd with he | ho
  · have h0 := Nat.even_iff.1 he
    have hhalf : (p + 1) / 2 = p / 2 := by omega
    rw [vertLab_of_odd (q := q) (by omega) (by simp_all), edgeLab_eq hq]
    rfl
  · have h1 := Nat.odd_iff.1 ho
    rw [vertLab_of_even (by omega), edgeLab_eq hq]
    simp

/-- Every edge of the cycle carries a one-cell of the rose, so the base vertex lies under it. -/
theorem base_le_edgeLab {p} (hp : p < 2 * l.length) :
    (Rose.base : Rose α) ≤ edgeLab l p := by
  cases' getElem?_half hp with q hq
  rw [edgeLab_eq hq]
  simp

/-! ### The label of a simplex -/







end Labels

/-! ### The attaching map -/
