module

public import proofs.HordijkSteelThreshold.WordContourLocality

public section

namespace HordijkSteelThreshold
open Classical SimpleGraph

/-- One end edit consumes at most one symbol of padding on either side. -/
theorem endWord_padding_step {u v core left right : List Bool} {k : ℕ}
    (hu : u = left ++ core ++ right) (hl : k + 1 ≤ left.length)
    (hr : k + 1 ≤ right.length) (ha : endWordGraph.Adj u v) :
    ∃ l r : List Bool, v = l ++ core ++ r ∧ k ≤ l.length ∧ k ≤ r.length := by
  obtain ⟨b, h | h | h | h⟩ := ha
  · grind
  · cases left with
    | nil => simp_all
    | cons c t =>
      grind
  · grind
  · have hn : right ≠ [] := by intro he; simp [he] at hr
    have hv := congrArg List.dropLast h
    grind

/-- A central word with padding at least the walk length cannot be erased by end edits. -/
theorem endWord_walk_protects_core {u v : List Bool} (p : endWordGraph.Walk u v)
    (core left right : List Bool) (hu : u = left ++ core ++ right)
    (hl : p.length ≤ left.length) (hr : p.length ≤ right.length) :
    ∃ l r : List Bool, v = l ++ core ++ r := by
  induction p generalizing left right with
  | nil => grind
  | @cons u v w ha p ih =>
    obtain ⟨l, r, hv, hpl, hpr⟩ := endWord_padding_step hu hl hr ha
    grind

end HordijkSteelThreshold
