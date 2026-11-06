module

public import proofs.HordijkSteelThreshold.WordContourLocality

public section

namespace HordijkSteelThreshold
open Classical SimpleGraph

theorem endWord_strip_left (l s : List Bool) :
    ∃ p : endWordGraph.Walk (l ++ s) s, p.length = l.length := by
  induction l with
  | nil => simp_all
  | cons b l ih =>
    obtain ⟨p, hp⟩ := ih
    have ha : endWordGraph.Adj (b :: (l ++ s)) (l ++ s) := ⟨b, Or.inr $ Or.inl rfl⟩
    exact ⟨Walk.cons ha p, by simp_all⟩

theorem endWord_append_right (s r : List Bool) :
    ∃ p : endWordGraph.Walk s $ s ++ r, p.length = r.length := by
  induction r generalizing s with
  | nil => simp_all
  | cons b r ih =>
    obtain ⟨p, hp⟩ := ih $ s ++ [b]
    have ha : endWordGraph.Adj s (s ++ [b]) := ⟨b, Or.inr $ Or.inr $ Or.inl rfl⟩
    have h : ∃ q : endWordGraph.Walk s $ (s ++ [b]) ++ r, q.length = (b :: r).length :=
      ⟨Walk.cons ha p, by simp_all⟩
    grind

theorem endWord_strip_padding (l core r : List Bool) :
    ∃ p : endWordGraph.Walk (l ++ core ++ r) core, p.length = l.length + r.length := by
  obtain ⟨p, hp⟩ := endWord_strip_left l $ core ++ r
  obtain ⟨q, hq⟩ := endWord_append_right core r
  have h : ∃ w : endWordGraph.Walk (l ++ (core ++ r)) core,
      w.length = l.length + r.length :=
    ⟨p.append q.reverse, by simp_all⟩
  grind

/-- Explicit path through a common core, with an exact cancellation-free length identity. -/
theorem endWord_common_core_walk (u v core : List Bool)
    (hu : ∃ l r : List Bool, u = l ++ core ++ r)
    (hv : ∃ l r : List Bool, v = l ++ core ++ r) :
    ∃ p : endWordGraph.Walk u v, p.length + 2 * core.length = u.length + v.length := by
  obtain ⟨l, r, rfl⟩ := hu
  obtain ⟨a, b, rfl⟩ := hv
  obtain ⟨p, hp⟩ := endWord_strip_padding l core r
  obtain ⟨q, hq⟩ := endWord_strip_padding a core b
  refine ⟨p.append q.reverse, ?_⟩
  simp
  omega

theorem endWord_walk_length_bound {u v : List Bool} (p : endWordGraph.Walk u v) :
    v.length ≤ u.length + p.length := by
  induction p with
  | nil => simp
  | @cons u v w ha p ih =>
    have hv : v.length ≤ u.length + 1 := by
      obtain ⟨b, h | h | h | h⟩ := ha <;>
        have hh := congrArg List.length h <;>
        simp at hh <;> omega
    simp
    omega

end HordijkSteelThreshold
