module

public import proofs.HordijkSteelThreshold.WordContourLocality

@[expose] public section

namespace HordijkSteelThreshold
open Classical SimpleGraph

theorem endWord_common_core_walk (u v core : List Bool)
    (hu : ∃ l r : List Bool, u = l ++ core ++ r)
    (hv : ∃ l r : List Bool, v = l ++ core ++ r) :
    ∃ p : endWordGraph.Walk u v, p.length + 2 * core.length = u.length + v.length := by
  have strip (l r : List Bool) : ∃ p : endWordGraph.Walk (l ++ core ++ r) core, p.length = l.length + r.length := by
    induction l with
    | nil =>
      induction r using List.reverseRecOn with
      | nil => simp
      | append_singleton r b ih =>
        obtain ⟨p, hp⟩ := ih
        have ha : endWordGraph.Adj ([] ++ core ++ (r ++ [b])) ([] ++ core ++ r) :=
          ⟨b, Or.inr (Or.inr (Or.inr (by simp [List.append_assoc])))⟩
        exact ⟨Walk.cons ha p, by simp [hp]⟩
    | cons b l ih =>
      obtain ⟨p, hp⟩ := ih
      have ha : endWordGraph.Adj ((b :: l) ++ core ++ r) (l ++ core ++ r) := ⟨b, Or.inr (Or.inl rfl)⟩
      exact ⟨Walk.cons ha p, by simp [hp]; omega⟩
  obtain ⟨l, r, rfl⟩ := hu
  obtain ⟨a, b, rfl⟩ := hv
  obtain ⟨p, hp⟩ := strip l r
  obtain ⟨q, hq⟩ := strip a b
  exact ⟨p.append q.reverse, by simp [hp, hq]; omega⟩

theorem endWord_walk_length_bound {u v : List Bool} (p : endWordGraph.Walk u v) :
    v.length ≤ u.length + p.length := by
  induction p with
  | nil => simp
  | @cons u v w ha p ih =>
    have hv : v.length ≤ u.length + 1 := by
      rcases ha with ⟨b, rfl | rfl | rfl | rfl⟩ <;> simp <;> omega
    simp only [Walk.length_cons]; omega

end HordijkSteelThreshold
