module

public import proofs.HordijkSteelThreshold.WordContourLocality

@[expose] public section

namespace HordijkSteelThreshold
open Classical SimpleGraph

theorem wordContour_protected_core {L N : ℕ} (C : Finset (WordBasicEdge L N))
    (hsub : C ⊆ wordBasicEdges L N) (e : WordBasicEdge L N) (he : e ∈ C)
    (hconn : ∀ d ∈ C, wordContourReach C e d)
    (core left right : List Bool) (ha : e.1.val = left ++ core ++ right)
    (hl : 4 * (C.card - 1) ≤ left.length) (hr : 4 * (C.card - 1) ≤ right.length)
    (d : WordBasicEdge L N) (hd : d ∈ C) :
    ∃ l r : List Bool, d.1.val = l ++ core ++ r := by
  obtain ⟨p, hp⟩ := wordContour_product_locality C hsub e he hconn d hd
  have hwalk {u v : List Bool} (p : endWordGraph.Walk u v)
      (left right : List Bool) (hu : u = left ++ core ++ right)
      (hl : p.length ≤ left.length) (hr : p.length ≤ right.length) :
      ∃ l r : List Bool, v = l ++ core ++ r := by
    induction p generalizing left right with
    | nil => exact ⟨left, right, hu⟩
    | @cons u v w ha p ih =>
      simp only [Walk.length_cons] at hl hr
      rcases ha with ⟨b, rfl | rfl | rfl | h⟩
      · exact ih (b :: left) right (by simp [hu]) (by simp; omega) (by omega)
      · rcases left with _ | ⟨c, t⟩; · simp at hl
        exact ih t right (by simpa [List.append_assoc] using congrArg List.tail hu) (by simp at hl; omega) (by omega)
      · exact ih left (right ++ [b]) (by simp [hu, List.append_assoc]) (by omega) (by simp; omega)
      · have hn : right ≠ [] := fun he => by simp [he] at hr
        have hv := congrArg List.dropLast h
        rw [hu, (List.dropLast_append_getLast hn).symm] at hv
        simp only [← List.append_assoc, List.dropLast_concat] at hv
        exact ih left right.dropLast hv.symm (by omega) (by simp; omega)
  exact hwalk p left right ha (hp.trans hl) (hp.trans hr)

end HordijkSteelThreshold
