module

public import Chazelle.Golf

public import Chazelle.Core.Lemma41Desc

/-!
# WP-J, part 5: the whole-polygon host

`Host.whole n = [run 0 (n - 1)]` is regular (every host edge is an edge of `Q`) and well formed,
and describes `Q` itself (`Brute.poly_whole` in WP-K; restated here to avoid the dependency).
-/

namespace Chazelle.Core.L41

@[expose] public section

theorem whole_pts_getD {n i : ℕ} (hi : i < n) :
    ((Host.whole n).pts n).getD i (.vtx 0) = .vtx i := by
  simp only [Host.whole, Host.pts, HostItem.pts, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, zero_add]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (⋄)]
  Θ Nat.mod_eq_of_lt hi

/-- **The whole host is regular.** -/
theorem hostRegular_whole {n : ℕ} (hn : 1 ≤ n) : HostRegular n (Host.whole n) := by
  intro i hi
  rw [Host.whole_pts_length n hn] at hi ⊢
  rw [whole_pts_getD hi, whole_pts_getD (Nat.mod_lt _ (⋄))]
  exact Or.inl rfl

/-- The whole host is well formed. -/
theorem hostWF_whole {n : ℕ} (hn : 1 ≤ n) : HostWF n (Host.whole n) := by
  intro it hit
  simp only [Host.whole, List.mem_singleton] at hit
  subst hit
  exact ⟨hn, ⋄⟩

/-- The whole host describes the polygon. -/
theorem poly_whole (Q : Polygon) (hQ : 1 ≤ Q.n) : (Host.whole Q.n).poly Q = Q := by
  cases Q with
  | mk l =>
    unfold Host.poly Host.whole Host.pts HostItem.pts
    ϴ List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map, zero_add
    congr 1
    have hn : (⟨l⟩ : Polygon).n = l.length := rfl
    have hQ' : 1 ≤ l.length := hQ
    Ξ hn
    apply List.ext_getElem
    · simp; omega
    · intro i h1 h2
      ϴ List.getElem_map, List.getElem_range, Function.comp
      simp only [List.length_map, List.length_range] at h1
      rw [Nat.mod_eq_of_lt (⋄)]
      ϴ SymPt.eval, Polygon.vtx
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl

end

end Chazelle.Core.L41
