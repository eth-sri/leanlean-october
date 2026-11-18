module

public import Chazelle.Core.ClusterStar
public import Chazelle.Core.ClusterCentroid

/-!
# WP-I, part 16: separators in the star map

For a map `M`, a spanning tree `T` and attachment darts `a g ∈ g`, in the star map with the tree
`starTree T a`:

* ancestry: `starTree_isAnc_inl` (between real vertices it is ancestry in `T`),
  `starTree_isAnc_inr` (the ancestors of a centre are the centre and the ancestors of its
  corner);
* `star_mem_sepSet_inl`: a real vertex `v` is in the separator of the star face `f` (an old dart)
  iff it is a `T`-ancestor of `vert f`, of `head f` or of `vert (a (face f))`;
* `starDarts`: the three darts `inl f`, `inr (inr (fperm f))`, `inr (inl f)` of the star face `f`
  (`star_face_iff`, `starDarts_inj`);
* `star_sep_card`: the separator meets a set of real vertices whose `T`-levels lie in a window of
  `k` consecutive levels in at most `3 k` vertices.
-/

namespace Chazelle.Core.Cluster

open Chazelle.Separator Chazelle.Separator.CombMap Equiv

@[expose] public section

variable {V F D : Type*} [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F] [Fintype D]
  [DecidableEq D] {M : CombMap V F D} (T : SpanTree M) (a : F → D) (ha : ∀ g, M.face (a g) = g)

omit [Fintype V] [Fintype F] [DecidableEq D] in
theorem starTree_parent_inl (v : V) :
    (starTree T a ha).parent (.inl v) = .inl (T.parent v) := by
  unfold SpanTree.parent
  by_cases hv : v = T.root
  · subst hv; simp [starTree]
  · have : (Sum.inl v : V ⊕ F) ≠ (starTree T a ha).root := by simp [starTree, hv]
    rw [ite_eq_right this, ite_eq_right hv]
    rfl

omit [Fintype V] [Fintype F] [DecidableEq D] in
theorem starTree_parent_inr (g : F) :
    (starTree T a ha).parent (.inr g) = .inl (M.vert (a g)) := by
  unfold SpanTree.parent
  have : (Sum.inr g : V ⊕ F) ≠ (starTree T a ha).root := by simp [starTree]
  rw [ite_eq_right this]
  rfl

omit [Fintype V] [Fintype F] [DecidableEq D] in
theorem starTree_iterate_inl (n : ℕ) (v : V) :
    (starTree T a ha).parent^[n] (.inl v) = .inl (T.parent^[n] v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, starTree_parent_inl, ih, Function.iterate_succ_apply]

omit [Fintype V] [Fintype F] [DecidableEq D] in
/-- Ancestry between real vertices is ancestry in `T`. -/
theorem starTree_isAnc_inl (v u : V) :
    (starTree T a ha).IsAnc (.inl v) (.inl u) ↔ T.IsAnc v u := by
  constructor
  · rintro ⟨n, hn⟩
    rw [starTree_iterate_inl] at hn
    exact ⟨n, Sum.inl_injective hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [starTree_iterate_inl, hn]⟩

omit [Fintype V] [Fintype F] [DecidableEq D] in
/-- A real vertex is an ancestor of a centre iff it is an ancestor of its corner. -/
theorem starTree_isAnc_inr (v : V) (g : F) :
    (starTree T a ha).IsAnc (.inl v) (.inr g) ↔ T.IsAnc v (M.vert (a g)) := by
  constructor
  · rintro ⟨n, hn⟩
    rcases n with _ | n
    · simp at hn
    · rw [Function.iterate_succ_apply, starTree_parent_inr, starTree_iterate_inl] at hn
      exact ⟨n, Sum.inl_injective hn⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, by rw [Function.iterate_succ_apply, starTree_parent_inr,
      starTree_iterate_inl, hn]⟩

/-- The three darts of the star face `f`. -/
def starDarts (f : D) : ℕ → D ⊕ D ⊕ D
  | 0 => .inl f
  | 1 => .inr (.inr (M.fperm f))
  | _ => .inr (.inl f)

omit [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F] [DecidableEq D] in
/-- The darts of the star face `f` are the three `starDarts f t`. -/
theorem star_face_iff (f : D) (e : D ⊕ D ⊕ D) :
    (star M).face e = f ↔ ∃ t, t < 3 ∧ starDarts (M := M) f t = e := by
  constructor
  · intro h
    rcases e with d | d | d
    · exact ⟨0, by omega, by simp only [star_face, starFace_inl] at h; subst h; rfl⟩
    · exact ⟨2, by omega, by simp only [star_face, starFace_inl_inr] at h; subst h; rfl⟩
    · refine ⟨1, by omega, ?_⟩
      simp only [star_face, starFace_inr_inr] at h
      subst h
      simp [starDarts]
  · rintro ⟨t, ht, rfl⟩
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega) with rfl | rfl | rfl <;> simp [starDarts]

omit [Fintype V] [DecidableEq V] [Fintype F] [DecidableEq F] [Fintype D] [DecidableEq D] in
theorem starDarts_inj (f : D) {t t' : ℕ} (ht : t < 3) (ht' : t' < 3)
    (h : starDarts (M := M) f t = starDarts (M := M) f t') : t = t' := by
  rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega) with rfl | rfl | rfl <;>
    rcases (show t' = 0 ∨ t' = 1 ∨ t' = 2 by omega) with rfl | rfl | rfl <;>
    simp_all [starDarts]

omit [DecidableEq D] in
/-- **The separator of a star face**, restricted to real vertices. -/
theorem star_mem_sepSet_inl (f : D) (v : V) :
    (Sum.inl v : V ⊕ F) ∈ (starTree T a ha).sepSet f ↔
      T.IsAnc v (M.vert f) ∨ T.IsAnc v (M.head f) ∨ T.IsAnc v (M.vert (a (M.face f))) := by
  rw [SpanTree.mem_sepSet]
  constructor
  · rintro ⟨e, he, hanc⟩
    obtain ⟨t, ht, rfl⟩ := (star_face_iff f e).mp he
    rcases (show t = 0 ∨ t = 1 ∨ t = 2 by omega) with rfl | rfl | rfl
    · left; simpa [starDarts, starTree_isAnc_inl] using hanc
    · right; left
      simp only [starDarts, star_vert, starVert_inr_inr] at hanc
      rw [starTree_isAnc_inl, M.vert_fperm] at hanc
      exact hanc
    · right; right
      simp only [starDarts, star_vert, starVert_inl_inr] at hanc
      exact (starTree_isAnc_inr T a ha v _).mp hanc
  · rintro (h | h | h)
    · exact ⟨.inl f, rfl, by simpa [starTree_isAnc_inl] using h⟩
    · refine ⟨.inr (.inr (M.fperm f)), ?_, ?_⟩
      · simp
      · simp only [star_vert, starVert_inr_inr]
        rw [starTree_isAnc_inl, M.vert_fperm]; exact h
    · exact ⟨.inr (.inl f), rfl, (starTree_isAnc_inr T a ha v _).mpr h⟩

/-- **The separator in a slab**: at most `3 k` real vertices whose levels (shifted by `c`) lie in
a window of `k` levels. -/
theorem star_sep_card (f : D) (c j k : ℕ) (S : Finset V)
    (hS : ∀ v ∈ S, j * k ≤ T.level v + c ∧ T.level v + c < j * k + k) :
    (S.filter (fun v => (Sum.inl v : V ⊕ F) ∈ (starTree T a ha).sepSet f)).card ≤ 3 * k := by
  classical
  have h := (starTree T a ha).card_sepSet_filter_shift_le f c (Finset.Ico (j * k) (j * k + k))
  rw [star_faceDeg, Nat.card_Ico, show j * k + k - j * k = k by omega] at h
  refine le_trans ?_ h
  rw [← Finset.card_map Function.Embedding.inl]
  refine Finset.card_le_card (fun x hx => ?_)
  obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hx
  rw [Finset.mem_filter] at hv ⊢
  refine ⟨hv.2, ?_⟩
  rw [Finset.mem_Ico]
  exact hS v hv.1

end

end Chazelle.Core.Cluster
