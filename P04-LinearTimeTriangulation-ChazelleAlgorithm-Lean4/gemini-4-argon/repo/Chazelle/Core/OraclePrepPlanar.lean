module

public import Chazelle.Core.OraclePrepRotMath

/-!
# Lemma 3.6 (WP-H), preprocessing part 19: the book map in memory

* `sortedDarts_of`: a sorted enumeration (non-strict) of darts with injective (vertex, key) pairs
  is strictly sorted;
* `rot_eq_csucc`: the rotation of the sorted darts is the rotation `csucc` of the book map;
* `planarMapAt_of_arrays`: arrays holding the opposite dart, the rotation and the vertex of every
  dart of a valid book describe a planar map (`PlanarMapAt`).
-/

namespace Chazelle.Core

namespace OracleR

open OracleBook OracleBook.BookData

@[expose] public section

theorem inj_of_surj {M : ℕ} {s : ℕ → ℕ} (hlt : ∀ t, t < M → s t < M)
    (hs : ∀ d, d < M → ∃ t, t < M ∧ s t = d) {t t' : ℕ} (ht : t < M) (ht' : t' < M)
    (h : s t = s t') : t = t' := by
  let f : Fin M → Fin M := fun x => ⟨s x, hlt x x.2⟩
  have hsurj : Function.Surjective f := fun d => by
    obtain ⟨t, ht, e⟩ := hs d d.2
    exact ⟨⟨t, ht⟩, Fin.ext e⟩
  have hinj := Finite.injective_iff_surjective.2 hsurj
  have := hinj (a₁ := ⟨t, ht⟩) (a₂ := ⟨t', ht'⟩) (Fin.ext h)
  exact congrArg Fin.val this

theorem sortedDarts_of {M : ℕ} {G K s : ℕ → ℕ}
    (hsort : SortedSeq (fun d => (G d, K d)) s M) (hlt : ∀ t, t < M → s t < M)
    (hs : ∀ d, d < M → ∃ t, t < M ∧ s t = d)
    (hinj : ∀ d d', d < M → d' < M → G d = G d' → K d = K d' → d = d') :
    SortedDarts M G K s := by
  refine ⟨hlt, hs, fun t t' htt ht' => ?_⟩
  have h := hsort t t' htt.le ht'
  unfold PLe at h; unfold PLt; simp only at h ⊢
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · rcases eq_or_lt_of_le h2 with e | e
    · have := hinj _ _ (hlt t (by omega)) (hlt t' ht') h1 e
      exact absurd (inj_of_surj hlt hs (by omega) ht' this) (by omega)
    · exact Or.inr ⟨h1, e⟩

variable {B : BookData}

/-- **The rotation of the sorted darts is the rotation of the book map.** -/
theorem rot_eq_csucc (hV : B.Valid) {s : ℕ → ℕ}
    (h : SortedDarts (2 * B.E) (fun d => View.tail B.N (B.view d)) (fun d => View.key B.N (B.view d)) s)
    {t : ℕ} (ht : t < 2 * B.E) :
    (csucc (gN (B := B)) (kN (B := B)) ⟨s t, h.lt t ht⟩).1 =
      rotN (2 * B.E) (fun d => View.tail B.N (B.view d)) s t := by
  obtain ⟨hl, hg, hc⟩ := rotN_spec h ht
  have := csucc_eq (keyInj hV) (d := ⟨s t, h.lt t ht⟩) (e := ⟨_, hl⟩) hg (by
    rcases hc with ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inl ⟨a, fun f hf hk => b f.1 f.2 hf hk⟩
    · exact Or.inr ⟨fun f hf => a f.1 f.2 hf, fun f hf => b f.1 f.2 hf⟩)
  rw [this]

/-- **The book map in memory is a planar map.** -/
theorem planarMapAt_of_arrays (hV : B.Valid) {m : ℕ → ℕ} {Bh : ℕ}
    (hopp : ∀ d, d < 2 * B.E → m (m Bh + d) = oppN d)
    (hrot : ∀ d (hd : d < 2 * B.E), m (m (Bh + 1) + d) = (csucc (gN (B := B)) (kN (B := B)) ⟨d, hd⟩).1)
    (hvt : ∀ d, d < 2 * B.E → m (m (Bh + 2) + d) = View.tail B.N (B.view d)) :
    PlanarMapAt m Bh B.N B.E :=
  ⟨FaceT hV, inferInstance, inferInstance, B.map hV, B.planar hV,
    fun d => ⟨hopp d d.2, hrot d d.2, hvt d d.2⟩⟩

/-- **The graph of the map in memory is the graph of the book.** -/
theorem memGraph_eq {m : ℕ → ℕ} {Bh : ℕ}
    (hopp : ∀ d, d < 2 * B.E → m (m Bh + d) = oppN d)
    (hvt : ∀ d, d < 2 * B.E → m (m (Bh + 2) + d) = View.tail B.N (B.view d)) :
    memGraph m Bh B.N B.E = OracleQ.bookGraph B := by
  have hdart : ∀ u v : ℕ, MemDart m Bh B.E u v ↔ OracleQ.BookAdj B u v := by
    intro u v
    constructor
    · rintro ⟨d, hd, h1, h2⟩
      refine ⟨d, hd, by rw [← h1, hvt d hd], ?_⟩
      rwa [hopp d hd, hvt _ (oppN_lt hd), view_oppN, View.tail_rev] at h2
    · rintro ⟨d, hd, h1, h2⟩
      refine ⟨d, hd, by rw [hvt d hd, h1], ?_⟩
      rw [hopp d hd, hvt _ (oppN_lt hd), view_oppN, View.tail_rev, h2]
  ext u v
  simp only [memGraph, OracleQ.bookGraph, hdart]

end

end OracleR

end Chazelle.Core
