module

public import Chazelle.Core.OraclePrepDedup

/-!
# Lemma 3.6 (WP-H), preprocessing part 17: the book data of the preprocessing

`graphOK_of`: the book with `A + 3` spine vertices, the star chords as inner chords and a list of
outer chords that has no repetition and contains exactly the raw zipper pairs, satisfies the
requirements `GraphOK` of the query.
-/

namespace Chazelle.Core

@[expose] public section

open OracleR OracleBook

namespace OracleQ

/-- **The book data of the preprocessing is correct.** -/
theorem graphOK_of {C : Chain} {Q : Polygon} {N : NF} (hN : IsNF (chainModel C) Q N)
    (hP : C.P.Simple) {D : List (ℕ × ℕ)} (hD : D.Nodup) (hDm : ∀ x, x ∈ D ↔ x ∈ zipRaw C Q N) :
    GraphOK C Q N ⟨N.arcs.length + 3, starList (rgi N) N.arcs.length, D⟩ where
  three_le := by simp
  arcs_le := by simp
  I_nodup := starList_nodup _ _
  O_nodup := hD
  I_ok := fun c hc => by
    obtain ⟨h1, h2, h3⟩ := mem_starList.1 hc
    refine ⟨by omega, by simp; omega, fun h => ?_⟩
    simp at h; omega
  O_ok := fun c hc => by
    obtain ⟨h1, h2, -⟩ := zipRaw_sound hN hP ((hDm c).1 hc)
    refine ⟨h1, by simp; omega, fun h => ?_⟩
    simp at h; omega
  I_star := fun c hc => by
    obtain ⟨h1, h2, h3⟩ := mem_starList.1 hc
    obtain ⟨f1, f2, f3⟩ := fpos_spec (rgi N) c.2
    refine ⟨by omega, h1, by rw [h2, f1], fun q _ hq => ?_⟩
    rw [h2] at hq ⊢
    exact f3 q (hq.trans f1)
  O_zip := fun c hc => by
    obtain ⟨h1, h2, h3⟩ := zipRaw_sound hN hP ((hDm c).1 hc)
    exact ⟨by omega, h2, h3⟩
  I_complete := fun p hp => by
    obtain ⟨f1, f2, f3⟩ := fpos_spec (rgi N) p
    refine ⟨fpos (rgi N) p, by omega, f1, fun q _ hq => f3 q hq, ?_⟩
    rcases starList_complete (rgi N) hp with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  O_complete := fun p q hpq hq hZ => by
    rcases zipRaw_complete hN hP hpq hq hZ with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl ((hDm _).2 h)

end OracleQ

end

end Chazelle.Core
