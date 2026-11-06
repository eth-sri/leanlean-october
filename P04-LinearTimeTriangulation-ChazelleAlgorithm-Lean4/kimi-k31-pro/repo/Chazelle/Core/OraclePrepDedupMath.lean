module

public import Chazelle.Core.OraclePrepZipSp3

/-!
# Lemma 3.6 (WP-H), preprocessing part 15: removing repeated pairs from a sorted list

Pairs `pr i = (P1 i, P2 i)` (`i < n`), and a sequence `s` (`s t` for `t < n`) listing the indices
in lexicographic order of their pairs.  `dedupF`: keep position `t` iff it is the first or its pair
differs from that of `t - 1`.  The kept pairs have no repetition (`dedup_nodup`) and are exactly
the pairs (`mem_dedup`).
-/

namespace Chazelle.Core

namespace OracleR

@[expose] public section

/-- Lexicographic order of pairs. -/
def PLe (x y : ℕ × ℕ) : Prop := x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)

theorem PLe.antisymm {x y : ℕ × ℕ} (h : PLe x y) (h' : PLe y x) : x = y := by
  unfold PLe at *; ext <;> omega

open Classical in
/-- The kept pair at position `t`. -/
noncomputable def dedupF (n : ℕ) (pr : ℕ → ℕ × ℕ) (s : ℕ → ℕ) (t : ℕ) : Option (ℕ × ℕ) :=
  if t < n ∧ (t = 0 ∨ pr (s t) ≠ pr (s (t - 1))) then some (pr (s t)) else none

/-- A sorted sequence: pairs increase along positions. -/
def SortedSeq (pr : ℕ → ℕ × ℕ) (s : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ t t', t ≤ t' → t' < n → PLe (pr (s t)) (pr (s t'))

theorem dedup_key {pr : ℕ → ℕ × ℕ} {s : ℕ → ℕ} {n : ℕ} (hs : SortedSeq pr s n) {a a' : ℕ}
    {b : ℕ × ℕ} (hlt : a < a') (h1 : dedupF n pr s a = some b) (h2 : dedupF n pr s a' = some b) :
    False := by
  unfold dedupF at h1 h2
  split_ifs at h1 h2 with c1 c2
  have e  := (Option.some.inj h1).trans (Option.some.inj h2).symm
  obtain ⟨ha', c2⟩ := c2
  rcases c2 with c2 | c2
  · omega
  · have e1 := hs a (a' - 1) (by omega) (by omega)
    have e2 := hs (a' - 1) a' (by omega) ha'
    rw [e] at e1
    exact c2 (PLe.antisymm e2 e1).symm

theorem dedup_nodup {pr : ℕ → ℕ × ℕ} {s : ℕ → ℕ} {n : ℕ} (hs : SortedSeq pr s n) :
    (emitted (dedupF n pr s) n).Nodup := by
  unfold emitted
  refine List.Nodup.filterMap (fun a a' b hb hb' => ?_) List.nodup_range
  rcases lt_trichotomy a a' with h | h | h
  · exact absurd (dedup_key hs h hb hb') id
  · exact h
  · exact absurd (dedup_key hs h hb' hb) id

theorem mem_dedup {pr : ℕ → ℕ × ℕ} {s : ℕ → ℕ} {n : ℕ} (hsurj : ∀ i, i < n → ∃ t, t < n ∧ s t = i)
    (hlt : ∀ t, t < n → s t < n) {x : ℕ × ℕ} :
    x ∈ emitted (dedupF n pr s) n ↔ ∃ i, i < n ∧ pr i = x := by
  rw [mem_emitted]
  constructor
  · rintro ⟨t, ht, h⟩
    unfold dedupF at h
    split_ifs at h
    cases h
    exact ⟨s t, hlt t ht, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    classical
    have hex : ∃ t, t < n ∧ pr (s t) = pr i := by
      obtain ⟨t, ht, e⟩ := hsurj i hi; exact ⟨t, ht, by rw [e]⟩
    let t0 := Nat.find hex
    obtain ⟨h0, e0⟩ := Nat.find_spec hex
    refine ⟨t0, h0, ?_⟩
    have hcond : t0 = 0 ∨ pr (s t0) ≠ pr (s (t0 - 1)) := by
      by_cases hz : t0 = 0
      · exact Or.inl hz
      · right
        intro e
        have := Nat.find_min hex (show t0 - 1 < t0 by omega)
        exact this ⟨by omega, by rw [← e, e0]⟩
    unfold dedupF
    rw [ite_eq_left ⟨h0, hcond⟩, e0]

end

end OracleR

end Chazelle.Core
