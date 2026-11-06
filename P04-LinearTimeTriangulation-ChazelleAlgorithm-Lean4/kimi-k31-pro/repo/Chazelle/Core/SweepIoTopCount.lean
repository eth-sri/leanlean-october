module

public import Chazelle.Core.SweepIoSpec
public import Chazelle.Core.SweepEvOrgM
public import Chazelle.SimpTactics

/-!
# The sweep RAM (WP-D), answers: endpoint queries at the top of `C₂` (`TopCountSpec`)

**`topCount : TopCountSpec`**: at most two endpoint queries of a normal form `N₂` of the model of
`C₂` have the top of `C₂` as origin.  The origin of an even query is the left end of its chord, of
an odd one the right end; a horizontal chord of the domain is determined by its height and one end
(`hchord_right_eq`, `hchord_left_eq`), and the chord sets of a normal form are distinct, so two
queries of the same parity with the same origin are equal (`endOrigin_inj`).
-/

namespace Chazelle.Core

namespace SweepIo

open Set
open Chazelle.Chain (IsHChordIn)
open Sweep

@[expose] public section

/-- A horizontal chord of a domain is determined by its height and its left end. -/
theorem hchord_right_eq {D : Set Point} {y a b b' : ℝ} (h : IsHChordIn D y a b)
    (h' : IsHChordIn D y a b') : b = b' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact h.right_not (h'.open_mem b h.lt hlt)
  · exact h'.right_not (h.open_mem b' h'.lt hlt)

/-- A horizontal chord of a domain is determined by its height and its right end. -/
theorem hchord_left_eq {D : Set Point} {y a a' b : ℝ} (h : IsHChordIn D y a b)
    (h' : IsHChordIn D y a' b) : a = a' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact h'.left_not (h.open_mem a' hlt h'.lt)
  · exact h.left_not (h'.open_mem a hlt h.lt)

/-- The chord records of a normal form of a chain model are augmented chords. -/
theorem chord_aug {C : Chain} {Q : Polygon} {N : NF} (hN : IsNF (chainModel C) Q N) {k : ℕ}
    (hk : k < N.nChords) :
    ∃ y a b : ℝ, IsHChordIn C.dom y a b ∧ (N.chord k).toSet (chainModel C) Q = Visibility.hseg y a b ∧
      Merge.lend ((N.chord k).toSet (chainModel C) Q) = (a, y) ∧
      Merge.rend ((N.chord k).toSet (chainModel C) Q) = (b, y) := by
  have hmem : (N.chord k).toSet (chainModel C) Q ∈ N.F (chainModel C) Q := by
    refine ⟨N.chord k, ?_, rfl⟩
    unfold NF.chord
    rw [NFLoc.getD_of_lt _ hk]
    exact List.getElem_mem _
  obtain ⟨y, a, b, hH, -, heq, hl, hr⟩ :=
    Merge.augChords_spec (show _ ∈ Merge.augChords C from hN.1.2.1 hmem)
  exact ⟨y, a, b, hH, heq, hl, hr⟩

/-- Two endpoint queries of the same parity with the same origin are equal. -/
theorem endOrigin_inj {J : Merge.Junction} {Q : Polygon} {N : NF}
    (hN : IsNF (chainModel J.right) Q N) {j j' : ℕ} (hj : j < 2 * N.nChords)
    (hj' : j' < 2 * N.nChords) (hp : j % 2 = j' % 2)
    (h : endOrigin J Q N j = endOrigin J Q N j') : j = j' := by
  obtain ⟨y, a, b, hH, heq, hl, hr⟩ := chord_aug hN (k := j / 2) (by omega)
  obtain ⟨y', a', b', hH', heq', hl', hr'⟩ := chord_aug hN (k := j' / 2) (by omega)
  have hset : (N.chord (j / 2)).toSet (chainModel J.right) Q =
      (N.chord (j' / 2)).toSet (chainModel J.right) Q := by
    rcases Nat.mod_two_eq_zero_or_one j with h0 | h1
    · simp only [endOrigin, h0, show j' % 2 = 0 by omega, ↓reduceIte, hl, hl'] at h
      obtain ⟨e1, e2⟩ := Prod.mk.inj h
      subst e1; subst e2
      rw [heq, heq', hchord_right_eq hH hH']
    · simp only [endOrigin, h1, show j' % 2 = 1 by omega, Nat.one_ne_zero, ↓reduceIte, hr,
        hr'] at h
      obtain ⟨e1, e2⟩ := Prod.mk.inj h
      subst e1; subst e2
      rw [heq, heq', hchord_left_eq hH hH']
  have := hN.2.1 _ _ (by omega) (by omega) hset
  omega

/-- **At most two endpoint queries start at the top of `C₂`.** -/
theorem topCount : TopCountSpec := by
  intro P J N₂ _ _ hN
  classical
  set l := (List.range (2 * N₂.nChords)).filter
    (fun j => decide (endOrigin J (Qof P) N₂ j = J.right.top)) with hl
  have hnd : l.Nodup := (List.nodup_range).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  have hmem : ∀ j ∈ l.toFinset, j < 2 * N₂.nChords ∧ endOrigin J (Qof P) N₂ j = J.right.top := by
    intro j hj
    rw [List.mem_toFinset, hl, List.mem_filter, List.mem_range, decide_eq_true_eq] at hj
    exact hj
  calc l.toFinset.card ≤ (Finset.range 2).card :=
        Finset.card_le_card_of_injOn (fun j => j % 2)
          (fun j _ => by sio only [Finset.coe_range, Set.mem_Iio])
          (fun j hj j' hj' h => by
            obtain ⟨h1, h2⟩ := hmem j hj
            obtain ⟨h1', h2'⟩ := hmem j' hj'
            exact endOrigin_inj hN h1 h1' h (h2.trans h2'.symm))
    _ = 2 := Finset.card_range 2

end

end SweepIo

end Chazelle.Core
