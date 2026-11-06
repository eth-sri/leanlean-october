module

public import Chazelle.Core.NFBuildValid

/-!
# WP-C (BuildNF): the comparator of the event sort

The machine sorts the event codes (`2 i`: left endpoint of chord `i`, `2 i + 1`: right endpoint)
with a comparator made of one walk-key comparison (`WalkKey.keyCmp`) and, at equal keys, one bit:
the **tie bit** `tieBit M L c` (the parity of the code, flipped when the walk edge of the position
goes down; `WalkKey.dirCode` computes the direction by one height test).

**Main result** `sorted_of_codeLe`: if the codes are sorted by `codeLe` (key, then tie bit), the
events are sorted by `BuildSort.EvLe` (key, then the cyclic tie rule), so `BuildNF.Input` holds
and the computed normal form is valid (`BuildNF.Input.isNF`).  The proof is the tie fact: equal
keys are the same walk position, the two chords attached there go east (the left-endpoint event)
and west (the right-endpoint event), and at a vertex whose leaving edge goes down the west chord's
event has the larger cyclic distance (`BuildOrder.tie_rule_down`), up: the east chord's
(`BuildOrder.tie_rule_up`).
-/

namespace Chazelle.Core

namespace BuildNF

@[expose] public section

open Set List
open Chazelle.Chain (SideAttach sideInArc sidePt sideKey_inj)
open BuildSort (Ev EvLe kap cycDist)
open BuildOrder (chordSet chordSet_mem chordSet_inj getD_mem)
open BuildRegions (eL eR crec famOf kl kr)

/-- **The tie bit** of an event code: its parity, flipped when the walk edge of its position goes
down. -/
noncomputable def tieBit (M : Model) (L : List (ℕ × ℕ × ℕ)) (c : ℕ) : ℕ :=
  if (M.wb (wposOf L c).edge).2 < (M.wa (wposOf L c).edge).2 then 1 - c % 2 else c % 2

/-- **The comparator of the event sort**: by key, then by tie bit. -/
def codeLe (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (c c' : ℕ) : Prop :=
  M.key Q (wposOf L c) < M.key Q (wposOf L c') ∨
    (M.key Q (wposOf L c) = M.key Q (wposOf L c') ∧ tieBit M L c ≤ tieBit M L c')

/-- The comparator is total. -/
theorem codeLe_total (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (c c' : ℕ) :
    codeLe M Q L c c' ∨ codeLe M Q L c' c := by
  unfold codeLe
  rcases lt_trichotomy (M.key Q (wposOf L c)) (M.key Q (wposOf L c')) with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases le_total (tieBit M L c) (tieBit M L c') with h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
  · exact Or.inr (Or.inl h)

/-- The comparator is transitive. -/
theorem codeLe_trans (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) {a b c : ℕ}
    (h1 : codeLe M Q L a b) (h2 : codeLe M Q L b c) : codeLe M Q L a c := by
  unfold codeLe at *
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · exact Or.inl (h1.trans h2)
  · exact Or.inl (h2 ▸ h1)
  · exact Or.inl (h1 ▸ h2)
  · exact Or.inr ⟨h1.trans h2, h1'.trans h2'⟩

variable {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)}

/-- The attachment of the position of an event code. -/
theorem attach_wposOf (hL : ChordTriplesOK M Q L) {c : ℕ} (hc : c < 2 * L.length) :
    SideAttach M.W (chordSet M Q L (c / 2)) (wposOf L c).edge (M.param Q (wposOf L c)) := by
  have hi : c / 2 < L.length := by omega
  have hatt := hL.2.2.1 _ (getD_mem hi)
  unfold wposOf
  split_ifs
  · exact hatt.1
  · exact hatt.2

theorem wposOf_even {c : ℕ} (hc : c % 2 = 0) : wposOf L c = (crec L (c / 2)).lpos := by
  unfold wposOf; rw [ite_eq_left hc]

theorem wposOf_odd {c : ℕ} (hc : c % 2 = 1) : wposOf L c = (crec L (c / 2)).rpos := by
  unfold wposOf; rw [ite_eq_right (by omega)]

theorem evOf_even {c : ℕ} (hc : c % 2 = 0) : evOf M Q L c = eL M Q L (c / 2) := by
  unfold evOf; rw [ite_eq_left hc]

theorem evOf_odd {c : ℕ} (hc : c % 2 = 1) : evOf M Q L c = eR M Q L (c / 2) := by
  unfold evOf; rw [ite_eq_right (by omega)]

/-- The left endpoint is left of the right endpoint (for a chord of a valid list). -/
theorem pos_lt' (hM : WalkAx M) (hL : ChordTriplesOK M Q L) {i : ℕ} (hi : i < L.length) :
    (M.pos Q (crec L i).lpos).1 < (M.pos Q (crec L i).rpos).1 :=
  BuildOrder.endpoints hM (hL.1.2.1 (chordSet_mem hi)) (hL.2.2.1 _ (getD_mem hi))

/-- **The tie between a left-endpoint event and a right-endpoint event at one position.** -/
theorem tie_codes (hM : WalkAx M) (hL : ChordTriplesOK M Q L) {e o : ℕ}
    (he : e < 2 * L.length) (ho : o < 2 * L.length) (hee : e % 2 = 0) (hoo : o % 2 = 1)
    (_hij : e / 2 ≠ o / 2) (hpe : (wposOf L e).edge = (wposOf L o).edge)
    (hpt : M.param Q (wposOf L e) = M.param Q (wposOf L o)) :
    (M.wb (wposOf L e).edge).2 ≠ (M.wa (wposOf L e).edge).2 ∧
      ((M.wb (wposOf L e).edge).2 < (M.wa (wposOf L e).edge).2 →
        cycDist M.W.n (evOf M Q L e).2.1 (evOf M Q L e).2.2 <
          cycDist M.W.n (evOf M Q L o).2.1 (evOf M Q L o).2.2) ∧
      ((M.wa (wposOf L e).edge).2 < (M.wb (wposOf L e).edge).2 →
        cycDist M.W.n (evOf M Q L o).2.1 (evOf M Q L o).2.2 <
          cycDist M.W.n (evOf M Q L e).2.1 (evOf M Q L e).2.2) := by
  set i := e / 2
  set i' := o / 2
  have hi : i < L.length := by omega
  have hi' : i' < L.length := by omega
  have hadm : famOf M Q L ⊆ M.Adm := hL.1.2.1
  have hfin : (famOf M Q L).Finite := hL.1.1
  have hattI := hL.2.2.1 _ (getD_mem hi)
  have hattI' := hL.2.2.1 _ (getD_mem hi')
  -- the common position
  set p := (crec L i).lp
  set t := M.param Q (crec L i).lpos
  have hpos' : (crec L i').rp = p ∧ M.param Q (crec L i').rpos = t := by
    rw [wposOf_even hee, wposOf_odd hoo] at hpe hpt
    exact ⟨hpe.symm, hpt.symm⟩
  have hAe : SideAttach M.W (chordSet M Q L i) p t := hattI.1
  have hAw : SideAttach M.W (chordSet M Q L i') p t := by
    have : SideAttach M.W (chordSet M Q L i') (crec L i').rp (M.param Q (crec L i').rpos) :=
      hattI'.2
    rwa [hpos'.1, hpos'.2] at this
  -- directions
  have hptE : sidePt M.W p t = M.pos Q (crec L i).lpos := rfl
  have hE : ∀ z ∈ chordSet M Q L i, (sidePt M.W p t).1 ≤ z.1 := by
    rintro z ⟨-, hz, -⟩; rwa [hptE]
  have hptW : sidePt M.W p t = M.pos Q (crec L i').rpos := by
    show sidePt M.W p t = sidePt M.W (crec L i').rp (M.param Q (crec L i').rpos)
    rw [hpos'.1, hpos'.2]
  have hW : ∀ z ∈ chordSet M Q L i', z.1 ≤ (sidePt M.W p t).1 := by
    rintro z ⟨-, -, hz⟩; rwa [hptW]
  -- the other ends
  have hBe := hattI.2
  have hBe' : sidePt M.W (crec L i).rp (M.param Q (crec L i).rpos) ≠ sidePt M.W p t := by
    intro h'
    have : M.pos Q (crec L i).rpos = M.pos Q (crec L i).lpos := h'
    have hlt := pos_lt' hM hL hi
    rw [this] at hlt; exact lt_irrefl _ hlt
  have hBw := hattI'.1
  have hBw' : sidePt M.W (crec L i').lp (M.param Q (crec L i').lpos) ≠ sidePt M.W p t := by
    intro h'
    have : M.pos Q (crec L i').lpos = M.pos Q (crec L i').rpos := by rwa [← hptW]
    have hlt := pos_lt' hM hL hi'
    rw [this] at hlt; exact lt_irrefl _ hlt
  have hedge : (wposOf L e).edge = p := by rw [wposOf_even hee]; rfl
  obtain ⟨-, hhor, -⟩ := hM.tie_shape hadm (chordSet_mem hi) (chordSet_mem hi') hAe hAw hE hW
  have hev : evOf M Q L e = (i, kl M Q L i, kr M Q L i) := by rw [evOf_even hee]; rfl
  have hov : evOf M Q L o = (i', kr M Q L i', kl M Q L i') := by rw [evOf_odd hoo]; rfl
  have hkl : kl M Q L i = (p : ℝ) + t := rfl
  have hkr' : kr M Q L i' = (p : ℝ) + t := by
    show ((crec L i').rp : ℝ) + M.param Q (crec L i').rpos = p + t
    rw [hpos'.1, hpos'.2]
  rw [hedge, hev, hov]
  refine ⟨hhor, fun hdown => ?_, fun hup => ?_⟩
  · obtain ⟨ht0, hlt⟩ := BuildOrder.tie_rule_down hM hadm hfin (chordSet_mem hi) (chordSet_mem hi')
      hAe hAw hE hW hdown hBe hBe' hBw hBw'
    simp only
    rwa [hkl, hkr', ht0, add_zero]
  · obtain ⟨ht0, hlt⟩ := BuildOrder.tie_rule_up hM hadm hfin (chordSet_mem hi) (chordSet_mem hi')
      hAe hAw hE hW hup hBe hBe' hBw hBw'
    simp only
    rwa [hkl, hkr', ht0, add_zero]

/-- **The comparator implies the event order** (for distinct codes of a valid chord list). -/
theorem evLe_of_codeLe (hM : WalkAx M) (hL : ChordTriplesOK M Q L) {c c' : ℕ}
    (hc : c < 2 * L.length) (hc' : c' < 2 * L.length) (hne : c ≠ c')
    (hle : codeLe M Q L c c') : EvLe M.W.n (evOf M Q L c) (evOf M Q L c') := by
  unfold codeLe at hle
  rw [key_wposOf, key_wposOf] at hle
  rcases hle with hlt | ⟨heq, htb⟩
  · exact Or.inl hlt
  · refine Or.inr ⟨heq, ?_⟩
    have hA := attach_wposOf hL hc
    have hA' := attach_wposOf hL hc'
    have heq' : ((wposOf L c).edge : ℝ) + M.param Q (wposOf L c) =
        (wposOf L c').edge + M.param Q (wposOf L c') := by
      rwa [← Model.key, ← Model.key, key_wposOf, key_wposOf]
    obtain ⟨hpe, hpt⟩ := sideKey_inj hA.2.1 hA.2.2.1 hA'.2.1 hA'.2.2.1 heq'
    have hi : c / 2 < L.length := by omega
    have hi' : c' / 2 < L.length := by omega
    have hposeq : M.pos Q (wposOf L c) = M.pos Q (wposOf L c') := by
      unfold Model.pos Model.wa Model.wb; rw [hpe, hpt]
    -- the two chords differ
    have hij : c / 2 ≠ c' / 2 := by
      intro hij
      rcases Nat.mod_two_eq_zero_or_one c with h0 | h0
      · have h1 : c' % 2 = 1 := by omega
        rw [wposOf_even h0, wposOf_odd h1, ← hij] at hposeq
        have := pos_lt' hM hL hi
        rw [hposeq] at this; exact lt_irrefl _ this
      · have h1 : c' % 2 = 0 := by omega
        rw [wposOf_odd h0, wposOf_even h1, ← hij] at hposeq
        have := pos_lt' hM hL hi
        rw [hposeq] at this; exact lt_irrefl _ this
    have hadm : famOf M Q L ⊆ M.Adm := hL.1.2.1
    -- the common position
    have hA'' : SideAttach M.W (chordSet M Q L (c' / 2)) (wposOf L c).edge
        (M.param Q (wposOf L c)) := by rwa [hpe, hpt]
    have hsp : sidePt M.W (wposOf L c).edge (M.param Q (wposOf L c)) = M.pos Q (wposOf L c) := rfl
    have hEast : ∀ d, d % 2 = 0 → ∀ z ∈ chordSet M Q L (d / 2), (M.pos Q (wposOf L d)).1 ≤ z.1 := by
      intro d hd z hz; rw [wposOf_even hd]; exact hz.2.1
    have hWest : ∀ d, d % 2 = 1 → ∀ z ∈ chordSet M Q L (d / 2), z.1 ≤ (M.pos Q (wposOf L d)).1 := by
      intro d hd z hz; rw [wposOf_odd hd]; exact hz.2.2
    have htbc : tieBit M L c = if (M.wb (wposOf L c).edge).2 < (M.wa (wposOf L c).edge).2
        then 1 - c % 2 else c % 2 := rfl
    have htbc' : tieBit M L c' = if (M.wb (wposOf L c).edge).2 < (M.wa (wposOf L c).edge).2
        then 1 - c' % 2 else c' % 2 := by unfold tieBit; rw [hpe]
    rw [htbc, htbc'] at htb
    rcases Nat.mod_two_eq_zero_or_one c with h0 | h0 <;>
      rcases Nat.mod_two_eq_zero_or_one c' with h1 | h1
    · exfalso
      apply hij
      refine chordSet_inj hL hi hi' (hM.attach_east_unique hadm (chordSet_mem hi) (chordSet_mem hi')
        hA hA'' ?_ ?_)
      · rw [hsp]; exact hEast c h0
      · rw [hsp, hposeq]; exact hEast c' h1
    · obtain ⟨hhor, hdown, hup⟩ := tie_codes hM hL hc hc' h0 h1 hij hpe hpt
      rcases lt_or_gt_of_ne hhor with hd | hd
      · exfalso
        rw [ite_eq_left hd, ite_eq_left hd, h0, h1] at htb
        omega
      · exact (hup hd).le
    · obtain ⟨hhor, hdown, hup⟩ := tie_codes hM hL hc' hc h1 h0 (Ne.symm hij) hpe.symm hpt.symm
      rw [← hpe] at hhor hdown hup
      rcases lt_or_gt_of_ne hhor with hd | hd
      · exact (hdown hd).le
      · exfalso
        rw [ite_eq_right (not_lt.2 hd.le), ite_eq_right (not_lt.2 hd.le), h0, h1] at htb
        omega
    · exfalso
      apply hij
      refine chordSet_inj hL hi hi' (hM.attach_west_unique hadm (chordSet_mem hi) (chordSet_mem hi')
        hA hA'' ?_ ?_)
      · rw [hsp]; exact hWest c h0
      · rw [hsp, hposeq]; exact hWest c' h1

/-- **Codes sorted by the comparator give events sorted by the tie rule.** -/
theorem sorted_of_codeLe (hM : WalkAx M) (hL : ChordTriplesOK M Q L) {E : List ℕ}
    (hperm : E.Perm (List.range (2 * L.length))) (hsort : E.Pairwise (codeLe M Q L)) :
    (E.map (evOf M Q L)).Pairwise (EvLe M.W.n) := by
  have hnd : E.Nodup := hperm.nodup_iff.2 nodup_range
  rw [pairwise_map]
  refine (hsort.and hnd).imp_of_mem fun {a b} ha hb hab => ?_
  exact evLe_of_codeLe hM hL (List.mem_range.1 (hperm.mem_iff.1 ha))
    (List.mem_range.1 (hperm.mem_iff.1 hb)) hab.2 hab.1

/-- **WP-C: the normal form computed from comparator-sorted event codes is valid.** -/
theorem isNF_of_codeLe (hM : WalkAx M) (hL : ChordTriplesOK M Q L) {E : List ℕ}
    (hperm : E.Perm (List.range (2 * L.length))) (hsort : E.Pairwise (codeLe M Q L)) :
    IsNF M Q (buildNF M Q L E) ∧
      (buildNF M Q L E).chords.map (fun r => (r.h, r.lp, r.rp)) = L ∧ (buildNF M Q L E).dec = [] :=
  Input.isNF ⟨hM, hL, hperm, sorted_of_codeLe hM hL hperm hsort⟩

/-- **The good-model form**: for a good model and a valid chord list of `Q`, sorting the event
codes by `codeLe` and building `buildNF` gives a valid normal form with the chords of the list. -/
theorem isNF_goodModel (hM : GoodModel M) (hL : ChordTriplesOK M Q L) {E : List ℕ}
    (hperm : E.Perm (List.range (2 * L.length))) (hsort : E.Pairwise (codeLe M Q L)) :
    IsNF M Q (buildNF M Q L E) ∧
      (buildNF M Q L E).chords.map (fun r => (r.h, r.lp, r.rp)) = L ∧ (buildNF M Q L E).dec = [] :=
  isNF_of_codeLe (walkAx_of_goodModel hM) hL hperm hsort

end

end BuildNF

end Chazelle.Core
