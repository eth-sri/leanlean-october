module

public import Chazelle.Core.RestoreTValid

/-!
# WP-E, the candidate test on the RAM, part 12: the count test as a scan

The count test (`CountOK`) asks for two exit chords of the region attached strictly on each side
of the new chord.  An attached admissible chord record is attached exactly at its two ends
(`attach_key_cases`), so an exit chord is attached strictly inside the key interval `(k₁, k₂)` iff
one of the keys of its ends is (`SideHit`).  The exit chords of region `r` are the records listed
in its chord list (`RegionsOK`), distinct records being distinct chords; so the side counts are
the numbers of places `t` of the list whose record satisfies `SideHit` (`sideExits_ncard`).
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sideInArc sidePt TouchesIn)

open Classical in
/-- The number of places `t' < t` satisfying `p`. -/
noncomputable def cntP (p : ℕ → Prop) (t : ℕ) : ℕ := ((Finset.range t).filter p).card

open Classical in
theorem cntP_succ (p : ℕ → Prop) (t : ℕ) :
    cntP p (t + 1) = cntP p t + (if p t then 1 else 0) := by
  unfold cntP
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

open Classical in
theorem cntP_zero (p : ℕ → Prop) : cntP p 0 = 0 := by simp [cntP]

open Classical in
theorem cntP_le (p : ℕ → Prop) (t : ℕ) : cntP p t ≤ t := by
  unfold cntP
  exact (Finset.card_filter_le _ _).trans (by simp)

variable {M : Model} {P : Polygon} {N : NF}

/-- The exit chord record `i` has an end with key strictly inside `(k₁, k₂)`. -/
def SideHit (M : Model) (P : Polygon) (N : NF) (k₁ k₂ : ℝ) (i : ℕ) : Prop :=
  sideInArc k₁ k₂ (M.key (Qof P) (N.chord i).lpos) ∨
    sideInArc k₁ k₂ (M.key (Qof P) (N.chord i).rpos)

/-- **The attachments of a record** are its ends (by key). -/
theorem record_attach (hGM : GoodModel M) (hNF : IsNF M (Qof P) N) {i : ℕ} (hi : i < N.nChords)
    {p : ℕ} {t : ℝ} (h : SideAttach M.W ((N.chord i).toSet M (Qof P)) p t) :
    (p : ℝ) + t = M.key (Qof P) (N.chord i).lpos ∨ (p : ℝ) + t = M.key (Qof P) (N.chord i).rpos := by
  have hM := walkAx_of_goodModel hGM
  have hadm : (N.chord i).toSet M (Qof P) ∈ M.Adm := hNF.1.2.1 (chord_toSet_mem' hi)
  have hat := hNF.2.2.1 i hi
  have hne : sidePt M.W (N.chord i).lp (M.param (Qof P) (N.chord i).lpos) ≠
      sidePt M.W (N.chord i).rp (M.param (Qof P) (N.chord i).rpos) := by
    intro h'
    have := endpoints_lt hM hadm hat
    have e : M.pos (Qof P) (N.chord i).lpos = M.pos (Qof P) (N.chord i).rpos := h'
    rw [e] at this; exact lt_irrefl _ this
  exact attach_key_cases hM hadm hat.1 hat.2 hne h

/-- **An exit chord record is attached inside `(k₁, k₂)` iff one of its ends is.** -/
theorem attach_side_iff (hGM : GoodModel M) (hNF : IsNF M (Qof P) N) {i : ℕ} (hi : i < N.nChords)
    (k₁ k₂ : ℝ) :
    (∃ (p : ℕ) (t : ℝ), SideAttach M.W ((N.chord i).toSet M (Qof P)) p t ∧ sideInArc k₁ k₂ (p + t)) ↔
      SideHit M P N k₁ k₂ i := by
  have hat := hNF.2.2.1 i hi
  constructor
  · rintro ⟨p, t, hA, hin⟩
    rcases record_attach hGM hNF hi hA with h | h
    · exact Or.inl (h ▸ hin)
    · exact Or.inr (h ▸ hin)
  · rintro (h | h)
    · exact ⟨_, _, hat.1, h⟩
    · exact ⟨_, _, hat.2, h⟩

/-- **The side counts are the numbers of places of the region's chord list** satisfying
`SideHit`. -/
theorem sideExits_ncard (hGM : GoodModel M) (hNF : IsNF M (Qof P) N) {reg : ℕ → Set Point}
    (hregs : NFRegs M (Qof P) N reg) {r : ℕ} (hr : r < N.nRegions) (k₁ k₂ : ℝ) :
    (sideExits M (N.F M (Qof P)) (reg r) k₁ k₂).ncard =
      cntP (fun t => SideHit M P N k₁ k₂ (chordAt N r t)) (N.region r).chords.length := by
  obtain ⟨-, -, -, hRok⟩ := hregs
  obtain ⟨hlist, hnd, -, -⟩ := hRok r hr
  set L := (N.region r).chords with hL
  -- the chords of the side are the images of the places
  have himg : sideExits M (N.F M (Qof P)) (reg r) k₁ k₂ =
      (fun t => (N.chord (chordAt N r t)).toSet M (Qof P)) ''
        {t | t < L.length ∧ SideHit M P N k₁ k₂ (chordAt N r t)} := by
    ext c
    constructor
    · rintro ⟨⟨hcF, htouch⟩, p, t, hA, hin⟩
      obtain ⟨i, hi, rfl⟩ := mem_F_iff hcF
      have hmem  := (hlist i).2 ⟨hi, htouch⟩
      obtain ⟨t', ht', hti⟩ := List.getElem_of_mem hmem
      have hat : chordAt N r t' = i := by
        unfold chordAt
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht', Option.getD_some]
        exact hti
      refine ⟨t', ⟨ht', ?_⟩, by simp [hat]⟩
      rw [hat]
      exact (attach_side_iff hGM hNF hi k₁ k₂).1 ⟨p, t, hA, hin⟩
    · rintro ⟨t', ⟨ht', hs⟩, rfl⟩
      have hmem : chordAt N r t' ∈ L := by
        unfold chordAt
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht', Option.getD_some]
        exact List.getElem_mem ht'
      obtain ⟨hi, htouch⟩ := (hlist _).1 hmem
      exact ⟨⟨chord_toSet_mem' hi, htouch⟩, (attach_side_iff hGM hNF hi k₁ k₂).2 hs⟩
  -- the map from places to chords is injective
  have hinj : Set.InjOn (fun t => (N.chord (chordAt N r t)).toSet M (Qof P))
      {t | t < L.length ∧ SideHit M P N k₁ k₂ (chordAt N r t)} := by
    rintro t₁ ⟨h₁, -⟩ t₂ ⟨h₂, -⟩ heq
    have g : ∀ t (ht : t < L.length), chordAt N r t = L[t] := fun t ht => by
      unfold chordAt
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
    have m₁ : chordAt N r t₁ ∈ L := by rw [g t₁ h₁]; exact List.getElem_mem h₁
    have m₂ : chordAt N r t₂ ∈ L := by rw [g t₂ h₂]; exact List.getElem_mem h₂
    have hi₁ : chordAt N r t₁ < N.nChords := ((hlist _).1 m₁).1
    have hi₂ : chordAt N r t₂ < N.nChords := ((hlist _).1 m₂).1
    have hij := hNF.2.1 _ _ hi₁ hi₂ heq
    rw [g t₁ h₁, g t₂ h₂] at hij
    exact (List.Nodup.getElem_inj_iff hnd).1 hij
  rw [himg, hinj.ncard_image]
  classical
  unfold cntP
  rw [← Set.ncard_coe_finset]
  congr 1
  ext t
  simp

end

end Restore

end Chazelle.Core
