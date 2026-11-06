module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseBoxAttach
public import Chazelle.Core.DownPhaseBoxBuild

/-!
# WP-M (B3′, part 7): box transport of chord lists

For twin chains `C`, `C'` (same vertex sequence, different hosts) and a chord list `L` whose
heights lie in the fixed band of the box stretch (`|y| < bnd C C'`):

* the chord list is valid for `C'` as soon as it is valid for `C` (`chordTriplesOK`);
* the two chain models agree on it (`keyCongr`), so `BuildNF` computes the same record in both;
* bounded degree and semigranularity of the chord family transfer (`transport`).

This is the per-chord part of the box transport of design finding M6 (option 1: drop the
wall-to-wall chords, whose heights may be outside the band, then transport).
-/

namespace Chazelle.Core

namespace BoxT

@[expose] public section

open Set List Chazelle.Chain Chazelle.Visibility BuildNF
open BuildRegions (crec famOf)

variable {C C' : Chain} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)}

/-- The heights of a chord list lie in the fixed band of the box stretch. -/
def InBand (C C' : Chain) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) : Prop :=
  ∀ x ∈ L, |(Q.vtx x.1).2| < bnd C C'

/-- The walk position of an event code is an end of a chord of the list. -/
theorem wposOf_mem {c : ℕ} (hc : c < 2 * L.length) :
    ∃ x ∈ L, wposOf L c = (recOf x).lpos ∨ wposOf L c = (recOf x).rpos := by
  have hi : c / 2 < L.length := by omega
  refine ⟨L[c / 2], getElem_mem _, ?_⟩
  simp_all [crec, wposOf] <;> omega_nf

/-- The facts about the ends of an attached band chord. -/
theorem end_facts (hband : InBand C C' Q L) (hL : ChordTriplesOK (chainModel C) Q L)
    {x : ℕ × ℕ × ℕ} (hx : x ∈ L) {w : WPos} (hw : w = (recOf x).lpos ∨ w = (recOf x).rpos) :
    w.edge < (chainModel C).W.n ∧ BandPos C C' Q w ∧
      (0 ≤ (chainModel C).param Q w ∧ (chainModel C).param Q w < 1) := by
  obtain ⟨hl, hr⟩ := hL.2.2.1 x hx
  have hb : |(Q.vtx x.1).2| < bnd C C' := hband x hx
  rcases hw with rfl | rfl
  · exact ⟨hl.1, Or.inr ⟨x.1, rfl, hb⟩, hl.2.1, hl.2.2.1⟩
  · exact ⟨hr.1, Or.inr ⟨x.1, rfl, hb⟩, hr.2.1, hr.2.2.1⟩

theorem phi_injective : Function.Injective (phi C C') := fun _ _ e =>
  (stretchHomeo (bnd_nonneg (C := C) (C' := C')) (kk_pos (C := C) (C' := C'))).injective e

namespace Twin

variable (h : Twin C C')
include h

section
variable (hband : InBand C C' Q L) (hL : ChordTriplesOK (chainModel C) Q L)
include hband hL
/-- The chords of the list in the model of `C'` are the stretched chords. -/
theorem toSet_rec
    {x : ℕ × ℕ × ℕ} (hx : x ∈ L) :
    (recOf x).toSet (chainModel C') Q = phi C C' '' (recOf x).toSet (chainModel C) Q := by
  obtain ⟨hl, -, hml⟩ := end_facts hband hL hx (Or.inl rfl)
  obtain ⟨hr, -, hmr⟩ := end_facts hband hL hx (Or.inr rfl)
  exact h.toSet_eq (hband x hx) hl hr hml hmr

/-- **The chord list is valid for the twin chain.** -/
theorem chordTriplesOK :
    ChordTriplesOK (chainModel C') Q L := by
  have hL0 := hL
  obtain ⟨⟨-, hadm, -⟩, hnd, hatt, hh⟩ := hL
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, hh⟩
  · refine ((List.finite_toSet L).image fun x => (recOf x).toSet (chainModel C') Q).subset ?_
    rintro c ⟨x, hx, rfl⟩
    grind
  · rintro c ⟨x, hx, rfl⟩
    obtain ⟨hl, hbl, hml⟩ := end_facts hband hL0 hx (Or.inl rfl)
    obtain ⟨hr, hbr, hmr⟩ := end_facts hband hL0 hx (Or.inr rfl)
    have hc := hadm ⟨x, hx, rfl⟩
    have e : (recOf x).toSet (chainModel C') Q = hseg (Q.vtx x.1).2
        (stretch (bnd C C') (kk C C') ((chainModel C).pos Q (recOf x).lpos).1)
        (stretch (bnd C C') (kk C C') ((chainModel C).pos Q (recOf x).rpos).1) := by
      unfold CRec.toSet
      rw [h.pos_eq hl hbl hml, h.pos_eq hr hbr hmr]
      rfl
    rw [e]
    exact h.augChords_transfer (hband x hx) hc
  · rintro c ⟨x, hx, rfl⟩
    exact ⟨x.1, hh x hx, _, _, rfl⟩
  · have e : L.map (fun x => (recOf x).toSet (chainModel C') Q) =
        (L.map fun x => (recOf x).toSet (chainModel C) Q).map (image (phi C C')) := by
      rw [map_map]
      exact map_congr_left fun x hx => h.toSet_rec hband hL0 hx
    rw [e]
    exact hnd.map (Set.image_injective.2 phi_injective)
  · intro x hx
    have hL := hL0
    obtain ⟨hl, hbl, hml⟩ := end_facts hband hL hx (Or.inl rfl)
    obtain ⟨hr, hbr, hmr⟩ := end_facts hband hL hx (Or.inr rfl)
    have hdy : ∀ z ∈ (recOf x).toSet (chainModel C) Q, z.2 = (Q.vtx (recOf x).h).2 :=
      fun z hz => hz.1
    rw [CRec.Attached, h.toSet_rec hband hL hx]
    exact ⟨h.attach_transfer hdy (h.pos_eq hl hbl hml) ((h.param_mem_iff hbl).2 hml)
        (h.param_eq_zero_iff hbl).symm (hatt x hx).1,
      h.attach_transfer hdy (h.pos_eq hr hbr hmr) ((h.param_mem_iff hbr).2 hmr)
        (h.param_eq_zero_iff hbr).symm (hatt x hx).2⟩

/-- **The two chain models agree on the chord list.** -/
theorem keyCongr :
    KeyCongr (chainModel C) (chainModel C') Q L where
  lt c c' hc hc' := by
    obtain ⟨x, hx, hw⟩ := wposOf_mem hc
    obtain ⟨x', hx', hw'⟩ := wposOf_mem hc'
    obtain ⟨-, hb, hm⟩ := end_facts hband hL hx hw
    obtain ⟨-, hb', hm'⟩ := end_facts hband hL hx' hw'
    exact h.key_lt_iff hb hb' hm hm'
  wt c c' hc hc' := by
    obtain ⟨x, hx, hw⟩ := wposOf_mem hc
    obtain ⟨x', hx', hw'⟩ := wposOf_mem hc'
    obtain ⟨-, hb, hm⟩ := end_facts hband hL hx hw
    obtain ⟨-, hb', hm'⟩ := end_facts hband hL hx' hw'
    exact h.arcWt_eq hb hb' hm hm'
  wt0 _ := by
    have hb : BandPos C C' Q ⟨0, 0⟩ := Or.inl rfl
    have hm : 0 ≤ (chainModel C).param Q ⟨0, 0⟩ ∧ (chainModel C).param Q ⟨0, 0⟩ < 1 := by
      simp [Model.param]
    exact h.arcWt_eq hb hb hm hm
  dir c _ := by
    rw [h.wa_eq, h.wb_eq]
    exact sig_lt_iff


end

end Twin

/-- The chord family of a normal form with chord list `L`. -/
theorem F_eq_famOf {M : Model} {N : NF}
    (hmap : N.chords.map (fun r => (r.h, r.lp, r.rp)) = L) : N.F M Q = famOf M Q L := by
  ext c
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨(r.h, r.lp, r.rp), hmap ▸ mem_map_of_mem hr, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    rw [← hmap] at hx
    obtain ⟨r, hr, rfl⟩ := mem_map.1 hx
    exact ⟨r, hr, rfl⟩

/-- A comparator-sorted event order exists. -/
theorem exists_sorted (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) :
    ∃ E : List ℕ, E.Perm (List.range (2 * L.length)) ∧ E.Pairwise (codeLe M Q L) := by
  classical
  have : Std.Total (codeLe M Q L) := ⟨codeLe_total M Q L⟩
  have : IsTrans ℕ (codeLe M Q L) := ⟨fun _ _ _ => codeLe_trans M Q L⟩
  exact ⟨_, perm_insertionSort _ _, pairwise_insertionSort _ _⟩

/-- **Box transport of a band chord list** (B3′, per-chord form).  For twin chains of simple
hosts and a valid chord list of `C` in the band, the list is valid for `C'`, and bounded degree
and `γ`-semigranularity of its chord family transfer from `C` to `C'`. -/
theorem transport (h : Twin C C') (hP : C.P.Simple) (hP' : C'.P.Simple)
    (hband : InBand C C' Q L) (hL : ChordTriplesOK (chainModel C) Q L) {d γ : ℕ}
    (hd : (chainModel C).DegLe (famOf (chainModel C) Q L) d)
    (hγ : (chainModel C).Semigranular (famOf (chainModel C) Q L) γ) :
    ChordTriplesOK (chainModel C') Q L ∧
      (chainModel C').DegLe (famOf (chainModel C') Q L) d ∧
      (chainModel C').Semigranular (famOf (chainModel C') Q L) γ := by
  have hL' := h.chordTriplesOK hband hL
  have hK := h.keyCongr hband hL
  obtain ⟨E, hperm, hsort⟩ := exists_sorted (chainModel C) Q L
  have hE : ∀ c ∈ E, c < 2 * L.length := fun c hc => mem_range.1 (hperm.subset hc)
  obtain ⟨hN, hmap, -⟩ := isNF_goodModel (Or.inl ⟨C, hP, rfl⟩) hL hperm hsort
  obtain ⟨hN', -, -⟩ := isNF_goodModel (Or.inl ⟨C', hP', rfl⟩) hL' hperm (hK.sorted hperm hsort)
  rw [hK.buildNF_eq hE] at hN'
  have e1 := F_eq_famOf (M := chainModel C) (Q := Q) hmap
  have e2 := F_eq_famOf (M := chainModel C') (Q := Q) hmap
  rw [← e1] at hd hγ
  rw [← e2]
  exact ⟨hL', IsNFRec.transfer hN hN' hd hγ⟩

end

end BoxT

end Chazelle.Core
