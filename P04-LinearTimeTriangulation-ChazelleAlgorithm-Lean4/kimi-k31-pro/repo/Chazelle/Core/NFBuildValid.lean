module

public import Chazelle.Core.NFBuildNF
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics
public import Chazelle.ChainTactics

/-!
# WP-C (BuildNF): the computed normal form is valid

**Main result** `BuildNF.Input.isNF`: for a valid chord list `L` (`ChordTriplesOK`) of a walk-axiom
model (every good model) and **any** ordering `E` of the event codes `0 … 2K - 1` whose events are
sorted by `BuildSort.EvLe` (key, then the tie rule), `buildNF M Q L E` is a valid normal form
(`IsNF`) whose chords are the triples of `L` in order, without decomposition.  This is the
mathematical content of `BuildNFSpec`; the remaining part of `BuildNFSpec` is the RAM program that
sorts the events (`SortR.sortStmt_exec` with a key/tie comparator), runs the stack pass and writes
the layout of `buildNF` (`NFWithin`) within the budget.
-/

namespace Chazelle.Core

namespace BuildNF

@[expose] public section

open Set List Filter Topology
open Chazelle.Chain (SideAttach sideInArc sidePt sideKey_inj TouchesIn)
open BuildSort (Ev EvLe kap cntBelow)
open BuildOrder (events evPair chordSet mem_events chordSet_inj chordSet_mem getD_mem)
open BuildRegions (eL eR crec famOf e1 e2 kl kr lo hi gapLabel reg LabelOK Ctx)

variable {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}

/-- **The hypotheses**: a walk-axiom model, a valid chord list, and a sorted ordering of the event
codes. -/
structure Input (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ) : Prop where
  walk : WalkAx M
  valid : ChordTriplesOK M Q L
  perm : E.Perm (List.range (2 * L.length))
  sorted : (E.map (evOf M Q L)).Pairwise (EvLe M.W.n)

theorem range_map_evOf (n : ℕ) :
    (List.range (2 * n)).map (evOf M Q L) = (List.range n).flatMap (evPair M Q L) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, List.range_succ, List.range_succ, map_append,
      map_append, ih, List.range_succ, flatMap_append]
    simp only [map_cons, map_nil, flatMap_cons, flatMap_nil, append_nil, append_assoc,
      singleton_append]
    have h1 : evOf M Q L (2 * n) = eL M Q L n := by
      unfold evOf; rw [ite_eq_left (by omega), show 2 * n / 2 = n by omega]
    have h2 : evOf M Q L (2 * n + 1) = eR M Q L n := by
      unfold evOf; rw [ite_eq_right (by omega), show (2 * n + 1) / 2 = n by omega]
    rw [h1, h2]
    rfl

theorem key_wposOf (c : ℕ) : M.key Q (wposOf L c) = (evOf M Q L c).2.1 := by
  unfold wposOf evOf
  split_ifs <;> rfl

/-- The supremum of the values of a list of naturals is its `foldr max 0`. -/
theorem sSup_list (l : List ℕ) : sSup {x | x ∈ l} = l.foldr max 0 := by
  have hle : ∀ y ∈ l, y ≤ l.foldr max 0 := by
    intro y hy
    induction l with
    | nil => exact absurd hy (List.not_mem_nil)
    | cons x l ih =>
      rw [foldr_cons]
      rcases mem_cons.1 hy with rfl | hy
      · exact le_max_left _ _
      · exact (ih hy).trans (le_max_right _ _)
  rcases l with _ | ⟨x, l⟩
  · simp
  · have hmem : ∀ (x : ℕ) (l : List ℕ), (x :: l).foldr max 0 ∈ x :: l := by
      intro x l
      induction l generalizing x with
      | nil => simp
      | cons y l ih =>
        rw [foldr_cons]
        rcases le_total x ((y :: l).foldr max 0) with h1 | h1
        · rw [max_eq_right h1]; exact mem_cons_of_mem _ (ih y)
        · rw [max_eq_left h1]; exact mem_cons_self
    exact IsGreatest.csSup_eq ⟨hmem x l, hle⟩

namespace Input

variable (h : Input M Q L E)
include h

/-- The sorted events form a `Ctx`. -/
theorem ctx : Ctx M Q L (evs M Q L E) where
  walk := h.walk
  valid := h.valid
  perm := by
    unfold evs events
    rw [← range_map_evOf]
    exact h.perm.map _
  sorted := h.sorted

theorem length_E : E.length = 2 * L.length := by
  rw [h.perm.length_eq, length_range]

omit h in
theorem length_evs (_h : Input M Q L E) : (evs M Q L E).length = E.length := length_map _

/-- The key of the walk position of the `m`-th event is the `m`-th key. -/
theorem key_s {m : ℕ} (hm : m < E.length) :
    M.key Q (wposOf L (E.getD m 0)) = kap (evs M Q L E) m := by
  rw [key_wposOf, BuildSort.kap_eq (by rwx [h.length_evs])]
  unfold evs
  rw [getElem_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some]

omit h in
/-- The chords of the computed normal form are the chords of the list. -/
theorem F_eq (_h : Input M Q L E) : (buildNF M Q L E).F M Q = famOf M Q L := by
  ext c
  simp only [NF.F, buildNF, List.mem_map, List.mem_range, mem_ofPred_eq, famOf]
  constructor
  · rintro ⟨r, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨_, getD_mem hi, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hx
    refine ⟨_, ⟨i, hi, rfl⟩, ?_⟩
    have : L.getD i (0, 0, 0) = L[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    unfold chordRec
    rw [this]
    rfl

omit h in
/-- The chord record `i` of the computed normal form. -/
theorem chord_eq {i : ℕ} (hi : i < L.length) : (buildNF M Q L E).chord i = chordRec M Q L E i := by
  unfold NF.chord buildNF
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using hi), Option.getD_some,
    getElem_map, getElem_range]

omit h in
theorem nChords : (buildNF M Q L E).nChords = L.length := by
  simp [NF.nChords, buildNF]

omit h in
theorem nRegions : (buildNF M Q L E).nRegions = L.length + 1 := by
  simp [NF.nRegions, buildNF]

omit h in
/-- The chord of a record of the computed normal form. -/
theorem toSet_chord (i : ℕ) : (chordRec M Q L E i).toSet M Q = chordSet M Q L i := rfl

/-- The split of the sorted events at the first event of chord `i`. -/
theorem split_first {i : ℕ} (hi : i < L.length) :
    ∃ u v, evs M Q L E = u ++ e1 M Q L i :: v ∧ u.length = (evs M Q L E).idxOf (e1 M Q L i) := by
  obtain ⟨u, v, hsplit⟩ := List.append_of_mem (h.ctx.e1_mem hi)
  refine ⟨u, v, hsplit, ?_⟩
  have hnd := h.ctx.nodup
  rw [hsplit, nodup_append] at hnd
  have hnot : e1 M Q L i ∉ u := fun h1 => hnd.2.2 _ h1 _ mem_cons_self rfl
  rw [hsplit, List.idxOf_append_of_notMem hnot, idxOf_cons_self, add_zero]

/-- The region of index `r`. -/
noncomputable def regF (r : ℕ) : Set Point := reg M Q L (evs M Q L E) (lab r)

omit h in
theorem labelOK_lab {r : ℕ} (hr : r < L.length + 1) : LabelOK L.length (lab r) := by
  intro i hi
  unfold lab at hi
  by_cases h0 : r = 0
  · rw [ite_eq_left h0] at hi; cases hi
  · rw [ite_eq_right h0] at hi
    have : r - 1 = i := Option.some.inj hi
    omega

omit h in
theorem ridx_lt {ℓ : Option ℕ} (hℓ : LabelOK L.length ℓ) : ridx ℓ < L.length + 1 := by
  cases ℓ with
  | none => simp [ridx]
  | some i => have := hℓ i rfl; sio only [ridx]

/-- **The region correspondence** of the computed normal form. -/
theorem regionCorr : RegionCorr M Q (buildNF M Q L E) (regF (M := M) (Q := Q) (L := L) (E := E)) := by
  obtain ⟨h1, h2, h3⟩ := h.ctx.regions_corr
  rw [RegionCorr, h.F_eq, nRegions]
  refine ⟨fun r hr => h1 _ (labelOK_lab hr), fun r r' hr hr' heq => ?_, fun U hU => ?_⟩
  · have := h2 _ _ (labelOK_lab hr) (labelOK_lab hr') heq
    rw [← ridx_lab r, ← ridx_lab r', this]
  · obtain ⟨ℓ, hℓ, hU⟩ := h3 U hU
    exact ⟨ridx ℓ, ridx_lt hℓ, by unfold regF; rwx [lab_ridx]⟩

/-- **The sides of the chord records.** -/
theorem sides_rec {i : ℕ} (hi : i < L.length) :
    (chordRec M Q L E i).up < L.length + 1 ∧ (chordRec M Q L E i).dn < L.length + 1 ∧
      M.AboveOf (chordSet M Q L i) (regF (M := M) (Q := Q) (L := L) (E := E) (chordRec M Q L E i).up) ∧
      M.BelowOf (chordSet M Q L i) (regF (M := M) (Q := Q) (L := L) (E := E) (chordRec M Q L E i).dn) := by
  obtain ⟨u, v, hsplit, hlen⟩ := h.split_first hi
  have hC := h.ctx
  have hsides := hC.sides hsplit hi
  have hfirst := hC.label_first hsplit hi
  have hout : outside M Q L E i = BuildStack.label (word M Q L E) u.length := by
    unfold outside; rw [hlen]
  have hOK : LabelOK L.length (outside M Q L E i) := by rw [hout]; exact hC.label_ok _
  have hword : word M Q L E = (evs M Q L E).map Prod.fst := rfl
  rw [hword] at hout
  rw [hfirst] at hsides
  have hri : ridx (some i) = i + 1 := rfl
  unfold chordRec regF
  split_ifs with hk
  · refine ⟨ridx_lt hOK, ?_, ?_, ?_⟩
    · show i + 1 < L.length + 1
      omega
    · rw [lab_ridx, hout]; exact (hsides.2.2.1 hk).2
    · rw [← hri, lab_ridx]; exact (hsides.2.2.1 hk).1
  · have hk' : kr M Q L i < kl M Q L i :=
      lt_of_le_of_ne (not_lt.1 hk) (Ne.symm (hC.kl_ne_kr hi))
    refine ⟨?_, ridx_lt hOK, ?_, ?_⟩
    · show i + 1 < L.length + 1
      omega
    · rw [← hri, lab_ridx]; exact (hsides.2.2.2 hk').1
    · rw [lab_ridx, hout]; exact (hsides.2.2.2 hk').2

/-- **The chord sides** of the computed normal form. -/
theorem chordSidesOK :
    ChordSidesOK M Q (buildNF M Q L E) (regF (M := M) (Q := Q) (L := L) (E := E)) := by
  intro i hi
  rw [nChords] at hi
  rw [nRegions, chord_eq hi]
  obtain ⟨hup, hdn, hA, hB⟩ := h.sides_rec hi
  refine ⟨hup, hdn, fun z hz hzD => ?_⟩
  rw [toSet_chord] at hz
  obtain ⟨ε₀, hε₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 ((hA z hz hzD).and (hB z hz hzD))
  exact ⟨ε₀, hε₀, fun ε h1 h2 => hsub ⟨h1, h2⟩⟩

/-! ## Arcs -/

omit h in
theorem mem_gapStarts {m : ℕ} :
    m ∈ gapStarts M Q L E ↔ m < E.length ∧
      (m + 1 = E.length ∨ kap (evs M Q L E) m < kap (evs M Q L E) (m + 1)) := by
  unfold gapStarts
  rw [mem_filter, List.mem_range, decide_eq_true_eq]

omit h in
/-- The gap starts are increasing. -/
theorem gapStarts_sorted : (gapStarts M Q L E).Pairwise (· < ·) :=
  (List.pairwise_lt_range).filter _

omit h in
/-- The arc record at index `j` (with chords). -/
theorem arc_eq {j : ℕ} (hK : L.length ≠ 0) (hj : j < (arcList M Q L E).length) :
    (buildNF M Q L E).arc j = arcRec M Q L E ((gapStarts M Q L E)[j]'(by
      unfold arcList at hj; rw [ite_eq_right hK, length_map] at hj; exact hj)) := by
  unfold NF.arc buildNF
  simp only
  unfold arcList
  simp only [ite_eq_right hK]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem, Option.map_some,
    Option.getD_some]

/-- The start key of the arc of the gap at `m`. -/
theorem key_arcRec_s {m : ℕ} (hm : m < E.length) :
    M.key Q (arcRec M Q L E m).s = kap (evs M Q L E) m := h.key_s hm

/-- The end key of the arc of the gap at `m`. -/
theorem key_arcRec_e {m : ℕ} (hm : m < E.length) :
    M.key Q (arcRec M Q L E m).e = kap (evs M Q L E) ((m + 1) % E.length) :=
  h.key_s (Nat.mod_lt _ (by omega))

/-- **The arc of a gap is an arc of the region of its record.** -/
theorem arcRec_isArc {m : ℕ} (hK : L.length ≠ 0) (hm : m ∈ gapStarts M Q L E) :
    (arcRec M Q L E m).reg < L.length + 1 ∧
      M.IsArc (famOf M Q L) (regF (M := M) (Q := Q) (L := L) (E := E) (arcRec M Q L E m).reg)
        (M.key Q (arcRec M Q L E m).s) (M.key Q (arcRec M Q L E m).e) := by
  rw [mem_gapStarts] at hm
  obtain ⟨hml, hgap⟩ := hm
  have hC := h.ctx
  have hlev := h.length_evs
  refine ⟨ridx_lt (hC.label_ok _), ?_⟩
  unfold regF
  rw [h.key_arcRec_s hml, h.key_arcRec_e hml]
  simp only [arcRec]
  rw [lab_ridx]
  rcases hgap with hlast | hlt
  · have hS : (evs M Q L E).length = m + 1 := by rw [hlev, hlast]
    rw [hlast, Nat.mod_self, show word M Q L E = (evs M Q L E).map Prod.fst from rfl, ← hlev,
      hC.label_ends.2, show m = (evs M Q L E).length - 1 by omega]
    exact hC.arc_of_wrap (Nat.pos_of_ne_zero hK)
  · have hm1 : m + 1 < E.length := by
      rcases lt_or_ge (m + 1) E.length with h1 | h1
      · exact h1
      · exfalso
        have h1' : m + 1 = (evs M Q L E).length := by rwo [hlev]
        have h0 : kap (evs M Q L E) (m + 1) = 0 := by
          unfold kap; rw [List.getD_eq_default _ _ (by omega)]
        have := (hC.kap_bounds (m := m) (by rwx [hlev])).1
        linarith
    rw [Nat.mod_eq_of_lt hm1]
    exact hC.arc_of_gap (by rwx [hlev]) hlt

/-- Two arcs with the same keys of regions of the computed normal form have the same region. -/
theorem reg_eq_of_arcs (hK : L.length ≠ 0) {r r' : ℕ} (hr : r < L.length + 1)
    (hr' : r' < L.length + 1) {a b : ℝ}
    (h1 : M.IsArc (famOf M Q L) (regF (M := M) (Q := Q) (L := L) (E := E) r) a b)
    (h2 : M.IsArc (famOf M Q L) (regF (M := M) (Q := Q) (L := L) (E := E) r') a b) : r = r' := by
  have hcorr := h.regionCorr
  rw [RegionCorr, h.F_eq, nRegions] at hcorr
  have hne : (famOf M Q L).Nonempty := ⟨_, chordSet_mem (Nat.pos_of_ne_zero hK)⟩
  obtain ⟨p, hp, t, ht, hin, -, hf⟩ := WalkAx.exists_pos_in_arc hne h1
  have hf' := h2.2.2.2.2.2.2 p t hp ht.1 ht.2 hin
  exact hcorr.2.1 r r' hr hr' (WalkAx.faces_unique (hcorr.1 r hr) (hcorr.1 r' hr') hf hf')

/-- **The arc records** of the computed normal form. -/
theorem arcsOK : ArcsOK M Q (buildNF M Q L E) (regF (M := M) (Q := Q) (L := L) (E := E)) := by
  have hC := h.ctx
  have hlev := h.length_evs
  have harcsN : (buildNF M Q L E).arcs = arcList M Q L E := rfl
  have hregion : ∀ r, r < L.length + 1 → (buildNF M Q L E).region r =
      ⟨regArcs M Q L E r, regChords M Q L E r, regWt M Q L E r⟩ := by
    intro r hr
    unfold NF.region buildNF
    simp only
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hr, Option.map_some,
      Option.getD_some]
  have hlast : ∀ r, r < (buildNF M Q L E).nRegions → ∀ j,
      (j ∈ ((buildNF M Q L E).region r).arcs ↔
        j < (buildNF M Q L E).arcs.length ∧ ((buildNF M Q L E).arc j).reg = r) := by
    intro r hr j
    rw [nRegions] at hr
    rw [hregion r hr, harcsN]
    unfold regArcs
    rw [mem_filter, List.mem_range, decide_eq_true_eq]
    rfl
  unfold ArcsOK
  rw [h.F_eq, nRegions, harcsN]
  by_cases hK : L.length = 0
  · -- no chord: the single pinned arc
    have hA : arcList M Q L E = [⟨0, ⟨0, 0⟩, ⟨0, 0⟩⟩] := by unfold arcList; rw [ite_eq_left hK]
    have hkey0 : M.key Q ⟨0, 0⟩ = 0 := by simp [Model.key, Model.param]
    have harc0 : (buildNF M Q L E).arc 0 = ⟨0, ⟨0, 0⟩, ⟨0, 0⟩⟩ := by
      urr NF.arc [harcsN, hA]
    have hreg0 : regF (M := M) (Q := Q) (L := L) (E := E) 0 = reg M Q L (evs M Q L E) none := rfl
    refine ⟨fun j hj => ?_, fun j j' hj hj' _ _ => ?_, fun r hr a b harc => ?_, ?_⟩
    · rw [hA, length_singleton] at hj
      have : j = 0 := by omega
      subst this
      rw [harc0]
      refine ⟨by show 0 < L.length + 1; omega, ?_⟩
      show M.IsArc _ (regF 0) (M.key Q ⟨0, 0⟩) (M.key Q ⟨0, 0⟩)
      rw [hkey0, hreg0]
      exact hC.arc_of_empty hK
    · rwo [hA, length_singleton] at hj hj'
    · obtain ⟨rfl, rfl⟩ := hC.gap_of_arc_empty hK harc
      refine ⟨0, by rws [hA], ?_, ?_, ?_⟩
      · rw [harc0]; show 0 = r; omega
      · rwx [harc0]
      · rwx [harc0]
    · intro r hr j; rw [← harcsN]; exact hlast r (by rwx [nRegions]) j
  · have hA : arcList M Q L E = (gapStarts M Q L E).map (arcRec M Q L E) := by
      unfold arcList; rw [ite_eq_right hK]
    have hlenA : (arcList M Q L E).length = (gapStarts M Q L E).length := by rw [hA, length_map]
    refine ⟨fun j hj => ?_, fun j j' hj hj' hreg hkey => ?_, fun r hr a b harc => ?_, ?_⟩
    · rw [arc_eq hK hj]
      exact h.arcRec_isArc hK (getElem_mem _)
    · rw [arc_eq hK hj, arc_eq hK hj'] at hkey
      have hj1 : j < (gapStarts M Q L E).length := hlenA ▸ hj
      have hj1' : j' < (gapStarts M Q L E).length := hlenA ▸ hj'
      have hmem := fun k (hk : k < (gapStarts M Q L E).length) =>
        (mem_gapStarts (M := M) (Q := Q) (L := L) (E := E)).1 (getElem_mem hk)
      rw [h.key_arcRec_s (hmem j hj1).1, h.key_arcRec_s (hmem j' hj1').1] at hkey
      by_contra hne
      have hsorted := pairwise_iff_getElem.1 (gapStarts_sorted (M := M) (Q := Q) (L := L) (E := E))
      -- the earlier gap start is followed by a strictly larger key
      have key_lt : ∀ k k', (hk : k < (gapStarts M Q L E).length) →
          (hk' : k' < (gapStarts M Q L E).length) → k < k' →
          kap (evs M Q L E) (gapStarts M Q L E)[k] < kap (evs M Q L E) (gapStarts M Q L E)[k'] := by
        intro k k' hk hk' hkk
        have hlt := hsorted k k' hk hk' hkk
        obtain ⟨hml, hgap⟩ := hmem k hk
        have hml' := (hmem k' hk').1
        rcases hgap with hlast | hgap
        · omega
        · exact hgap.trans_le (BuildSort.kap_mono hC.sorted hlt (by rwx [hlev]))
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · exact (key_lt j j' hj1 hj1' hlt).ne hkey
      · exact (key_lt j' j hj1' hj1 hlt).ne hkey.symm
    · have hS : (evs M Q L E).length = E.length := hlev
      -- the gap of the arc
      obtain ⟨m, hmG, rfl, rfl⟩ : ∃ m ∈ gapStarts M Q L E,
          a = kap (evs M Q L E) m ∧ b = kap (evs M Q L E) ((m + 1) % E.length) := by
        rcases hC.gap_of_arc (Nat.pos_of_ne_zero hK) harc with ⟨m, hm1, hlt, rfl, rfl⟩ | ⟨rfl, rfl⟩
        · refine ⟨m, (mem_gapStarts (M := M) (Q := Q) (L := L) (E := E)).2
            ⟨by omega, Or.inr hlt⟩, rfl, ?_⟩
          rw [Nat.mod_eq_of_lt (by omega)]
        · have hE : 0 < E.length := by rwo [h.length_E]
          refine ⟨E.length - 1, (mem_gapStarts (M := M) (Q := Q) (L := L) (E := E)).2
            ⟨by omega, Or.inl (by omega)⟩, by rw [hS], ?_⟩
          rw [Nat.sub_add_cancel hE, Nat.mod_self]
      obtain ⟨j, hj, hjm⟩ := List.mem_iff_getElem.1 hmG
      have hjA : j < (arcList M Q L E).length := hlenA ▸ hj
      have hmE := ((mem_gapStarts (M := M) (Q := Q) (L := L) (E := E)).1 hmG).1
      obtain ⟨hreg, harc'⟩ := h.arcRec_isArc hK hmG
      rw [h.key_arcRec_s hmE, h.key_arcRec_e hmE] at harc'
      refine ⟨j, hjA, ?_, ?_, ?_⟩
      · rw [arc_eq hK hjA]
        simp only [hjm]
        exact (h.reg_eq_of_arcs hK hr hreg harc harc').symm
      · rw [arc_eq hK hjA]; simp only [hjm]; exact h.key_arcRec_s hmE
      · rw [arc_eq hK hjA]; simp only [hjm]; exact h.key_arcRec_e hmE
    · intro r hr j; rw [← harcsN]; exact hlast r (by rwx [nRegions]) j

/-! ## Regions and the sequence -/

omit h in
theorem region_eq (_h : Input M Q L E) {r : ℕ}
    (hr : r < L.length + 1) : (buildNF M Q L E).region r =
    ⟨regArcs M Q L E r, regChords M Q L E r, regWt M Q L E r⟩ := by
  unfold NF.region buildNF
  simp only
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hr, Option.map_some,
    Option.getD_some]

/-- The two side regions of a chord are the regions of its `up` and `dn` records. -/
theorem touches_iff {i : ℕ} (hi : i < L.length) {r : ℕ} (hr : r < L.length + 1) :
    TouchesIn M.D (chordSet M Q L i) (regF (M := M) (Q := Q) (L := L) (E := E) r) ↔
      (chordRec M Q L E i).up = r ∨ (chordRec M Q L E i).dn = r := by
  have hcorr := h.regionCorr
  rw [RegionCorr, h.F_eq, nRegions] at hcorr
  have hsys := h.walk.sys _ h.ctx.adm h.ctx.finite
  obtain ⟨Up, Dn, hUp, hDn, -, hside, htouch⟩ := chordSides_of_system hsys (chordSet_mem hi)
  obtain ⟨hup, hdn, hA, hB⟩ := h.sides_rec hi
  obtain ⟨z, hzc, hzD⟩ := (hsys.chord_inter_nonempty_isPreconnected (chordSet_mem hi)).1
  have heqU : regF (M := M) (Q := Q) (L := L) (E := E) (chordRec M Q L E i).up = Up := by
    obtain ⟨δ, h1, h2, -⟩ := ((hA z hzc hzD).and (hside z hzc hzD)).exists
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint (hcorr.1 _ hup) hUp with h' | h'
    · exact h'
    · exact absurd (h'.le_bot ⟨h1, h2⟩) (id)
  have heqD : regF (M := M) (Q := Q) (L := L) (E := E) (chordRec M Q L E i).dn = Dn := by
    obtain ⟨δ, h1, -, h2⟩ := ((hB z hzc hzD).and (hside z hzc hzD)).exists
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint (hcorr.1 _ hdn) hDn with h' | h'
    · exact h'
    · exact absurd (h'.le_bot ⟨h1, h2⟩) (id)
  rw [htouch _ (hcorr.1 r hr), ← heqU, ← heqD]
  constructor
  · rintro (h1 | h1)
    · exact Or.inl (hcorr.2.1 _ _ hup hr h1.symm)
    · exact Or.inr (hcorr.2.1 _ _ hdn hr h1.symm)
  · rintro (h1 | h1)
    · exact Or.inl (by rw [h1])
    · exact Or.inr (by rw [h1])

/-- **The region records** of the computed normal form. -/
theorem regionsOK : RegionsOK M Q (buildNF M Q L E) (regF (M := M) (Q := Q) (L := L) (E := E)) := by
  have harcs := h.arcsOK
  intro r hr
  rw [nRegions] at hr
  rw [h.region_eq hr, h.F_eq]
  refine ⟨fun i => ?_, (nodup_range).filter _, (nodup_range).filter _, ?_⟩
  · simp only
    unfold regChords
    rw [mem_filter, List.mem_range, decide_eq_true_eq, nChords]
    constructor
    · rintro ⟨hi, hc⟩
      refine ⟨hi, ?_⟩
      rw [chord_eq hi, toSet_chord]
      exact (h.touches_iff hi hr).2 hc
    · rintro ⟨hi, hc⟩
      rw [chord_eq hi, toSet_chord] at hc
      exact ⟨hi, (h.touches_iff hi hr).1 hc⟩
  · -- the weight
    simp only
    unfold Model.weight regWt
    rw [← sSup_list]
    congr 1
    obtain ⟨h1, -, h3, h4⟩ := harcs
    rw [h.F_eq, nRegions] at h1 h3
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
      have hj' := (h4 r (by rwx [nRegions]) j).1 (by rwx [h.region_eq hr])
      obtain ⟨-, harc⟩ := h1 j hj'.1
      rw [hj'.2] at harc
      exact ⟨(M.key Q ((buildNF M Q L E).arc j).s, M.key Q ((buildNF M Q L E).arc j).e), harc, rfl⟩
    · rintro ⟨ab, harc, rfl⟩
      obtain ⟨j, hj, hjr, hs, he⟩ := h3 r hr ab.1 ab.2 harc
      have hjr' := (h4 r (by rwx [nRegions]) j).2 ⟨hj, hjr⟩
      rw [h.region_eq hr] at hjr'
      refine List.mem_map.2 ⟨j, hjr', ?_⟩
      show M.arcWt (M.key Q ((buildNF M Q L E).arc j).s) (M.key Q ((buildNF M Q L E).arc j).e) = _
      rw [hs, he]

/-- **The arc sequence** of the computed normal form. -/
theorem seqOK : SeqOK M Q (buildNF M Q L E) := by
  refine ⟨Perm.refl _, ?_⟩
  show (List.range (arcList M Q L E).length).Pairwise
    (fun j j' => M.key Q ((buildNF M Q L E).arc j).s ≤ M.key Q ((buildNF M Q L E).arc j').s)
  rw [pairwise_iff_getElem]
  intro j j' hj hj' hjj
  simp only [getElem_range]
  rw [length_range] at hj hj'
  by_cases hK : L.length = 0
  · have : (arcList M Q L E).length = 1 := by urr arcList [ite_eq_left hK]
    omega
  · have hC := h.ctx
    have hlenA : (arcList M Q L E).length = (gapStarts M Q L E).length := by
      unfold arcList; rw [ite_eq_right hK, length_map]
    rw [arc_eq hK hj, arc_eq hK hj']
    have hj1 : j < (gapStarts M Q L E).length := hlenA ▸ hj
    have hj1' : j' < (gapStarts M Q L E).length := hlenA ▸ hj'
    have hmem := fun k (hk : k < (gapStarts M Q L E).length) =>
      (mem_gapStarts (M := M) (Q := Q) (L := L) (E := E)).1 (getElem_mem hk)
    rw [h.key_arcRec_s (hmem j hj1).1, h.key_arcRec_s (hmem j' hj1').1]
    have hlt := pairwise_iff_getElem.1 (gapStarts_sorted (M := M) (Q := Q) (L := L) (E := E))
      j j' hj1 hj1' hjj
    exact BuildSort.kap_mono hC.sorted hlt.le (by rw [h.length_evs]; exact (hmem j' hj1').1)

/-- The walk positions of the events are positions of the walk proper. -/
theorem properPos_wposOf {c : ℕ} (hc : c ∈ E) : ProperPos M Q Q.n (wposOf L c) := by
  have hc2  := List.mem_range.1 (h.perm.mem_iff.1 hc)
  have hi : c / 2 < L.length := by omega
  have hC := h.ctx
  have hh : (crec L (c / 2)).h < Q.n := h.valid.2.2.2 _ (getD_mem hi)
  unfold wposOf
  split_ifs
  · have hA := hC.attL hi
    exact ⟨hA.2.1, hA.2.2.1, by show (crec L (c / 2)).h + 1 ≤ Q.n; omega⟩
  · have hA := hC.attR hi
    exact ⟨hA.2.1, hA.2.2.1, by show (crec L (c / 2)).h + 1 ≤ Q.n; omega⟩

/-- The ends of the arc records are positions of the walk proper. -/
theorem properPos_arcs {j : ℕ} (hj : j < (arcList M Q L E).length) :
    ProperPos M Q Q.n ((buildNF M Q L E).arc j).s ∧ ProperPos M Q Q.n ((buildNF M Q L E).arc j).e := by
  by_cases hK : L.length = 0
  · have hA : arcList M Q L E = [⟨0, ⟨0, 0⟩, ⟨0, 0⟩⟩] := by unfold arcList; rw [ite_eq_left hK]
    rw [hA, length_singleton] at hj
    have : j = 0 := by omega
    subst this
    have harc0 : (buildNF M Q L E).arc 0 = ⟨0, ⟨0, 0⟩, ⟨0, 0⟩⟩ := by
      unfold NF.arc; show (arcList M Q L E).getD 0 _ = _; rwr [hA]
    rw [harc0]
    have hp : ProperPos M Q Q.n ⟨0, 0⟩ := ⟨le_refl _, by simp [Model.param], Nat.zero_le _⟩
    exact ⟨hp, hp⟩
  · rw [arc_eq hK hj]
    have hlenA : (arcList M Q L E).length = (gapStarts M Q L E).length := by
      unfold arcList; rw [ite_eq_right hK, length_map]
    have hj1 : j < (gapStarts M Q L E).length := hlenA ▸ hj
    have hm := ((mem_gapStarts (M := M) (Q := Q) (L := L) (E := E)).1 (getElem_mem hj1)).1
    have hgetD : ∀ k, k < E.length → E.getD k 0 ∈ E := fun k hk => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
      exact getElem_mem hk
    exact ⟨h.properPos_wposOf (hgetD _ hm), h.properPos_wposOf (hgetD _ (Nat.mod_lt _ (by omega)))⟩

/-- **WP-C: the computed normal form is valid** (`IsNF`), with the chords of the list in order
and no decomposition. -/
theorem isNF : IsNF M Q (buildNF M Q L E) ∧
    (buildNF M Q L E).chords.map (fun r => (r.h, r.lp, r.rp)) = L ∧ (buildNF M Q L E).dec = [] := by
  have hC := h.ctx
  refine ⟨⟨?_, fun i i' hi hi' heq => ?_, fun i hi => ?_, regF, h.regionCorr, h.chordSidesOK,
    h.arcsOK, h.regionsOK, h.seqOK, fun i hi => ?_, fun j hj => h.properPos_arcs hj⟩, ?_, rfl⟩
  · rw [h.F_eq]; exact h.valid.1
  · rw [nChords] at hi hi'
    rw [chord_eq hi, chord_eq hi', toSet_chord, toSet_chord] at heq
    exact chordSet_inj h.valid hi hi' heq
  · rw [nChords] at hi
    rw [chord_eq hi]
    exact h.valid.2.2.1 _ (getD_mem hi)
  · rw [nChords] at hi
    rw [chord_eq hi]
    exact h.valid.2.2.2 _ (getD_mem hi)
  · simp only [buildNF, List.map_map]
    apply List.ext_getElem (by simp)
    intro k hk1 hk2
    simp only [getElem_map, getElem_range, Function.comp_apply, chordRec]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk2, Option.getD_some]

end Input

end

end BuildNF

end Chazelle.Core
