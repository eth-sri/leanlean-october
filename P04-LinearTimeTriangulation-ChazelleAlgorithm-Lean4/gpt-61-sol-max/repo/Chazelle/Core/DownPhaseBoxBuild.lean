module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.NFBuildCmp

/-!
# WP-M (B3′, part 5): congruence of `buildNF`

`buildNF M Q L E` depends on the model `M` only through the order of the keys of the chord
endpoints of `L`, the weights of the arcs between them, and (for the comparator `codeLe`) the
direction of the walk edges carrying them.  If two models agree on these (`KeyCongr`), they
compute **the same normal-form record** (`buildNF_eq`) from the same event order, and the event
order sorted for one is sorted for the other (`codeLe_iff`).

This is model-independent; it is used for twin chains (box transport, design
`docs/design-downphase.md`, finding M6).
-/

namespace Chazelle.Core

namespace BoxT

@[expose] public section

open List BuildNF
open BuildSort (Ev kap)
open BuildRegions (eL eR crec kl kr lo hi e1)

variable {M M' : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)}

/-- **Two models agree on a chord list**: the keys of the chord endpoints compare alike, the arcs
between them weigh alike, and their walk edges go down alike. -/
structure KeyCongr (M M' : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) : Prop where
  lt : ∀ c c', c < 2 * L.length → c' < 2 * L.length →
    (M'.key Q (wposOf L c) < M'.key Q (wposOf L c') ↔
      M.key Q (wposOf L c) < M.key Q (wposOf L c'))
  wt : ∀ c c', c < 2 * L.length → c' < 2 * L.length →
    M'.arcWt (M'.key Q (wposOf L c)) (M'.key Q (wposOf L c')) =
      M.arcWt (M.key Q (wposOf L c)) (M.key Q (wposOf L c'))
  wt0 : L = [] → M'.arcWt (M'.key Q ⟨0, 0⟩) (M'.key Q ⟨0, 0⟩) =
    M.arcWt (M.key Q ⟨0, 0⟩) (M.key Q ⟨0, 0⟩)
  dir : ∀ c, c < 2 * L.length →
    ((M'.wb (wposOf L c).edge).2 < (M'.wa (wposOf L c).edge).2 ↔
      (M.wb (wposOf L c).edge).2 < (M.wa (wposOf L c).edge).2)

/-- The index of an image in a mapped list, for a map injective at the element. -/
theorem idxOf_map_of_inj {α β : Type*} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] (f : α → β)
    (l : List α) (a : α) (h : ∀ x ∈ l, f x = f a → x = a) :
    (l.map f).idxOf (f a) = l.idxOf a := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    grind

theorem wposOf_even (L : List (ℕ × ℕ × ℕ)) (i : ℕ) : wposOf L (2 * i) = (crec L i).lpos := by
  simp [wposOf]

theorem wposOf_odd (L : List (ℕ × ℕ × ℕ)) (i : ℕ) : wposOf L (2 * i + 1) = (crec L i).rpos := by
  grind [wposOf]

theorem kl_eq (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (i : ℕ) :
    kl M Q L i = M.key Q (wposOf L (2 * i)) := by
  rw [wposOf_even]; rfl

theorem kr_eq (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (i : ℕ) :
    kr M Q L i = M.key Q (wposOf L (2 * i + 1)) := by
  rw [wposOf_odd]; rfl

/-- The keys of the chord endpoints. -/
def InS (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (x : ℝ) : Prop :=
  ∃ c, c < 2 * L.length ∧ M.key Q (wposOf L c) = x

/-- The key map from `M` to `M'` on the keys of the chord endpoints. -/
noncomputable def gmap (M M' : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (x : ℝ) : ℝ := by
  classical
  exact if h : InS M Q L x then M'.key Q (wposOf L h.choose) else x

/-- The map of events. -/
noncomputable def mapEv (g : ℝ → ℝ) (e : Ev) : Ev := (e.1, g e.2.1, g e.2.2)

namespace KeyCongr

variable (hK : KeyCongr M M' Q L)
include hK

theorem eq_iff {c c' : ℕ} (hc : c < 2 * L.length) (hc' : c' < 2 * L.length) :
    M'.key Q (wposOf L c) = M'.key Q (wposOf L c') ↔
      M.key Q (wposOf L c) = M.key Q (wposOf L c') := by
  core_grind

theorem gmap_key {c : ℕ} (hc : c < 2 * L.length) :
    gmap M M' Q L (M.key Q (wposOf L c)) = M'.key Q (wposOf L c) := by
  have h : InS M Q L (M.key Q (wposOf L c)) := ⟨c, hc, rfl⟩
  unfold gmap
  rw [dite_eq_left h]
  exact (hK.eq_iff h.choose_spec.1 hc).2 h.choose_spec.2

section
variable {x y : ℝ} (hx : InS M Q L x) (hy : InS M Q L y)
include hx hy
theorem gmap_lt :
    gmap M M' Q L x < gmap M M' Q L y ↔ x < y := by
  obtain ⟨c, hc, rfl⟩ := hx
  obtain ⟨c', hc', rfl⟩ := hy
  rw [hK.gmap_key hc, hK.gmap_key hc']
  exact hK.lt c c' hc hc'

theorem gmap_inj
    (e : gmap M M' Q L x = gmap M M' Q L y) : x = y := by
  rcases lt_trichotomy x y with l | l | l
  · exact absurd e ((hK.gmap_lt hx hy).2 l).ne
  · exact l
  · exact absurd e ((hK.gmap_lt hy hx).2 l).ne'


end

omit hK in
theorem inS_kl {i : ℕ} (hi : i < L.length) : InS M Q L (kl M Q L i) :=
  ⟨2 * i, by omega, (kl_eq M Q L i).symm⟩

omit hK in
theorem inS_kr {i : ℕ} (hi : i < L.length) : InS M Q L (kr M Q L i) :=
  ⟨2 * i + 1, by omega, (kr_eq M Q L i).symm⟩

section
variable {i : ℕ} (hi : i < L.length)
include hi
theorem kl' : kl M' Q L i = gmap M M' Q L (kl M Q L i) := by
  rw [kl_eq, kl_eq, hK.gmap_key (by omega)]

theorem kr' : kr M' Q L i = gmap M M' Q L (kr M Q L i) := by
  rw [kr_eq, kr_eq, hK.gmap_key (by omega)]

theorem klr_lt_iff : kl M' Q L i < kr M' Q L i ↔ kl M Q L i < kr M Q L i := by
  rw [hK.kl' hi, hK.kr' hi, hK.gmap_lt (inS_kl hi) (inS_kr hi)]


end

theorem evOf_eq {c : ℕ} (hc : c < 2 * L.length) :
    evOf M' Q L c = mapEv (gmap M M' Q L) (evOf M Q L c) := by
  grind [Chazelle.Core.BoxT.KeyCongr.kl', Chazelle.Core.BoxT.KeyCongr.kr', evOf, eL, mapEv, eR]

theorem e1_eq {i : ℕ} (hi : i < L.length) : e1 M' Q L i = mapEv (gmap M M' Q L) (e1 M Q L i) := by
  grind [Chazelle.Core.BoxT.KeyCongr.klr_lt_iff, Chazelle.Core.BoxT.KeyCongr.gmap_lt, Chazelle.Core.BoxT.KeyCongr.inS_kl, Chazelle.Core.BoxT.KeyCongr.inS_kr, Chazelle.Core.BoxT.KeyCongr.kl', Chazelle.Core.BoxT.KeyCongr.kr', e1, mapEv, lo, BuildRegions.hi]

omit hK in
/-- The keys of the events of codes. -/
theorem evOf_inS {c : ℕ} (hc : c < 2 * L.length) :
    InS M Q L (evOf M Q L c).2.1 ∧ InS M Q L (evOf M Q L c).2.2 := by
  have hi : c / 2 < L.length := by omega
  unfold evOf
  split_ifs
  · exact ⟨inS_kl hi, inS_kr hi⟩
  · exact ⟨inS_kr hi, inS_kl hi⟩

omit hK in
theorem e1_inS {i : ℕ} (hi : i < L.length) :
    InS M Q L (e1 M Q L i).2.1 ∧ InS M Q L (e1 M Q L i).2.2 := by
  grind [Chazelle.Core.BoxT.KeyCongr.inS_kl, Chazelle.Core.BoxT.KeyCongr.inS_kr, e1, lo, BuildRegions.hi]

variable {E : List ℕ} (hE : ∀ c ∈ E, c < 2 * L.length)
include hE

theorem evs_eq : evs M' Q L E = (evs M Q L E).map (mapEv (gmap M M' Q L)) := by
  unfold evs
  rw [map_map]
  exact map_congr_left fun c hc => hK.evOf_eq (hE c hc)

theorem word_eq : word M' Q L E = word M Q L E := by
  unfold word
  rw [hK.evs_eq hE, map_map]
  rfl

section
variable {i : ℕ} (hi : i < L.length)
include hi
theorem outside_eq : outside M' Q L E i = outside M Q L E i := by
  unfold outside
  rw [hK.word_eq hE, hK.evs_eq hE, hK.e1_eq hi, idxOf_map_of_inj]
  intro x hx e
  unfold evs at hx
  grind [Chazelle.Core.BoxT.KeyCongr.evOf_inS, Chazelle.Core.BoxT.KeyCongr.e1_inS, Chazelle.Core.BoxT.KeyCongr.gmap_inj, mapEv, Prod.mk.injEq]

theorem chordRec_eq : chordRec M' Q L E i = chordRec M Q L E i := by
  unfold chordRec
  rw [hK.outside_eq hE hi]
  simp only [hK.klr_lt_iff hi]


end

theorem kap_eq' {m : ℕ} (hm : m < E.length) :
    kap (evs M' Q L E) m = gmap M M' Q L (kap (evs M Q L E) m) ∧
      InS M Q L (kap (evs M Q L E) m) := by
  have hm' : m < (evs M Q L E).length := by grind [evs]
  have hm'' : m < (evs M' Q L E).length := by grind [evs]
  rw [BuildSort.kap_eq hm'', BuildSort.kap_eq hm']
  grind [Chazelle.Core.BoxT.KeyCongr.evs_eq, Chazelle.Core.BoxT.KeyCongr.evOf_inS, getElem_map, mapEv, evs]

theorem gapStarts_eq : gapStarts M' Q L E = gapStarts M Q L E := by
  unfold gapStarts
  apply filter_congr
  grind [Chazelle.Core.BoxT.KeyCongr.kap_eq', Chazelle.Core.BoxT.KeyCongr.gmap_lt]

theorem arcList_eq : arcList M' Q L E = arcList M Q L E := by
  unfold arcList arcRec
  rw [hK.gapStarts_eq hE, hK.word_eq hE]

theorem regArcs_eq (r : ℕ) : regArcs M' Q L E r = regArcs M Q L E r := by
  unfold regArcs; rw [hK.arcList_eq hE]

theorem regChords_eq (r : ℕ) : regChords M' Q L E r = regChords M Q L E r := by
  unfold regChords
  apply filter_congr
  intro i hi
  rw [hK.chordRec_eq hE (mem_range.1 hi)]

theorem arcW_eq {a : ARec} (ha : a ∈ arcList M Q L E) : arcW M' Q a = arcW M Q a := by
  unfold arcList at ha
  split_ifs at ha with h0
  · rw [mem_singleton] at ha
    subst ha
    exact hK.wt0 (length_eq_zero_iff.1 h0)
  · obtain ⟨m, hm, rfl⟩ := mem_map.1 ha
    have hmE : m < E.length := mem_range.1 (mem_filter.1 hm).1
    have hpos : 0 < E.length := by omega
    have hs : E.getD m 0 < 2 * L.length := by
      simp_all
    have he : E.getD ((m + 1) % E.length) 0 < 2 * L.length := by
      rw [getD_eq_getElem _ _ (Nat.mod_lt _ hpos)]; simp_all
    exact hK.wt _ _ hs he

theorem regWt_eq (r : ℕ) : regWt M' Q L E r = regWt M Q L E r := by
  unfold regWt
  rw [hK.regArcs_eq hE, hK.arcList_eq hE]
  congr 1
  apply map_congr_left
  intro j hj
  have hj' : j < (arcList M Q L E).length := mem_range.1 (mem_filter.1 hj).1
  rw [getD_eq_getElem _ _ hj']
  exact hK.arcW_eq hE (getElem_mem _)

/-- **Congruence of `buildNF`**: models that agree on the chord list compute the same normal
form from the same event order. -/
theorem buildNF_eq : buildNF M' Q L E = buildNF M Q L E := by
  unfold buildNF
  rw [hK.arcList_eq hE]
  congr 1
  · exact map_congr_left fun i hi => hK.chordRec_eq hE (mem_range.1 hi)
  · exact map_congr_left fun r _ => by
      rw [hK.regArcs_eq hE, hK.regChords_eq hE, hK.regWt_eq hE]

omit hE

theorem tieBit_eq {c : ℕ} (hc : c < 2 * L.length) : tieBit M' L c = tieBit M L c := by
  unfold tieBit
  simp only [hK.dir c hc]

/-- **The comparators agree** on the event codes. -/
theorem codeLe_iff {c c' : ℕ} (hc : c < 2 * L.length) (hc' : c' < 2 * L.length) :
    codeLe M' Q L c c' ↔ codeLe M Q L c c' := by
  unfold codeLe
  rw [hK.lt c c' hc hc', hK.eq_iff hc hc', hK.tieBit_eq hc, hK.tieBit_eq hc']

/-- An event order sorted for `M` is sorted for `M'`. -/
theorem sorted {E : List ℕ} (hperm : E.Perm (List.range (2 * L.length)))
    (hsort : E.Pairwise (codeLe M Q L)) : E.Pairwise (codeLe M' Q L) := by
  apply hsort.imp_of_mem
  grind [Chazelle.Core.BoxT.KeyCongr.codeLe_iff]

end KeyCongr

/-! ## Degrees and weights from the records -/

namespace IsNFRec

variable {N : NF}

/-- The exit chords of a region are the chords of the indices listed in its record. -/
theorem exits_eq {reg : ℕ → Set Point} (hN : ∀ i i', i < N.nChords → i' < N.nChords →
      (N.chord i).toSet M Q = (N.chord i').toSet M Q → i = i')
    (hR : RegionsOK M Q N reg) {r : ℕ} (hr : r < N.nRegions) :
    {c | c ∈ N.F M Q ∧ Chazelle.Chain.TouchesIn M.D c (reg r)}.ncard =
      (N.region r).chords.length := by
  obtain ⟨hmem, hnd, -, -⟩ := hR r hr
  have hset : {c | c ∈ N.F M Q ∧ Chazelle.Chain.TouchesIn M.D c (reg r)} =
      (fun i => (N.chord i).toSet M Q) '' {i | i ∈ (N.region r).chords} := by
    ext c
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, ht⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
      have hc : N.chord i = N.chords[i] := by
        grind [NF.chord]
      refine ⟨i, (hmem i).2 ⟨hi, ?_⟩, ?_⟩
      all_goals grind
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨hi', ht⟩ := (hmem i).1 hi
      refine ⟨⟨N.chord i, ?_, rfl⟩, ht⟩
      unfold NF.chord; rw [getD_eq_getElem _ _ hi']; grind
  have hinj : Set.InjOn (fun i => (N.chord i).toSet M Q) {i | i ∈ (N.region r).chords} :=
    fun i hi i' hi' e => hN i i' ((hmem i).1 hi).1 ((hmem i').1 hi').1 e
  rw [hset, hinj.ncard_image]
  have : {i | i ∈ (N.region r).chords} = ((N.region r).chords.toFinset : Set ℕ) := by
    ext; simp
  rw [this, Set.ncard_coe_finset, toFinset_card_of_nodup hnd]

section
variable (h : IsNF M Q N)
include h
/-- **Bounded degree from the records.** -/
theorem degLe_iff (d : ℕ) :
    M.DegLe (N.F M Q) d ↔ ∀ r, r < N.nRegions → (N.region r).chords.length ≤ d := by
  obtain ⟨-, hinj, -, reg, hC, -, -, hR, -⟩ := h
  constructor
  · intro hD r hr
    rw [← exits_eq hinj hR hr]
    exact hD _ (hC.1 r hr)
  · intro hD U hU
    obtain ⟨r, hr, rfl⟩ := hC.2.2 U hU
    unfold Model.deg
    rw [exits_eq hinj hR hr]
    simp_all

/-- **Semigranularity from the records.** -/
theorem semigranular_iff (γ : ℕ) :
    M.Semigranular (N.F M Q) γ ↔ ∀ r, r < N.nRegions → (N.region r).wt ≤ γ := by
  obtain ⟨-, -, -, reg, hC, -, -, hR, -⟩ := h
  constructor
  · intro hS r hr
    rw [(hR r hr).2.2.2]
    exact hS _ (hC.1 r hr)
  · intro hS U hU
    obtain ⟨r, hr, rfl⟩ := hC.2.2 U hU
    rw [← (hR r hr).2.2.2]
    simp_all


end

/-- **Transfer of degree and weight bounds** between two models in which the same record is a
valid normal form. -/
theorem transfer {N : NF} (h : IsNF M Q N) (h' : IsNF M' Q N) {d γ : ℕ}
    (hd : M.DegLe (N.F M Q) d) (hγ : M.Semigranular (N.F M Q) γ) :
    M'.DegLe (N.F M' Q) d ∧ M'.Semigranular (N.F M' Q) γ :=
  ⟨(degLe_iff h' d).2 ((degLe_iff h d).1 hd),
    (semigranular_iff h' γ).2 ((semigranular_iff h γ).1 hγ)⟩

end IsNFRec

end

end BoxT

end Chazelle.Core
