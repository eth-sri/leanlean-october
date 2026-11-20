module

public import Chazelle.Core.GranWt

/-!
# WP-F, part 4: what a valid normal form tells the granularity procedure

For a valid normal form `N` (`IsNF M Q N`, region correspondence `reg`) of a model satisfying the
walk axioms:

* chords: `cs M Q N i` is the chord of record `i`; `mem_F_iff`, `cs_inj`;
* attachments: a chord of a record is attached exactly at the keys of its two walk positions
  `lpos`, `rpos` (`attach_keys`), which differ (`lkey_ne_rkey`); a subfamily given by a set of
  record indices has exactly these keys as cuts (`isCut_fam_iff`);
* the **arc ring**: the start keys `pk i` of the arcs in the order of the sequence table are
  strictly increasing (`pk_strict`), are cuts (`pk_cut`), and every cut is one of them
  (`cut_pk`);
* regions: the exit chords, degree and weight of region `r` are stored in its record
  (`deg_region`, `wt_region`), and chord `i` touches exactly the regions `up` and `dn` of its
  record (`touch_iff_side`, `up_ne_dn`).
-/

namespace Chazelle.Core

namespace Gran

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (SideAttach sideInArc sidePt ChordSystem freeIn regionsIn TouchesIn)

variable {M : Model} {Q : Polygon} {N : NF}

/-- The chord of record `i`. -/
noncomputable def cs (M : Model) (Q : Polygon) (N : NF) (i : ℕ) : Set Point :=
  (N.chord i).toSet M Q

/-- The start key of the arc at position `i` of the sequence table. -/
noncomputable def pk (M : Model) (Q : Polygon) (N : NF) (i : ℕ) : ℝ :=
  M.key Q (N.arc (N.seq.getD i 0)).s

/-- The subfamily of the records with indices in `L`. -/
def fam (M : Model) (Q : Polygon) (N : NF) (L : Set ℕ) : Set (Set Point) :=
  {c | ∃ i ∈ L, i < N.nChords ∧ c = cs M Q N i}

theorem mem_F_iff {c : Set Point} : c ∈ N.F M Q ↔ ∃ i, i < N.nChords ∧ c = cs M Q N i := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨i, hi, e⟩ := List.mem_iff_getElem.1 hr
    refine ⟨i, hi, ?_⟩
    unfold cs NF.chord
    rw [NFLoc.getD_of_lt _ hi, e]
  · rintro ⟨i, hi, rfl⟩
    refine ⟨N.chords[i], List.getElem_mem hi, ?_⟩
    unfold cs NF.chord
    rw [NFLoc.getD_of_lt _ hi]

theorem cs_mem {i : ℕ} (hi : i < N.nChords) : cs M Q N i ∈ N.F M Q := mem_F_iff.2 ⟨i, hi, rfl⟩

theorem fam_univ : fam M Q N univ = N.F M Q := by
  ext c
  rw [mem_F_iff]
  constructor
  · rintro ⟨i, -, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩; exact ⟨i, mem_univ _, hi, rfl⟩

theorem fam_sub (L : Set ℕ) : fam M Q N L ⊆ N.F M Q := by
  rintro c ⟨i, -, hi, rfl⟩; exact cs_mem hi

section valid

variable (hN : IsNF M Q N)
include hN

theorem cs_inj {i i' : ℕ} (hi : i < N.nChords) (hi' : i' < N.nChords)
    (h : cs M Q N i = cs M Q N i') : i = i' :=
  hN.2.1 i i' hi hi' h

theorem F_adm : N.F M Q ⊆ M.Adm := hN.1.2.1

theorem F_finite : (N.F M Q).Finite := hN.1.1

theorem fam_adm (L : Set ℕ) : fam M Q N L ⊆ M.Adm := (fam_sub L).trans (F_adm hN)

theorem fam_finite (L : Set ℕ) : (fam M Q N L).Finite := (F_finite hN).subset (fam_sub L)

theorem fam_chordFamily (L : Set ℕ) : M.ChordFamily Q (fam M Q N L) :=
  ⟨fam_finite hN L, fam_adm hN L, fun c hc => hN.1.2.2 c (fam_sub L hc)⟩

/-- The record's left position is an attachment of its chord. -/
theorem attach_l {i : ℕ} (hi : i < N.nChords) :
    SideAttach M.W (cs M Q N i) (N.chord i).lp (M.param Q (N.chord i).lpos) :=
  (hN.2.2.1 i hi).1

theorem attach_r {i : ℕ} (hi : i < N.nChords) :
    SideAttach M.W (cs M Q N i) (N.chord i).rp (M.param Q (N.chord i).rpos) :=
  (hN.2.2.1 i hi).2

omit hN in
theorem key_lpos (i : ℕ) :
    M.key Q (N.chord i).lpos = ((N.chord i).lp : ℝ) + M.param Q (N.chord i).lpos := rfl

omit hN in
theorem key_rpos (i : ℕ) :
    M.key Q (N.chord i).rpos = ((N.chord i).rp : ℝ) + M.param Q (N.chord i).rpos := rfl

omit hN in
/-- The point of a walk position is the side point at its parameter. -/
theorem pos_eq_sidePt (x : WPos) : M.pos Q x = sidePt M.W x.edge (M.param Q x) := rfl

/-- The two attachments of a record's chord have distinct points. -/
theorem lpt_ne_rpt (hM : WalkAx M) {i : ℕ} (hi : i < N.nChords) :
    sidePt M.W (N.chord i).lp (M.param Q (N.chord i).lpos) ≠
      sidePt M.W (N.chord i).rp (M.param Q (N.chord i).rpos) := by
  intro he
  have hc : cs M Q N i ∈ M.Adm := F_adm hN (cs_mem hi)
  obtain ⟨a, b, hab, hcab, -, -, -, -⟩ := hM.ends _ hc
  -- the chord is `hseg y x₁ x₂` with `x₁ = x₂`: a single point
  have hset : cs M Q N i = Visibility.hseg (Q.vtx (N.chord i).h).2
      (M.pos Q (N.chord i).lpos).1 (M.pos Q (N.chord i).rpos).1 := rfl
  have hx : (M.pos Q (N.chord i).lpos).1 = (M.pos Q (N.chord i).rpos).1 := by
    rw [pos_eq_sidePt, pos_eq_sidePt]
    exact congrArg Prod.fst he
  have ha : a ∈ cs M Q N i := by rw [hcab]; exact Geometry.left_mem_segment a b
  have hb : b ∈ cs M Q N i := by rw [hcab]; exact Geometry.right_mem_segment a b
  rw [hset] at ha hb
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  rw [hx] at ha2 hb2
  exact hab (Prod.ext (by linarith) (by rw [ha1, hb1]))

/-- **The attachments of a record's chord** are at the keys of its two positions. -/
theorem attach_keys (hM : WalkAx M) {i : ℕ} (hi : i < N.nChords) {p : ℕ} {t : ℝ}
    (hA : SideAttach M.W (cs M Q N i) p t) :
    (p : ℝ) + t = M.key Q (N.chord i).lpos ∨ (p : ℝ) + t = M.key Q (N.chord i).rpos := by
  have hc : cs M Q N i ∈ M.Adm := F_adm hN (cs_mem hi)
  have hL := attach_l hN hi
  have hR := attach_r hN hi
  obtain ⟨hceq, -, hopen, -, -⟩ := hM.attach_seg hc hL hR (lpt_ne_rpt hN hM hi)
  have hA' := hA
  rw [hceq] at hA'
  rcases hM.attach_endpoint hopen hA' with h | h
  · obtain ⟨e1, e2⟩ := WalkAx.attach_unique hM hc hA hL h
    left; rw [key_lpos, e1, e2]
  · obtain ⟨e1, e2⟩ := WalkAx.attach_unique hM hc hA hR h
    right; rw [key_rpos, e1, e2]

/-- The two keys of a record differ. -/
theorem lkey_ne_rkey (hM : WalkAx M) {i : ℕ} (hi : i < N.nChords) :
    M.key Q (N.chord i).lpos ≠ M.key Q (N.chord i).rpos := by
  rw [key_lpos, key_rpos]
  exact WalkAx.key_ne_of_pt_ne (attach_l hN hi) (attach_r hN hi) (lpt_ne_rpt hN hM hi)

/-- **The cuts of a subfamily** are the keys of the positions of its records. -/
theorem isCut_fam_iff (hM : WalkAx M) (L : Set ℕ) (k : ℝ) :
    M.IsCut (fam M Q N L) k ↔ ∃ i ∈ L, i < N.nChords ∧
      (k = M.key Q (N.chord i).lpos ∨ k = M.key Q (N.chord i).rpos) := by
  constructor
  · rintro ⟨c, ⟨i, hiL, hi, rfl⟩, p, t, hA, rfl⟩
    exact ⟨i, hiL, hi, attach_keys hN hM hi hA⟩
  · rintro ⟨i, hiL, hi, h | h⟩
    · exact ⟨cs M Q N i, ⟨i, hiL, hi, rfl⟩, _, _, attach_l hN hi, h⟩
    · exact ⟨cs M Q N i, ⟨i, hiL, hi, rfl⟩, _, _, attach_r hN hi, h⟩

/-! ### The arc ring -/

theorem seq_nodup : N.seq.Nodup := by
  obtain ⟨-, -, -, hS⟩ := NFLoc.isNF_arcs hN
  exact hS.1.nodup_iff.2 List.nodup_range

theorem seq_inj {i i' : ℕ} (hi : i < N.arcs.length) (hi' : i' < N.arcs.length)
    (h : N.seq.getD i 0 = N.seq.getD i' 0) : i = i' := by
  have hl := NFLoc.seq_length hN
  rw [NFLoc.getD_of_lt 0 (by omega), NFLoc.getD_of_lt 0 (by omega)] at h
  exact (List.Nodup.getElem_inj_iff (seq_nodup hN)).1 h

/-- Distinct arcs of a nonempty submap start at distinct keys. -/
theorem start_inj (hne : (N.F M Q).Nonempty) {j j' : ℕ} (hj : j < N.arcs.length)
    (hj' : j' < N.arcs.length) (h : M.key Q (N.arc j).s = M.key Q (N.arc j').s) : j = j' := by
  obtain ⟨-, -, -, reg, hRC, -, hAO, -⟩ := hN
  obtain ⟨hr, ha⟩ := hAO.1 j hj
  obtain ⟨hr', ha'⟩ := hAO.1 j' hj'
  rw [h] at ha
  obtain ⟨-, hreg⟩ := arc_start_unique hne (hRC.1 _ hr) (hRC.1 _ hr') ha ha'
  have e := hRC.2.1 _ _ hr hr' hreg
  exact hAO.2.1 j j' hj hj' e h

/-- The start keys along the sequence table are cuts. -/
theorem pk_cut (hne : (N.F M Q).Nonempty) {i : ℕ} (hi : i < N.arcs.length) :
    M.IsCut (N.F M Q) (pk M Q N i) := by
  obtain ⟨U, hU⟩ := NFLoc.isArc_of_listed hN (NFLoc.seq_lt hN hi)
  exact (WalkAx.arc_cuts hne hU).1

/-- **The start keys are strictly increasing along the sequence table.** -/
theorem pk_strict (hne : (N.F M Q).Nonempty) {i i' : ℕ} (hii : i < i')
    (hi' : i' < N.arcs.length) : pk M Q N i < pk M Q N i' := by
  refine lt_of_le_of_ne (NFLoc.seq_sorted hN hii.le hi') fun h => ?_
  have := start_inj hN hne (NFLoc.seq_lt hN (by omega)) (NFLoc.seq_lt hN hi') h
  have := seq_inj hN (by omega) hi' this
  omega

theorem pk_inj (hne : (N.F M Q).Nonempty) {i i' : ℕ} (hi : i < N.arcs.length)
    (hi' : i' < N.arcs.length) (h : pk M Q N i = pk M Q N i') : i = i' := by
  rcases lt_trichotomy i i' with h' | h' | h'
  · exact absurd h (ne_of_lt (pk_strict hN hne h' hi'))
  · exact h'
  · exact absurd h.symm (ne_of_lt (pk_strict hN hne h' hi))

/-- **Every cut is a start key** (from the arc cover `arcCover`). -/
theorem cut_pk (hGM : GoodModel M) {k : ℝ} (hk : M.IsCut (N.F M Q) k) :
    ∃ i, i < N.arcs.length ∧ pk M Q N i = k := by
  obtain ⟨-, hcov⟩ := arcCover M Q (N.F M Q) hGM hN.1
  obtain ⟨U, hU, b, hab⟩ := hcov k hk
  obtain ⟨j, hj, hs, -⟩ := NFLoc.listed_of_isArc hN hU hab
  obtain ⟨i, hi, hij⟩ := NFLoc.seq_surj hN hj
  exact ⟨i, hi, by unfold pk; rw [hij, hs]⟩

/-! ### Regions -/

variable {reg : ℕ → Set Point}

omit hN in
/-- The degree of region `r` is the length of its chord list. -/
theorem deg_region (hNF : IsNF M Q N) (_hRC : RegionCorr M Q N reg)
    (hRO : RegionsOK M Q N reg) {r : ℕ} (hr : r < N.nRegions) :
    M.deg (N.F M Q) (reg r) = (N.region r).chords.length := by
  obtain ⟨hmem, hnd, -, -⟩ := hRO r hr
  unfold Model.deg
  have e : {c | c ∈ N.F M Q ∧ TouchesIn M.D c (reg r)} =
      (fun i => cs M Q N i) '' {i | i ∈ (N.region r).chords} := by
    ext c
    simp only [mem_ofPred_eq, mem_image]
    constructor
    · rintro ⟨hc, ht⟩
      obtain ⟨i, hi, rfl⟩ := mem_F_iff.1 hc
      exact ⟨i, (hmem i).2 ⟨hi, ht⟩, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨hi', ht⟩ := (hmem i).1 hi
      exact ⟨cs_mem hi', ht⟩
  have hinj : Set.InjOn (fun i => cs M Q N i) {i | i ∈ (N.region r).chords} := by
    intro i hi i' hi' h
    exact cs_inj hNF ((hmem i).1 hi).1 ((hmem i').1 hi').1 h
  rw [e, hinj.ncard_image]
  rw [show {i | i ∈ (N.region r).chords} = ((N.region r).chords.toFinset : Set ℕ) by
    ext; simp]
  rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]

omit hN in
/-- **Chord `i` touches exactly the regions `up` and `dn` of its record**, which differ. -/
theorem touch_iff_side (hNF : IsNF M Q N) (hM : WalkAx M) (hRC : RegionCorr M Q N reg)
    (hCS : ChordSidesOK M Q N reg) {i : ℕ} (hi : i < N.nChords) :
    (N.chord i).up ≠ (N.chord i).dn ∧ ∀ r, r < N.nRegions →
      (TouchesIn M.D (cs M Q N i) (reg r) ↔ r = (N.chord i).up ∨ r = (N.chord i).dn) := by
  have hsys := hM.sys _ (F_adm hNF) (F_finite hNF)
  obtain ⟨U, V, hU, hV, hUV, hside, htouch⟩ := Chazelle.Core.chordSides_of_system hsys (cs_mem hi)
  obtain ⟨hup, hdn, hCSi⟩ := hCS i hi
  -- a point of the open part of the chord
  have hc : cs M Q N i ∈ M.Adm := F_adm hNF (cs_mem hi)
  obtain ⟨a, b, -, hcab, -, hopen, -, -⟩ := hM.ends _ hc
  set z := Geometry.lerp a b (1 / 2) with hz
  have hzD : z ∈ M.D := hopen _ ⟨by norm_num, by norm_num⟩
  have hzc : z ∈ cs M Q N i := by
    rw [hcab]; exact Geometry.lerp_mem_segment a b (by norm_num) (by norm_num)
  obtain ⟨ε₀, hε₀, hε⟩ := hCSi z hzc hzD
  obtain ⟨δ, ⟨h1, h2⟩, hδ0, hδ1⟩ := ((hside z hzc hzD).and (Ioo_mem_nhdsGT hε₀)).exists
  obtain ⟨e1, e2⟩ := hε δ hδ0 hδ1
  have hUup : U = reg (N.chord i).up := by
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint hU (hRC.1 _ hup) with h | h
    · exact h
    · exact absurd e1 (h.notMem_of_mem_left h1)
  have hVdn : V = reg (N.chord i).dn := by
    rcases Chazelle.Chain.regionsIn_eq_or_disjoint hV (hRC.1 _ hdn) with h | h
    · exact h
    · exact absurd e2 (h.notMem_of_mem_left h2)
  refine ⟨fun h => hUV (by rw [hUup, hVdn, h]), fun r hr => ?_⟩
  rw [htouch _ (hRC.1 r hr), hUup, hVdn]
  constructor
  · rintro (h | h)
    · exact Or.inl (hRC.2.1 _ _ hr hup h)
    · exact Or.inr (hRC.2.1 _ _ hr hdn h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

end valid

end

end Gran

end Chazelle.Core
