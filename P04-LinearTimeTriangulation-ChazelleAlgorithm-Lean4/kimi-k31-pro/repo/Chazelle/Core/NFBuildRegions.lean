module

public import Chazelle.Core.NFBuildOrder
public import Chazelle.Core.NFBuildGap
public import Chazelle.Core.NFBuildGeom
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.ChainTactics

/-!
# WP-C (BuildNF): the regions of a submap are the labels of the stack pass

Let `L` be a valid chord list (`ChordTriplesOK`) of a walk-axiom model, and `S` an ordering of
its attachment events (`BuildOrder.events`) sorted by `BuildSort.EvLe` (key, then the tie rule);
`w = S.map fst` is its chord word, a parenthesis word (`BuildOrder.parenthesis_of_sorted`).  For a
non-cut key `y`, `gapLabel S y` is the label of the stack pass after the events with key below
`y`: the innermost chord whose key interval contains `y` (`none` for the root).

## Results

* `faces_same_iff`: two non-cut positions inside walk edges face the same region iff their keys
  have the same gap label;
* `side_labels`: for chord `i`, whose first event in `S` is at position `|u|` (`S = u ++ e :: v`),
  the region faced at non-cut keys with label `label w (|u| + 1) = some i` is the region below
  the chord if its first event is its left endpoint (`key lpos < key rpos`) and above it
  otherwise, and the region faced at keys with label `label w |u|` (the label before the chord's
  opening event, i.e. its parent) is the other side.

These are the facts that make the stack pass compute the region records of the normal form: the
regions are the `K + 1` labels, and chord `i` has the sides `some i` (inside) and the label before
its opening event (outside), `up`/`dn` fixed by the orientation of its first event.
-/

namespace Chazelle.Core

namespace BuildRegions

@[expose] public section

open Set List
open Chazelle.Chain (SideAttach sideInArc sidePt sideKey_inj TouchesIn)
open BuildSort (Ev EvLe cycDist cntBelow)
open BuildOrder (events evPair chordSet mem_events event_data getD_mem chordSet_inj chordSet_mem)

/-! ## The context -/

/-- The chord family of a triple list. -/
def famOf (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) : Set (Set Point) :=
  {c | ∃ x ∈ L, c = (recOf x).toSet M Q}

/-- **A sorted event list** of a valid chord list in a walk-axiom model. -/
structure Ctx (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (S : List Ev) : Prop where
  walk : WalkAx M
  valid : ChordTriplesOK M Q L
  perm : S.Perm (events M Q L)
  sorted : S.Pairwise (EvLe M.W.n)

variable {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {S : List Ev}

/-- The record of chord `i`. -/
def crec (L : List (ℕ × ℕ × ℕ)) (i : ℕ) : CRec := recOf (L.getD i (0, 0, 0))

/-- The key of the left endpoint of chord `i`. -/
noncomputable def kl (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (i : ℕ) : ℝ :=
  M.key Q (crec L i).lpos

/-- The key of the right endpoint of chord `i`. -/
noncomputable def kr (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (i : ℕ) : ℝ :=
  M.key Q (crec L i).rpos

/-- The event of the left endpoint of chord `i`. -/
noncomputable def eL (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (i : ℕ) : Ev :=
  (i, kl M Q L i, kr M Q L i)

/-- The event of the right endpoint of chord `i`. -/
noncomputable def eR (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (i : ℕ) : Ev :=
  (i, kr M Q L i, kl M Q L i)

theorem evPair_eq (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (i : ℕ) :
    evPair M Q L i = [eL M Q L i, eR M Q L i] := rfl

/-- The smaller key of chord `i`. -/
noncomputable def lo (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (i : ℕ) : ℝ :=
  min (kl M Q L i) (kr M Q L i)

/-- The larger key of chord `i`. -/
noncomputable def hi (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (i : ℕ) : ℝ :=
  max (kl M Q L i) (kr M Q L i)

/-- The first event of chord `i` (the one with the smaller key). -/
noncomputable def e1 (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (i : ℕ) : Ev :=
  (i, lo M Q L i, hi M Q L i)

/-- The second event of chord `i`. -/
noncomputable def e2 (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (i : ℕ) : Ev :=
  (i, hi M Q L i, lo M Q L i)

/-- **The gap label** of a key `y`: the label of the stack pass after the events with key below
`y`. -/
noncomputable def gapLabel (S : List Ev) (y : ℝ) : Option ℕ :=
  BuildStack.label (S.map Prod.fst) (cntBelow S y)

/-- Chord `j` is nested in chord `i`'s closed key interval... reversed: `i` lies within `j`. -/
def Within (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (i j : ℕ) : Prop :=
  lo M Q L j ≤ lo M Q L i ∧ hi M Q L i ≤ hi M Q L j

/-- **The region of a label**: the region faced at the non-cut keys with that gap label (the
empty set for a label that no non-cut key has). -/
noncomputable def reg (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (S : List Ev)
    (ℓ : Option ℕ) : Set Point := by
  classical
  exact if hh : ∃ U ∈ M.regions (famOf M Q L), ∃ (p : ℕ) (t : ℝ), p < M.W.n ∧ 0 < t ∧ t < 1 ∧
      ¬ M.IsCut (famOf M Q L) (p + t) ∧ gapLabel S (p + t) = ℓ ∧ M.Faces p t U
    then hh.choose else ∅

/-- The labels of the stack pass over `K` chords: the root `none` and `some i`, `i < K`. -/
def LabelOK (K : ℕ) (ℓ : Option ℕ) : Prop := ∀ i, ℓ = some i → i < K

namespace Ctx

variable (h : Ctx M Q L S)
include h

theorem mem_iff (e : Ev) : e ∈ S ↔ e ∈ events M Q L := h.perm.mem_iff

theorem finite : (famOf M Q L).Finite := h.valid.1.1

theorem adm : famOf M Q L ⊆ M.Adm := h.valid.1.2.1

/-- The attachment of the left endpoint of chord `i`. -/
theorem attL {i : ℕ} (hi : i < L.length) :
    SideAttach M.W (chordSet M Q L i) (crec L i).lp (M.param Q (crec L i).lpos) := by
  have := h.valid.2.2.1 (L.getD i (0, 0, 0)) (getD_mem hi)
  exact this.1

/-- The attachment of the right endpoint of chord `i`. -/
theorem attR {i : ℕ} (hi : i < L.length) :
    SideAttach M.W (chordSet M Q L i) (crec L i).rp (M.param Q (crec L i).rpos) := by
  have := h.valid.2.2.1 (L.getD i (0, 0, 0)) (getD_mem hi)
  exact this.2

/-- The left endpoint is left of the right endpoint. -/
theorem pos_lt {i : ℕ} (hi : i < L.length) :
    (M.pos Q (crec L i).lpos).1 < (M.pos Q (crec L i).rpos).1 := by
  have := h.valid.2.2.1 (L.getD i (0, 0, 0)) (getD_mem hi)
  exact BuildOrder.endpoints h.walk (h.adm (chordSet_mem hi)) this

theorem pts_ne {i : ℕ} (hi : i < L.length) :
    sidePt M.W (crec L i).lp (M.param Q (crec L i).lpos) ≠
      sidePt M.W (crec L i).rp (M.param Q (crec L i).rpos) := by
  intro heq
  have hlt := h.pos_lt hi
  have : M.pos Q (crec L i).lpos = M.pos Q (crec L i).rpos := heq
  rw [this] at hlt
  exact lt_irrefl _ hlt

theorem kl_ne_kr {i : ℕ} (hi : i < L.length) : kl M Q L i ≠ kr M Q L i :=
  WalkAx.key_ne_of_pt_ne (h.attL hi) (h.attR hi) (h.pts_ne hi)

omit h in
theorem key_bounds {pa : ℕ} {ta : ℝ} {c : Set Point} (hA : SideAttach M.W c pa ta) :
    0 ≤ (pa : ℝ) + ta ∧ (pa : ℝ) + ta < M.W.n := by
  have : (pa : ℝ) + 1 ≤ M.W.n := by exact_mod_cast hA.1
  exact ⟨by have := hA.2.1; positivity, by linarith [hA.2.2.1]⟩

theorem kl_bounds {i : ℕ} (hi : i < L.length) : 0 ≤ kl M Q L i ∧ kl M Q L i < M.W.n :=
  key_bounds (h.attL hi)

theorem kr_bounds {i : ℕ} (hi : i < L.length) : 0 ≤ kr M Q L i ∧ kr M Q L i < M.W.n :=
  key_bounds (h.attR hi)

theorem eL_mem {i : ℕ} (hi : i < L.length) : eL M Q L i ∈ S :=
  (h.mem_iff _).2 (mem_events.2 ⟨i, hi, by rws [evPair_eq]⟩)

theorem eR_mem {i : ℕ} (hi : i < L.length) : eR M Q L i ∈ S :=
  (h.mem_iff _).2 (mem_events.2 ⟨i, hi, by rws [evPair_eq]⟩)

theorem eL_ne_eR {i : ℕ} (hi : i < L.length) : eL M Q L i ≠ eR M Q L i := by
  intro heq
  apply h.kl_ne_kr hi
  have := congrArg (fun e : Ev => e.2.1) heq
  simpa [eL, eR] using this

/-- Every event is the left or the right event of its chord. -/
theorem mem_cases {e : Ev} (he : e ∈ S) :
    e.1 < L.length ∧ (e = eL M Q L e.1 ∨ e = eR M Q L e.1) := by
  obtain ⟨i, hi, he⟩ := mem_events.1 ((h.mem_iff e).1 he)
  rw [evPair_eq] at he
  rcases mem_cons.1 he with rfl | he
  · exact ⟨hi, Or.inl rfl⟩
  · rw [List.mem_singleton] at he; subst he; exact ⟨hi, Or.inr rfl⟩

theorem events_nodup : (events M Q L).Nodup := by
  unfold events
  rw [nodup_flatMap]
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [evPair_eq, nodup_cons, List.mem_singleton]
    refine ⟨?_, nodup_singleton _⟩
    exact h.eL_ne_eR (mem_range.1 hi)
  · refine (nodup_range).pairwise_of_forall_ne fun i _ j _ hij => ?_
    rw [Function.onFun, disjoint_iff_ne]
    intro a ha b hb hab
    rw [evPair_eq] at ha hb
    have hfst : ∀ k, ∀ x ∈ [eL M Q L k, eR M Q L k], x.1 = k := by
      intro k x hx
      simp [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl <;> rfl
    have h1  := hfst i a ha
    have h2  := hfst j b hb
    exact hij (h1.symm.trans ((congrArg Prod.fst hab).trans h2))

theorem nodup : S.Nodup := h.perm.nodup_iff.2 h.events_nodup

theorem lo_lt_hi {i : ℕ} (hi' : i < L.length) : lo M Q L i < hi M Q L i := by
  unfold lo hi
  rcases lt_or_gt_of_ne (h.kl_ne_kr hi') with h1 | h1
  · rwx [min_eq_left h1.le, max_eq_right h1.le]
  · rwx [min_eq_right h1.le, max_eq_left h1.le]

theorem lo_bounds {i : ℕ} (hi' : i < L.length) : 0 ≤ lo M Q L i ∧ lo M Q L i < M.W.n := by
  unfold lo
  exact ⟨le_min (h.kl_bounds hi').1 (h.kr_bounds hi').1,
    (min_le_left _ _).trans_lt (h.kl_bounds hi').2⟩

theorem hi_bounds {i : ℕ} (hi' : i < L.length) : 0 ≤ hi M Q L i ∧ hi M Q L i < M.W.n := by
  unfold hi
  exact ⟨(h.kl_bounds hi').1.trans (le_max_left _ _),
    max_lt (h.kl_bounds hi').2 (h.kr_bounds hi').2⟩

omit h in
/-- The first and second events are the left and right events, in key order. -/
theorem e1_e2_cases (_h : Ctx M Q L S) (i : ℕ) :
    (kl M Q L i < kr M Q L i ∧ e1 M Q L i = eL M Q L i ∧ e2 M Q L i = eR M Q L i) ∨
      (kr M Q L i ≤ kl M Q L i ∧ e1 M Q L i = eR M Q L i ∧ e2 M Q L i = eL M Q L i) := by
  unfold e1 e2 eL eR lo hi
  rcases lt_or_ge (kl M Q L i) (kr M Q L i) with h1 | h1
  · left; rw [min_eq_left h1.le, max_eq_right h1.le]; exact ⟨h1, rfl, rfl⟩
  · right; rw [min_eq_right h1, max_eq_left h1]; exact ⟨h1, rfl, rfl⟩

theorem e1_mem {i : ℕ} (hi' : i < L.length) : e1 M Q L i ∈ S := by
  rcases h.e1_e2_cases i with ⟨-, h1, -⟩ | ⟨-, h1, -⟩ <;> rw [h1]
  · exact h.eL_mem hi'
  · exact h.eR_mem hi'

theorem e2_mem {i : ℕ} (hi' : i < L.length) : e2 M Q L i ∈ S := by
  rcases h.e1_e2_cases i with ⟨-, -, h1⟩ | ⟨-, -, h1⟩ <;> rw [h1]
  · exact h.eR_mem hi'
  · exact h.eL_mem hi'

theorem e1_ne_e2 {i : ℕ} (hi' : i < L.length) : e1 M Q L i ≠ e2 M Q L i := by
  intro heq
  have := congrArg (fun e : Ev => e.2.1) heq
  simp [e1, e2] at this
  exact (h.lo_lt_hi hi').ne this

/-- Every event of chord `j` is its first or its second event. -/
theorem mem_cases' {f : Ev} (hf : f ∈ S) :
    f.1 < L.length ∧ (f = e1 M Q L f.1 ∨ f = e2 M Q L f.1) := by
  obtain ⟨hlt, hc⟩ := h.mem_cases hf
  refine ⟨hlt, ?_⟩
  rcases h.e1_e2_cases f.1 with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
  · rwx [h1, h2]
  · rw [h1, h2]; exact hc.symm

/-- The attachments of chord `i` at its two keys, in key order. -/
theorem att_lo_hi {i : ℕ} (hi' : i < L.length) :
    ∃ (pa pb : ℕ) (ta tb : ℝ), SideAttach M.W (chordSet M Q L i) pa ta ∧
      SideAttach M.W (chordSet M Q L i) pb tb ∧ sidePt M.W pa ta ≠ sidePt M.W pb tb ∧
      (pa : ℝ) + ta = lo M Q L i ∧ (pb : ℝ) + tb = hi M Q L i := by
  rcases h.e1_e2_cases i with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
  · have hlo : lo M Q L i = kl M Q L i := min_eq_left h0.le
    have hhi : hi M Q L i = kr M Q L i := max_eq_right h0.le
    exact ⟨_, _, _, _, h.attL hi', h.attR hi', h.pts_ne hi', by rwr [hlo], by rwr [hhi]⟩
  · have hlo : lo M Q L i = kr M Q L i := min_eq_right h0
    have hhi : hi M Q L i = kl M Q L i := max_eq_left h0
    exact ⟨_, _, _, _, h.attR hi', h.attL hi', Ne.symm (h.pts_ne hi'), by rwr [hlo],
      by rwr [hhi]⟩

/-- **No crossing**, in key order. -/
theorem no_cross_keys {i j : ℕ} (hi' : i < L.length) (hj : j < L.length) (hij : i ≠ j) :
    ¬ (lo M Q L i < lo M Q L j ∧ lo M Q L j < hi M Q L i ∧ hi M Q L i < hi M Q L j) := by
  rintro ⟨h1, h2, h3⟩
  obtain ⟨pa, pb, ta, tb, hA, hB, hAB, ka, kb⟩ := h.att_lo_hi hi'
  obtain ⟨pc, pd, tc, td, hC, hD, -, kc, kd⟩ := h.att_lo_hi hj
  have hne : chordSet M Q L i ≠ chordSet M Q L j := fun e => hij (chordSet_inj h.valid hi' hj e)
  apply h.walk.no_cross h.adm h.finite (chordSet_mem hi') (chordSet_mem hj) hne hA hB hAB hC hD
  rw [ka, kb, kc, kd]
  have hlh := h.lo_lt_hi hi'
  unfold sideInArc
  rw [ite_eq_left hlh, ite_eq_right (not_lt.2 hlh.le)]
  exact ⟨⟨h1, h2⟩, Or.inl h3⟩

/-- **Distinct chords have distinct key pairs.** -/
theorem keys_ne {i j : ℕ} (hi' : i < L.length) (hj : j < L.length) (hij : i ≠ j) :
    ¬ (lo M Q L i = lo M Q L j ∧ hi M Q L i = hi M Q L j) := by
  rintro ⟨h1, h2⟩
  obtain ⟨pa, pb, ta, tb, hA, hB, hAB, ka, kb⟩ := h.att_lo_hi hi'
  obtain ⟨pc, pd, tc, td, hC, hD, hCD, kc, kd⟩ := h.att_lo_hi hj
  obtain ⟨rfl, rfl⟩ := sideKey_inj hA.2.1 hA.2.2.1 hC.2.1 hC.2.2.1 (by rw [ka, kc, h1])
  obtain ⟨rfl, rfl⟩ := sideKey_inj hB.2.1 hB.2.2.1 hD.2.1 hD.2.2.1 (by rw [kb, kd, h2])
  have e1 := (h.walk.attach_seg (h.adm (chordSet_mem hi')) hA hB hAB).1
  have e2 := (h.walk.attach_seg (h.adm (chordSet_mem hj)) hC hD hCD).1
  exact hij (chordSet_inj h.valid hi' hj (e1.trans e2.symm))

/-- The keys of the events are cut keys: a non-cut key is no event key. -/
theorem key_ne_of_not_cut {y : ℝ} (hy : ¬ M.IsCut (famOf M Q L) y) : ∀ e ∈ S, e.2.1 ≠ y := by
  intro e he hey
  obtain ⟨hi', hc⟩ := h.mem_cases he
  apply hy
  rcases hc with hc | hc <;> rw [hc] at hey
  · exact ⟨_, chordSet_mem hi', _, _, h.attL hi', hey.symm⟩
  · exact ⟨_, chordSet_mem hi', _, _, h.attR hi', hey.symm⟩

omit h in
/-- Every chord of the family is a chord of the list. -/
theorem fam_cases (_h : Ctx M Q L S) {c : Set Point} (hc : c ∈ famOf M Q L) :
    ∃ j < L.length, c = chordSet M Q L j := by
  obtain ⟨x, hx, rfl⟩ := hc
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
  refine ⟨j, hj, ?_⟩
  unfold chordSet
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

/-! ## Open chords at a key -/

/-- **Chord `j` is open at a non-event key `y`** iff `y` is strictly between its keys. -/
theorem open_iff {y : ℝ} (hy : ∀ e ∈ S, e.2.1 ≠ y) {j : ℕ} (hj : j < L.length) :
    ((S.filter (fun e => decide (e.2.1 < y))).map Prod.fst).count j = 1 ↔
      lo M Q L j < y ∧ y < hi M Q L j := by
  rw [BuildSort.count_two (j := j) (h.nodup.filter _) (h.e1_ne_e2 hj) rfl rfl
    (fun f hf hfj => by
      have := (h.mem_cases' (mem_of_mem_filter hf)).2
      rw [hfj] at this; exact this)]
  have m1 : (j, lo M Q L j, hi M Q L j) ∈ S := h.e1_mem hj
  have m2 : (j, hi M Q L j, lo M Q L j) ∈ S := h.e2_mem hj
  simp [e1, e2, mem_filter, decide_eq_true_eq, m1, m2, true_and]
  have hlh := h.lo_lt_hi hj
  have h1 := hy _ (h.e1_mem hj)
  have h2 := hy _ (h.e2_mem hj)
  simp [e1, e2] at h1 h2
  constructor
  · intro hc
    by_cases hlo : lo M Q L j < y
    · refine ⟨hlo, lt_of_le_of_ne (not_lt.1 fun hh => ?_) (Ne.symm h2)⟩
      rwo [ite_eq_left hlo, ite_eq_left hh] at hc
    · rw [ite_eq_right hlo] at hc
      by_cases hh : hi M Q L j < y
      · exfalso; linarith [not_lt.1 hlo]
      · rwo [ite_eq_right hh] at hc
  · rintro ⟨h3, h4⟩
    rw [ite_eq_left h3, ite_eq_right (not_lt.2 h4.le)]

/-- A chord index beyond the list is never open. -/
theorem count_ge {y : ℝ} {j : ℕ} (hj : L.length ≤ j) :
    ((S.filter (fun e => decide (e.2.1 < y))).map Prod.fst).count j = 0 := by
  rw [count_eq_zero, mem_map]
  rintro ⟨f, hf, rfl⟩
  have := (h.mem_cases (mem_of_mem_filter hf)).1
  omega

/-! ## Gap labels -/

/-- The chord word of the sorted events is a parenthesis word. -/
theorem word : BuildStack.NoCross (S.map Prod.fst) ∧ BuildStack.Twice (S.map Prod.fst) :=
  BuildOrder.parenthesis_of_sorted h.walk h.valid h.perm h.sorted

/-- **Two non-event keys have the same gap label iff every chord contains both or neither.** -/
theorem gapLabel_eq_iff {y y' : ℝ} (hy : ∀ e ∈ S, e.2.1 ≠ y) (hy' : ∀ e ∈ S, e.2.1 ≠ y') :
    gapLabel S y = gapLabel S y' ↔ ∀ j < L.length,
      (lo M Q L j < y ∧ y < hi M Q L j ↔ lo M Q L j < y' ∧ y' < hi M Q L j) := by
  obtain ⟨hnc, htw⟩ := h.word
  unfold gapLabel
  rw [BuildStack.label_eq_iff htw hnc, BuildSort.take_map_cntBelow h.sorted hy,
    BuildSort.take_map_cntBelow h.sorted hy']
  constructor
  · intro H j hj
    rw [← h.open_iff hy hj, ← h.open_iff hy' hj]
    exact H j
  · intro H j
    rcases lt_or_ge j L.length with hj | hj
    · rw [h.open_iff hy hj, h.open_iff hy' hj]; exact H j hj
    · rw [h.count_ge hj, h.count_ge hj]

/-- A key strictly inside a chord's arc from its smaller to its larger key. -/
theorem sideInArc_lo_hi {j : ℕ} (hj : j < L.length) (y : ℝ) :
    sideInArc (lo M Q L j) (hi M Q L j) y ↔ lo M Q L j < y ∧ y < hi M Q L j := by
  unfold sideInArc; rw [ite_eq_left (h.lo_lt_hi hj)]

/-- A key outside a chord's closed key interval is in its arc from the larger to the smaller key. -/
theorem sideInArc_hi_lo {j : ℕ} (hj : j < L.length) {y : ℝ} (h1 : y < lo M Q L j ∨ hi M Q L j < y) :
    sideInArc (hi M Q L j) (lo M Q L j) y := by
  unfold sideInArc; rw [ite_eq_right (not_lt.2 (h.lo_lt_hi hj).le)]; tauto

/-- **Two non-cut positions face the same region iff their keys have the same gap label.** -/
theorem faces_same_iff {p p' : ℕ} {t t' : ℝ} {U U' : Set Point}
    (hU : U ∈ M.regions (famOf M Q L)) (hU' : U' ∈ M.regions (famOf M Q L))
    (hp : p < M.W.n) (hp' : p' < M.W.n) (ht : t ∈ Ioo (0 : ℝ) 1) (ht' : t' ∈ Ioo (0 : ℝ) 1)
    (hcut : ¬ M.IsCut (famOf M Q L) (p + t)) (hcut' : ¬ M.IsCut (famOf M Q L) (p' + t'))
    (hf : M.Faces p t U) (hf' : M.Faces p' t' U') :
    U = U' ↔ gapLabel S (p + t) = gapLabel S (p' + t') := by
  have hy := h.key_ne_of_not_cut hcut
  have hy' := h.key_ne_of_not_cut hcut'
  rw [h.walk.eq_iff_not_separates h.adm h.finite hU hU' hp hp' ht ht' hcut hcut' hf hf',
    h.gapLabel_eq_iff hy hy']
  have hsep : ∀ j < L.length, (M.Separates (chordSet M Q L j) (p + t) (p' + t') ↔
      ¬ (lo M Q L j < p + t ∧ p + t < hi M Q L j ↔
        lo M Q L j < p' + t' ∧ p' + t' < hi M Q L j)) := by
    intro j hj
    obtain ⟨pa, pb, ta, tb, hA, hB, hAB, ka, kb⟩ := h.att_lo_hi hj
    have n1 := hy _ (h.e1_mem hj)
    have n2 := hy _ (h.e2_mem hj)
    have n3 := hy' _ (h.e1_mem hj)
    have n4 := hy' _ (h.e2_mem hj)
    simp [e1, e2] at n1 n2 n3 n4
    rw [h.walk.separates_iff (h.adm (chordSet_mem hj)) hA hB hAB (by rw [ka]; exact Ne.symm n1)
      (by rw [kb]; exact Ne.symm n2) (by rw [ka]; exact Ne.symm n3) (by rw [kb]; exact Ne.symm n4),
      ka, kb, h.sideInArc_lo_hi hj, h.sideInArc_lo_hi hj]
    tauto
  constructor
  · intro H j hj
    have := H _ (chordSet_mem hj)
    rw [hsep j hj] at this
    tauto
  · intro H c hc
    obtain ⟨j, hj, rfl⟩ := h.fam_cases hc
    rw [hsep j hj]
    exact not_not.2 (H j hj)

/-! ## Nesting: the prefix before a chord's first event -/

/-- **The chords open just before the first event of chord `i`** are the chords containing it. -/
theorem prefix_open {u v : List Ev} {i j : ℕ} (hsplit : S = u ++ e1 M Q L i :: v)
    (hi' : i < L.length) (hj : j < L.length) (hij : j ≠ i) :
    (u.map Prod.fst).count j = 1 ↔ Within M Q L i j := by
  have hs := h.sorted
  rw [hsplit] at hs
  have hnd := h.nodup
  rw [hsplit, nodup_append] at hnd
  have hmemS : ∀ f, f ∈ S → f ∈ u ++ e1 M Q L i :: v := fun f hf => hsplit ▸ hf
  rw [BuildSort.count_two (j := j) hnd.1 (h.e1_ne_e2 hj) rfl rfl
    (fun f hf hfj => by
      have := (h.mem_cases' (hsplit ▸ mem_append_left _ hf)).2
      rw [hfj] at this; exact this)]
  have hne1 : e1 M Q L j ≠ e1 M Q L i := fun he => hij (congrArg Prod.fst he)
  have hne2 : e2 M Q L j ≠ e1 M Q L i := fun he => hij (congrArg Prod.fst he)
  have hsp1 := BuildSort.mem_split_of_ne (hmemS _ (h.e1_mem hj)) hne1
  have hsp2 := BuildSort.mem_split_of_ne (hmemS _ (h.e2_mem hj)) hne2
  have hdisj : ∀ f, f ∈ u → f ∉ v := fun f hfu hfv =>
    hnd.2.2 f hfu f (mem_cons_of_mem _ hfv) rfl
  have hlh := h.lo_lt_hi hi'
  have hlhj := h.lo_lt_hi hj
  have hbi := (h.hi_bounds hi').2
  have haj := (h.lo_bounds hj).1
  have hcyc1 : ∀ x : ℕ, x < L.length → cycDist M.W.n (lo M Q L x) (hi M Q L x) =
      hi M Q L x - lo M Q L x := fun x hx => by
    unfold cycDist; rw [ite_eq_left (h.lo_lt_hi hx)]
  have hcyc2 : ∀ x : ℕ, x < L.length → cycDist M.W.n (hi M Q L x) (lo M Q L x) =
      lo M Q L x - hi M Q L x + M.W.n := fun x hx => by
    unfold cycDist; rw [ite_eq_right (not_lt.2 (h.lo_lt_hi hx).le)]
  constructor
  · intro hc
    by_cases h1 : e1 M Q L j ∈ u
    · have h2 : e2 M Q L j ∉ u := by
        intro h2; rwo [ite_eq_left h1, ite_eq_left h2] at hc
      have h2v := hsp2.resolve_left h2
      have le1 := BuildSort.evLe_of_mem_left hs h1
      have le2 := BuildSort.evLe_of_mem_right hs h2v
      unfold EvLe at le1 le2
      simp [e1, e2] at le1 le2
      rw [hcyc1 i hi', hcyc1 j hj] at le1
      rw [hcyc2 j hj, hcyc1 i hi'] at le2
      refine ⟨by rcases le1 with h3 | h3; exact h3.le; exact h3.1.le, ?_⟩
      rcases le1 with h3 | ⟨h3, h4⟩
      · rcases le2 with h5 | ⟨h5, h6⟩
        · by_contra h7
          exact h.no_cross_keys hj hi' hij ⟨h3, h5, lt_of_not_ge h7⟩
        · exfalso; rwli [← h5] at h6
      · linarith
    · have h2 : e2 M Q L j ∈ u := by
        by_contra h2; rwo [ite_eq_right h1, ite_eq_right h2] at hc
      have h1v := hsp1.resolve_left h1
      have le1 := BuildSort.key_le_of_evLe (BuildSort.evLe_of_mem_left hs h2)
      have le2 := BuildSort.key_le_of_evLe (BuildSort.evLe_of_mem_right hs h1v)
      simp [e1, e2] at le1 le2
      exfalso; linarith
  · rintro ⟨hw1, hw2⟩
    have h2 : e2 M Q L j ∉ u := by
      intro h2
      have := BuildSort.key_le_of_evLe (BuildSort.evLe_of_mem_left hs h2)
      simp [e1, e2] at this
      linarith
    have h1 : e1 M Q L j ∈ u := by
      by_contra h1
      have h1v := hsp1.resolve_left h1
      have le := BuildSort.evLe_of_mem_right hs h1v
      unfold EvLe at le
      simp [e1] at le
      rw [hcyc1 i hi', hcyc1 j hj] at le
      rcases le with h3 | ⟨h3, h4⟩
      · linarith
      · exact h.keys_ne hi' hj (Ne.symm hij) ⟨h3, by linarith⟩
    rw [ite_eq_left h1, ite_eq_right h2]

/-- **A region touching chord `i`, faced at a non-cut key `y`**: for every other chord `j`, `y` is
strictly inside `j` iff `i` lies within `j`. -/
theorem touch_within {U : Set Point} (hU : U ∈ M.regions (famOf M Q L)) {p : ℕ} {t : ℝ}
    (hp : p < M.W.n) (ht : t ∈ Ioo (0 : ℝ) 1) (hcut : ¬ M.IsCut (famOf M Q L) (p + t))
    (hf : M.Faces p t U) {i j : ℕ} (hi' : i < L.length) (hj : j < L.length) (hij : j ≠ i)
    (htouch : TouchesIn M.D (chordSet M Q L i) U) :
    (lo M Q L j < p + t ∧ p + t < hi M Q L j) ↔ Within M Q L i j := by
  have hy := h.key_ne_of_not_cut hcut
  obtain ⟨pa, pb, ta, tb, hA, hB, hAB, ka, kb⟩ := h.att_lo_hi hj
  obtain ⟨pc, pd, tc, td, hC, hD, -, kc, kd⟩ := h.att_lo_hi hi'
  have hne : chordSet M Q L i ≠ chordSet M Q L j := fun e => hij (chordSet_inj h.valid hj hi' e.symm)
  have n1 := hy _ (h.e1_mem hj)
  have n2 := hy _ (h.e2_mem hj)
  simp [e1, e2] at n1 n2
  have hlhi := h.lo_lt_hi hi'
  constructor
  · intro hin
    by_contra hw
    unfold Within at hw
    have hout : ∃ (q : ℕ) (τ : ℝ), SideAttach M.W (chordSet M Q L i) q τ ∧
        sideInArc (pb + tb) (pa + ta) (q + τ) := by
      rw [ka, kb]
      by_cases h1 : lo M Q L j ≤ lo M Q L i
      · have h2 : hi M Q L j < hi M Q L i := lt_of_not_ge fun h2 => hw ⟨h1, h2⟩
        exact ⟨pd, td, hD, by rw [kd]; exact h.sideInArc_hi_lo hj (Or.inr h2)⟩
      · exact ⟨pc, tc, hC, by rw [kc]; exact h.sideInArc_hi_lo hj (Or.inl (lt_of_not_ge h1))⟩
    obtain ⟨q, τ, hQ, hq⟩ := hout
    exact h.walk.not_touches_of_split h.adm h.finite (chordSet_mem hi') (chordSet_mem hj) hne
      hA hB hAB hU hp ht (by rwx [ka, kb, h.sideInArc_lo_hi hj]) hf hQ hq htouch
  · rintro ⟨hw1, hw2⟩
    by_contra hin
    have hy' : sideInArc (hi M Q L j) (lo M Q L j) (p + t) := by
      apply h.sideInArc_hi_lo hj
      by_contra h3
      push Not at h3
      exact hin ⟨lt_of_le_of_ne h3.1 n1, lt_of_le_of_ne h3.2 (Ne.symm n2)⟩
    have hin2 : ∃ (q : ℕ) (τ : ℝ), SideAttach M.W (chordSet M Q L i) q τ ∧
        sideInArc (pa + ta) (pb + tb) (q + τ) := by
      rw [ka, kb]
      rcases hw1.lt_or_eq with h1 | h1
      · exact ⟨pc, tc, hC, by rw [kc, h.sideInArc_lo_hi hj]; exact ⟨h1, by linarith⟩⟩
      · have h2 : hi M Q L i < hi M Q L j :=
          lt_of_le_of_ne hw2 fun h2 => h.keys_ne hi' hj (Ne.symm hij) ⟨h1.symm, h2⟩
        exact ⟨pd, td, hD, by rw [kd, h.sideInArc_lo_hi hj]; exact ⟨by linarith, h2⟩⟩
    obtain ⟨q, τ, hQ, hq⟩ := hin2
    exact h.walk.not_touches_of_split h.adm h.finite (chordSet_mem hi') (chordSet_mem hj) hne
      hB hA (Ne.symm hAB) hU hp ht (by rwx [ka, kb]) hf hQ hq htouch

/-! ## The region of a label -/

/-- **Every non-cut position faces the region of its gap label.** -/
theorem faces_reg {p : ℕ} {t : ℝ} (hp : p < M.W.n) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hcut : ¬ M.IsCut (famOf M Q L) (p + t)) :
    reg M Q L S (gapLabel S (p + t)) ∈ M.regions (famOf M Q L) ∧
      M.Faces p t (reg M Q L S (gapLabel S (p + t))) := by
  classical
  obtain ⟨U, hU, hf⟩ := h.walk.exists_faces_of_not_cut h.adm h.finite hp ht hcut
  have hh : ∃ U ∈ M.regions (famOf M Q L), ∃ (p' : ℕ) (t' : ℝ), p' < M.W.n ∧ 0 < t' ∧ t' < 1 ∧
      ¬ M.IsCut (famOf M Q L) (p' + t') ∧ gapLabel S (p' + t') = gapLabel S (p + t) ∧
        M.Faces p' t' U := ⟨U, hU, p, t, hp, ht.1, ht.2, hcut, rfl, hf⟩
  have hreg : reg M Q L S (gapLabel S (p + t)) = hh.choose := by
    unfold reg; rw [dite_eq_left hh]
  obtain ⟨hU', p', t', hp', ht0', ht1', hcut', hlab, hf'⟩ := hh.choose_spec
  have heq  := (h.faces_same_iff hU' hU hp' hp ⟨ht0', ht1'⟩ ht hcut' hcut hf' hf).2 hlab
  rw [hreg, heq]
  exact ⟨hU, hf⟩

/-- The region faced at a non-cut position is the region of its gap label. -/
theorem reg_eq_of_faces {p : ℕ} {t : ℝ} (hp : p < M.W.n) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hcut : ¬ M.IsCut (famOf M Q L) (p + t)) {U : Set Point} (hU : U ∈ M.regions (famOf M Q L))
    (hf : M.Faces p t U) : reg M Q L S (gapLabel S (p + t)) = U := by
  obtain ⟨hR, hfR⟩ := h.faces_reg hp ht hcut
  exact WalkAx.faces_unique hR hU hfR hf

omit h in
/-- The prefix of the chord word before the event at the end of `u`. -/
theorem take_word (_h : Ctx M Q L S) {u v : List Ev} {e : Ev} (hsplit : S = u ++ e :: v) :
    (S.map Prod.fst).take u.length = u.map Prod.fst := by
  rw [← map_take, hsplit, take_left' rfl]

omit h in
theorem take_word_succ (_h : Ctx M Q L S) {u v : List Ev} {e : Ev} (hsplit : S = u ++ e :: v) :
    (S.map Prod.fst).take (u.length + 1) = u.map Prod.fst ++ [e.1] := by
  rw [← map_take, hsplit, show u ++ e :: v = (u ++ [e]) ++ v by simp,
    take_left' (by simp), map_append, map_singleton]

/-- The first event of a chord is not in the prefix before it, nor is its second event. -/
theorem count_prefix_self {u v : List Ev} {i : ℕ} (hsplit : S = u ++ e1 M Q L i :: v)
    (hi' : i < L.length) : (u.map Prod.fst).count i = 0 := by
  have hs := h.sorted
  rw [hsplit] at hs
  have hnd := h.nodup
  rw [hsplit, nodup_append] at hnd
  rw [BuildSort.count_two (j := i) hnd.1 (h.e1_ne_e2 hi') rfl rfl
    (fun f hf hfj => by
      have := (h.mem_cases' (hsplit ▸ mem_append_left _ hf)).2
      rw [hfj] at this; exact this)]
  have h1 : e1 M Q L i ∉ u := fun h1 => hnd.2.2 _ h1 _ mem_cons_self rfl
  have h2 : e2 M Q L i ∉ u := by
    intro h2
    have := BuildSort.key_le_of_evLe (BuildSort.evLe_of_mem_left hs h2)
    simp [e1, e2] at this
    linarith [h.lo_lt_hi hi']
  rw [ite_eq_right h1, ite_eq_right h2]

/-- The chord indices of the prefix are chords of the list. -/
theorem count_prefix_ge {u v : List Ev} {e : Ev} (hsplit : S = u ++ e :: v) {j : ℕ}
    (hj : L.length ≤ j) : (u.map Prod.fst).count j = 0 := by
  rw [count_eq_zero, mem_map]
  rintro ⟨f, hf, rfl⟩
  have := (h.mem_cases (hsplit ▸ mem_append_left _ hf)).1
  omega

/-- **The label right after the first event of chord `i` is `some i`.** -/
theorem label_first {u v : List Ev} {i : ℕ} (hsplit : S = u ++ e1 M Q L i :: v)
    (hi' : i < L.length) : BuildStack.label (S.map Prod.fst) (u.length + 1) = some i := by
  obtain ⟨hnc, htw⟩ := h.word
  rw [BuildStack.label_eq htw hnc, h.take_word_succ hsplit, show (e1 M Q L i).1 = i from rfl,
    BuildStack.openList_snoc_open (h.count_prefix_self hsplit hi')]
  rfl

/-- **A region touching chord `i` on the outside** has the label before the first event of `i`. -/
theorem label_outside {u v : List Ev} {i : ℕ} (hsplit : S = u ++ e1 M Q L i :: v)
    (hi' : i < L.length) {U : Set Point} (hU : U ∈ M.regions (famOf M Q L)) {p : ℕ} {t : ℝ}
    (hp : p < M.W.n) (ht : t ∈ Ioo (0 : ℝ) 1) (hcut : ¬ M.IsCut (famOf M Q L) (p + t))
    (hf : M.Faces p t U) (htouch : TouchesIn M.D (chordSet M Q L i) U)
    (hout : ¬ (lo M Q L i < p + t ∧ p + t < hi M Q L i)) :
    gapLabel S (p + t) = BuildStack.label (S.map Prod.fst) u.length := by
  obtain ⟨hnc, htw⟩ := h.word
  have hy := h.key_ne_of_not_cut hcut
  unfold gapLabel
  rw [BuildStack.label_eq_iff htw hnc, BuildSort.take_map_cntBelow h.sorted hy,
    h.take_word hsplit]
  intro j
  rcases lt_or_ge j L.length with hj | hj
  · rw [h.open_iff hy hj]
    by_cases hji : j = i
    · subst hji
      rw [h.count_prefix_self hsplit hi']
      exact ⟨fun h' => absurd h' hout, fun h' => absurd h' (by omega)⟩
    · rw [h.prefix_open hsplit hi' hj hji]
      exact h.touch_within hU hp ht hcut hf hi' hj hji htouch
  · rw [h.count_ge hj, h.count_prefix_ge hsplit hj]

/-- **A region touching chord `i` on the inside** has the label `some i`. -/
theorem label_inside {u v : List Ev} {i : ℕ} (hsplit : S = u ++ e1 M Q L i :: v)
    (hi' : i < L.length) {U : Set Point} (hU : U ∈ M.regions (famOf M Q L)) {p : ℕ} {t : ℝ}
    (hp : p < M.W.n) (ht : t ∈ Ioo (0 : ℝ) 1) (hcut : ¬ M.IsCut (famOf M Q L) (p + t))
    (hf : M.Faces p t U) (htouch : TouchesIn M.D (chordSet M Q L i) U)
    (hin : lo M Q L i < p + t ∧ p + t < hi M Q L i) :
    gapLabel S (p + t) = BuildStack.label (S.map Prod.fst) (u.length + 1) := by
  obtain ⟨hnc, htw⟩ := h.word
  have hy := h.key_ne_of_not_cut hcut
  unfold gapLabel
  rw [BuildStack.label_eq_iff htw hnc, BuildSort.take_map_cntBelow h.sorted hy,
    h.take_word_succ hsplit, show (e1 M Q L i).1 = i from rfl]
  intro j
  rw [count_append, count_singleton']
  rcases lt_or_ge j L.length with hj | hj
  · rw [h.open_iff hy hj]
    by_cases hji : j = i
    · subst hji
      rw [h.count_prefix_self hsplit hi']
      simp [hin]
    · rw [ite_eq_right (Ne.symm hji), add_zero, h.prefix_open hsplit hi' hj hji]
      exact h.touch_within hU hp ht hcut hf hi' hj hji htouch
  · have hji : i ≠ j := by omega
    rw [h.count_ge hj, h.count_prefix_ge hsplit hj, ite_eq_right hji]

/-! ## The two sides of a chord -/

/-- **The two sides of chord `i`** are the regions of the labels right after (inside) and right
before (outside) its first event: if its first event is its left endpoint, the inside is below
the chord and the outside above; otherwise the inside is above and the outside below. -/
theorem sides {u v : List Ev} {i : ℕ} (hsplit : S = u ++ e1 M Q L i :: v)
    (hi' : i < L.length) :
    reg M Q L S (BuildStack.label (S.map Prod.fst) (u.length + 1)) ∈ M.regions (famOf M Q L) ∧
      reg M Q L S (BuildStack.label (S.map Prod.fst) u.length) ∈ M.regions (famOf M Q L) ∧
      (kl M Q L i < kr M Q L i →
        M.BelowOf (chordSet M Q L i) (reg M Q L S (BuildStack.label (S.map Prod.fst) (u.length + 1))) ∧
        M.AboveOf (chordSet M Q L i) (reg M Q L S (BuildStack.label (S.map Prod.fst) u.length))) ∧
      (kr M Q L i < kl M Q L i →
        M.AboveOf (chordSet M Q L i) (reg M Q L S (BuildStack.label (S.map Prod.fst) (u.length + 1))) ∧
        M.BelowOf (chordSet M Q L i) (reg M Q L S (BuildStack.label (S.map Prod.fst) u.length))) := by
  set c := chordSet M Q L i with hc
  have hcF : c ∈ famOf M Q L := chordSet_mem hi'
  have hsys := h.walk.sys _ h.adm h.finite
  obtain ⟨Up, Dn, hUp, hDn, -, hside, htouch⟩ := chordSides_of_system hsys hcF
  have hAbove : M.AboveOf c Up := fun z hz hzD => (hside z hz hzD).mono fun _ h => h.1
  have hBelow : M.BelowOf c Dn := fun z hz hzD => (hside z hz hzD).mono fun _ h => h.2
  obtain ⟨pu, tu, hpu, htu0, htu1, hcu, hfu⟩ := h.walk.exists_faces_nc h.adm h.finite hUp
  obtain ⟨pd, td, hpd, htd0, htd1, hcd, hfd⟩ := h.walk.exists_faces_nc h.adm h.finite hDn
  have htU : TouchesIn M.D c Up := (htouch Up hUp).2 (Or.inl rfl)
  have htD : TouchesIn M.D c Dn := (htouch Dn hDn).2 (Or.inr rfl)
  -- the attachments and the midpoints
  have hA := h.attL hi'
  have hB := h.attR hi'
  have hAB := h.pts_ne hi'
  set pl := sidePt M.W (crec L i).lp (M.param Q (crec L i).lpos) with hpl
  set pr := sidePt M.W (crec L i).rp (M.param Q (crec L i).rpos) with hpr
  obtain ⟨hcab, hy, hopen, -, -⟩ := h.walk.attach_seg (h.adm hcF) hA hB hAB
  have hlt : pl.1 < pr.1 := h.pos_lt hi'
  have hmid : Geometry.lerp pl pr (1 / 2) ∈ c := by
    rw [hcab]; exact Geometry.lerp_mem_segment _ _ (by norm_num) (by norm_num)
  have hmidD : Geometry.lerp pl pr (1 / 2) ∈ M.D := hopen _ ⟨by norm_num, by norm_num⟩
  have hmid' : Geometry.lerp pr pl (1 / 2) ∈ c := by
    rw [hcab, Geometry.segment_comm]; exact Geometry.lerp_mem_segment _ _ (by norm_num) (by norm_num)
  have hmidD' : Geometry.lerp pr pl (1 / 2) ∈ M.D :=
    WalkAx.open_rev hopen _ ⟨by norm_num, by norm_num⟩
  -- `Up` is not faced strictly between the left and the right endpoint
  have hnU : ¬ sideInArc (kl M Q L i) (kr M Q L i) (pu + tu) := by
    intro hin
    refine h.walk.not_left_of_after h.adm hcF hA hB hAB hUp hpu ⟨htu0, htu1⟩ hin hfu ?_
    refine (eventually_mul_pos (hAbove _ hmid hmidD) (sub_pos.2 hlt)).mono fun δ hδ => ?_
    rw [Chazelle.Core.offset_mid_ab hy]; exact hδ
  -- `Dn` is not faced strictly between the right and the left endpoint
  have hnD : ¬ sideInArc (kr M Q L i) (kl M Q L i) (pd + td) := by
    intro hin
    refine h.walk.not_left_of_after h.adm hcF hB hA (Ne.symm hAB) hDn hpd ⟨htd0, htd1⟩ hin hfd ?_
    refine (eventually_mul_pos (hBelow _ hmid' hmidD') (sub_pos.2 hlt)).mono fun δ hδ => ?_
    rw [Chazelle.Core.offset_mid_ab hy.symm]
    convert hδ using 2; ring
  -- the keys differ from the non-cut keys
  have nU1 := h.key_ne_of_not_cut hcu _ (h.eL_mem hi')
  have nU2 := h.key_ne_of_not_cut hcu _ (h.eR_mem hi')
  have nD1 := h.key_ne_of_not_cut hcd _ (h.eL_mem hi')
  have nD2 := h.key_ne_of_not_cut hcd _ (h.eR_mem hi')
  simp [eL, eR] at nU1 nU2 nD1 nD2
  have hregU := h.reg_eq_of_faces hpu ⟨htu0, htu1⟩ hcu hUp hfu
  have hregD := h.reg_eq_of_faces hpd ⟨htd0, htd1⟩ hcd hDn hfd
  rcases lt_or_gt_of_ne (h.kl_ne_kr hi') with hk | hk
  · have hlo : lo M Q L i = kl M Q L i := min_eq_left hk.le
    have hhi : hi M Q L i = kr M Q L i := max_eq_right hk.le
    -- `Up` outside, `Dn` inside
    have hUout : ¬ (lo M Q L i < pu + tu ∧ pu + tu < hi M Q L i) := by
      rw [hlo, hhi]; intro h'; apply hnU; unfold sideInArc; rwx [ite_eq_left hk]
    have hDin : lo M Q L i < pd + td ∧ pd + td < hi M Q L i := by
      rw [hlo, hhi]
      unfold sideInArc at hnD; rw [ite_eq_right (not_lt.2 hk.le)] at hnD
      push Not at hnD
      exact ⟨lt_of_le_of_ne hnD.2 nD1, lt_of_le_of_ne hnD.1 (Ne.symm nD2)⟩
    have e1' := h.label_outside hsplit hi' hUp hpu ⟨htu0, htu1⟩ hcu hfu htU hUout
    have e2' := h.label_inside hsplit hi' hDn hpd ⟨htd0, htd1⟩ hcd hfd htD hDin
    rw [e1'] at hregU
    rw [e2'] at hregD
    rw [hregU, hregD]
    exact ⟨hDn, hUp, fun _ => ⟨hBelow, hAbove⟩, fun h' => absurd h' (not_lt.2 hk.le)⟩
  · have hlo : lo M Q L i = kr M Q L i := min_eq_right hk.le
    have hhi : hi M Q L i = kl M Q L i := max_eq_left hk.le
    -- `Up` inside, `Dn` outside
    have hUin : lo M Q L i < pu + tu ∧ pu + tu < hi M Q L i := by
      rw [hlo, hhi]
      unfold sideInArc at hnU; rw [ite_eq_right (not_lt.2 hk.le)] at hnU
      push Not at hnU
      exact ⟨lt_of_le_of_ne hnU.2 nU2, lt_of_le_of_ne hnU.1 (Ne.symm nU1)⟩
    have hDout : ¬ (lo M Q L i < pd + td ∧ pd + td < hi M Q L i) := by
      rw [hlo, hhi]; intro h'; apply hnD; unfold sideInArc; rwx [ite_eq_left hk]
    have e1' := h.label_inside hsplit hi' hUp hpu ⟨htu0, htu1⟩ hcu hfu htU hUin
    have e2' := h.label_outside hsplit hi' hDn hpd ⟨htd0, htd1⟩ hcd hfd htD hDout
    rw [e1'] at hregU
    rw [e2'] at hregD
    rw [hregU, hregD]
    exact ⟨hUp, hDn, fun h' => absurd h' (not_lt.2 hk.le), fun _ => ⟨hAbove, hBelow⟩⟩

/-! ## Regions and labels correspond -/

/-- Every label of the stack pass is a label of a chord of the list, or the root. -/
theorem label_ok (m : ℕ) : LabelOK L.length (BuildStack.label (S.map Prod.fst) m) := by
  obtain ⟨hnc, htw⟩ := h.word
  intro i hl
  rw [BuildStack.label_eq htw hnc] at hl
  have hi := BuildStack.mem_openList.1 (mem_of_mem_head? hl)
  have hmem : i ∈ S.map Prod.fst :=
    mem_of_mem_take (count_pos_iff.1 (by rw [hi]; norm_num : 0 < ((S.map Prod.fst).take m).count i))
  obtain ⟨f, hf, rfl⟩ := mem_map.1 hmem
  exact (h.mem_cases hf).1

omit h in
/-- A region of a label is faced at a non-cut key with that label. -/
theorem reg_realized {ℓ : Option ℕ} (hr : reg M Q L S ℓ ∈ M.regions (famOf M Q L)) :
    ∃ (p : ℕ) (t : ℝ), p < M.W.n ∧ 0 < t ∧ t < 1 ∧ ¬ M.IsCut (famOf M Q L) (p + t) ∧
      gapLabel S (p + t) = ℓ ∧ M.Faces p t (reg M Q L S ℓ) := by
  classical
  by_cases hh : ∃ U ∈ M.regions (famOf M Q L), ∃ (p : ℕ) (t : ℝ), p < M.W.n ∧ 0 < t ∧ t < 1 ∧
      ¬ M.IsCut (famOf M Q L) (p + t) ∧ gapLabel S (p + t) = ℓ ∧ M.Faces p t U
  · have hreg : reg M Q L S ℓ = hh.choose := by unfold reg; rw [dite_eq_left hh]
    obtain ⟨-, p, t, hp, ht0, ht1, hcut, hlab, hf⟩ := hh.choose_spec
    exact ⟨p, t, hp, ht0, ht1, hcut, hlab, hreg ▸ hf⟩
  · have hreg : reg M Q L S ℓ = ∅ := by unfold reg; rw [dite_eq_right hh]
    rw [hreg] at hr
    obtain ⟨x, hx⟩ := Chazelle.Chain.regionsIn_nonempty hr
    exact absurd hx (Set.notMem_empty x)

/-- The first event of the sorted list is the first event of its chord. -/
theorem first_split (hK : 0 < L.length) :
    ∃ i < L.length, ∃ v, S = [] ++ e1 M Q L i :: v := by
  rcases hS : S with _ | ⟨f, v⟩
  · exact absurd (hS ▸ h.e1_mem hK) (List.not_mem_nil)
  · have hf : f ∈ S := by rw [hS]; exact mem_cons_self
    obtain ⟨hi, hc⟩ := h.mem_cases' hf
    refine ⟨f.1, hi, v, ?_⟩
    rcases hc with hc | hc
    · rwr [← hc]
    · exfalso
      have hs := h.sorted
      rw [hS, pairwise_cons] at hs
      have h1 : e1 M Q L f.1 ∈ v := by
        have := h.e1_mem hi
        rw [hS, mem_cons] at this
        exact this.resolve_left fun he => h.e1_ne_e2 hi (he ▸ hc)
      have := BuildSort.key_le_of_evLe (hs.1 _ h1)
      rw [hc] at this
      simp [e1, e2] at this
      linarith [h.lo_lt_hi hi]

/-- **The regions of the labels are exactly the regions of the submap, each once.** -/
theorem regions_corr :
    (∀ ℓ, LabelOK L.length ℓ → reg M Q L S ℓ ∈ M.regions (famOf M Q L)) ∧
      (∀ ℓ ℓ', LabelOK L.length ℓ → LabelOK L.length ℓ' → reg M Q L S ℓ = reg M Q L S ℓ' →
        ℓ = ℓ') ∧
      (∀ U ∈ M.regions (famOf M Q L), ∃ ℓ, LabelOK L.length ℓ ∧ reg M Q L S ℓ = U) := by
  obtain ⟨hnc, htw⟩ := h.word
  have hsys := h.walk.sys _ h.adm h.finite
  have hmemR : ∀ ℓ, LabelOK L.length ℓ → reg M Q L S ℓ ∈ M.regions (famOf M Q L) := by
    intro ℓ hℓ
    rcases ℓ with _ | i
    · -- the root
      rcases Nat.eq_zero_or_pos L.length with hK | hK
      · -- no chord: every non-cut position has the root label
        obtain ⟨hfin, hcard⟩ := hsys.regionsIn_finite_ncard h.walk.preconn h.walk.nonempty subset_rfl
        have hne : (M.regions (famOf M Q L)).Nonempty :=
          Set.nonempty_of_ncard_ne_zero (by
            change (Chazelle.Chain.regionsIn M.D (famOf M Q L)).ncard ≠ 0
            omega)
        obtain ⟨U, hU⟩ := hne
        obtain ⟨p, t, hp, ht0, ht1, hcut, hf⟩ := h.walk.exists_faces_nc h.adm h.finite hU
        have hS : S = [] := by
          rcases hS : S with _ | ⟨f, v⟩
          · rfl
          · have := (h.mem_cases (by rw [hS]; exact mem_cons_self : f ∈ S)).1; omega
        have hlab : gapLabel S (p + t) = none := by
          urr gapLabel [hS]
        have := (h.faces_reg hp ⟨ht0, ht1⟩ hcut).1
        rwa [hlab] at this
      · obtain ⟨i, hi, v, hsplit⟩ := h.first_split hK
        have := (h.sides hsplit hi).2.1
        have h0 : BuildStack.label (S.map Prod.fst) ([] : List Ev).length = none := by
          simp [List.length_nil]
          unfold BuildStack.label; simp [BuildStack.run]
        rwa [h0] at this
    · have hi : i < L.length := hℓ i rfl
      obtain ⟨u, v, hsplit⟩ := List.append_of_mem (h.e1_mem hi)
      have := (h.sides hsplit hi).1
      rwa [h.label_first hsplit hi] at this
  refine ⟨hmemR, fun ℓ ℓ' hℓ hℓ' heq => ?_, fun U hU => ?_⟩
  · obtain ⟨p, t, hp, ht0, ht1, hcut, hlab, hf⟩ := reg_realized (hmemR ℓ hℓ)
    obtain ⟨p', t', hp', ht0', ht1', hcut', hlab', hf'⟩ := reg_realized (hmemR ℓ' hℓ')
    rw [← hlab, ← hlab']
    exact (h.faces_same_iff (hmemR ℓ hℓ) (hmemR ℓ' hℓ') hp hp' ⟨ht0, ht1⟩ ⟨ht0', ht1'⟩ hcut hcut'
      hf hf').1 heq
  · obtain ⟨p, t, hp, ht0, ht1, hcut, hf⟩ := h.walk.exists_faces_nc h.adm h.finite hU
    refine ⟨gapLabel S (p + t), h.label_ok _, h.reg_eq_of_faces hp ⟨ht0, ht1⟩ hcut hU hf⟩

end Ctx

end

end BuildRegions

end Chazelle.Core
