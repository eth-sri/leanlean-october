module

public import Chazelle.Core.SweepEvStopM2

/-!
# The sweep (WP-D), stage 2: the stop list from the raw records (mathematics)

The RAM produces raw stop records (one per origin and attachment on the `C₁` part), each with a
**leaving direction** code `dc` (`1`: the position is the left end of the chord, `0`: its right
end).  Sorted by the key `(offset, dc)` (lexicographic) and with equal neighbours dropped
(`DInv`, the invariant of the dedupe pass), they give the stop list (`stopsOK_of`): same
position and same leaving direction is the same chord (`aug_eq_of_lend`, `aug_eq_of_rend`).
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (SideAttach sidePt)
open Chazelle.Merge (FreeAt)
open WalkEmbed

namespace SweepStop

open Sweep SweepEv

/-! ## Lexicographic keys -/

/-- The lexicographic order of keys `(offset, code)`. -/
def KLe (a b : ℝ × ℕ) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)

/-- The strict lexicographic order. -/
def KLt (a b : ℝ × ℕ) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

theorem KLe.trans {a b c : ℝ × ℕ} (h1 : KLe a b) (h2 : KLe b c) : KLe a c := by
  unfold KLe at *
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · exact Or.inl (h1.trans h2)
  · exact Or.inl (by rwa [← h2])
  · exact Or.inl (by rwa [h1])
  · exact Or.inr ⟨h1.trans h2, h1'.trans h2'⟩

theorem KLe.total (a b : ℝ × ℕ) : KLe a b ∨ KLe b a := by
  unfold KLe
  rcases lt_trichotomy a.1 b.1 with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases le_total a.2 b.2 with h' | h'
    · exact Or.inl (Or.inr ⟨h, h'⟩)
    · exact Or.inr (Or.inr ⟨h.symm, h'⟩)
  · exact Or.inr (Or.inl h)

theorem KLt.of_le_ne {a b : ℝ × ℕ} (h : KLe a b) (hne : a ≠ b) : KLt a b := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · refine Or.inr ⟨h1, lt_of_le_of_ne h2 fun h' => hne (Prod.ext h1 h')⟩

theorem KLt.ne {a b : ℝ × ℕ} (h : KLt a b) : a ≠ b := by
  rintro rfl
  rcases h with h | ⟨-, h⟩ <;> exact lt_irrefl _ h


theorem KLt.fst_le {a b : ℝ × ℕ} (h : KLt a b) : a.1 ≤ b.1 := by
  rcases h with h | ⟨h1, -⟩
  · exact h.le
  · exact h1.le

/-! ## The dedupe pass -/

variable {α : Type*} (key : α → ℝ × ℕ)

/-- **The invariant of the dedupe pass** over the sorted list `L` after `i` items: the kept list
`O` consists of items of `L`, has strictly increasing keys, covers the keys of the first `i`
items, and (for `i > 0`) its last key is that of item `i - 1`. -/
structure DInv (L : List α) (i : ℕ) (O : List α) : Prop where
  sub : ∀ y ∈ O, y ∈ L
  inc : O.Pairwise (fun x y => KLt (key x) (key y))
  cov : ∀ j, j < i → ∀ x, L[j]? = some x → ∃ y ∈ O, key y = key x
  last : ∀ x, 0 < i → L[i - 1]? = some x → ∃ y, O.getLast? = some y ∧ key y = key x
  nil : i = 0 → O = []

variable {key}

theorem DInv.start (L : List α) : DInv key L 0 [] :=
  ⟨fun _ h => by simp at h, List.Pairwise.nil, fun _ h => absurd h (Nat.not_lt_zero _),
    fun _ h => absurd h (lt_irrefl 0), fun _ => rfl⟩

/-- **A step of the dedupe pass**: item `i` is kept iff it is the first or its key differs from
that of item `i - 1`. -/
theorem DInv.step {L : List α} (hs : L.Pairwise (fun x y => KLe (key x) (key y))) {i : ℕ}
    {O : List α} (h : DInv key L i O) {x : α} (hx : L[i]? = some x) :
    ((i = 0 ∨ ∀ x', L[i - 1]? = some x' → key x' ≠ key x) → DInv key L (i + 1) (O ++ [x])) ∧
      ((0 < i ∧ ∀ x', L[i - 1]? = some x' → key x' = key x) → DInv key L (i + 1) O) := by
  have hi : i < L.length := by
    by_contra h'; push Not at h'; rw [List.getElem?_eq_none h'] at hx; cases hx
  have hxL : x ∈ L := List.mem_of_getElem? hx
  constructor
  · intro hcase
    -- the last kept key is below the key of `x`
    have hlast : ∀ y ∈ O, KLt (key y) (key x) := by
      intro y hy
      rcases Nat.eq_zero_or_pos i with h0 | hpos
      · rw [h.nil h0] at hy; cases hy
      · obtain ⟨x', hx'⟩ : ∃ x', L[i - 1]? = some x' :=
          ⟨L[i - 1], List.getElem?_eq_getElem (by omega)⟩
        obtain ⟨yl, hyl, hkl⟩ := h.last x' hpos hx'
        have hne : key x' ≠ key x := by
          rcases hcase with h0 | hc
          · omega
          · exact hc x' hx'
        -- `key x' ≤ key x` by sortedness
        have hle : KLe (key x') (key x) := by
          have := List.pairwise_iff_getElem.1 hs (i - 1) i (by omega) hi (by omega)
          rw [List.getElem?_eq_getElem (by omega)] at hx'
          rw [List.getElem?_eq_getElem hi] at hx
          simp only [Option.some.injEq] at hx hx'
          rwa [hx, hx'] at this
        have hlt : KLt (key x') (key x) := KLt.of_le_ne hle hne
        -- every kept key is at most the last one
        rcases List.getLast?_eq_some_iff.1 hyl with ⟨O', rfl⟩
        rcases List.mem_append.1 hy with hy | hy
        · have := List.pairwise_append.1 h.inc
          have h2 := this.2.2 y hy yl (by simp)
          rw [hkl] at h2
          rcases h2 with h2 | ⟨h2, h2'⟩ <;> rcases hlt with h3 | ⟨h3, h3'⟩
          · exact Or.inl (h2.trans h3)
          · exact Or.inl (by rwa [← h3])
          · exact Or.inl (by rwa [h2])
          · exact Or.inr ⟨h2.trans h3, h2'.trans h3'⟩
        · simp at hy; rwa [hy, hkl]
    refine ⟨fun y hy => ?_, ?_, fun j hj x'' hx'' => ?_, fun x'' _ hx'' => ?_, fun h' => by omega⟩
    · rcases List.mem_append.1 hy with hy | hy
      · exact h.sub y hy
      · simp at hy; rwa [hy]
    · rw [List.pairwise_append]
      exact ⟨h.inc, List.pairwise_singleton _ _, fun a ha b hb => by
        simp at hb; rw [hb]; exact hlast a ha⟩
    · rcases (show j < i ∨ j = i by omega) with hj | rfl
      · obtain ⟨y, hy, hk⟩ := h.cov j hj x'' hx''
        exact ⟨y, List.mem_append_left _ hy, hk⟩
      · rw [hx] at hx''; cases hx''
        exact ⟨x, by simp, rfl⟩
    · simp only [Nat.add_sub_cancel] at hx''
      rw [hx] at hx''; cases hx''
      exact ⟨x, by simp, rfl⟩
  · rintro ⟨hpos, heq⟩
    obtain ⟨x', hx'⟩ : ∃ x', L[i - 1]? = some x' :=
      ⟨L[i - 1], List.getElem?_eq_getElem (by omega)⟩
    refine ⟨h.sub, h.inc, fun j hj x'' hx'' => ?_, fun x'' _ hx'' => ?_, fun h' => by omega⟩
    · rcases (show j < i ∨ j = i by omega) with hj | rfl
      · exact h.cov j hj x'' hx''
      · rw [hx] at hx''; cases hx''
        obtain ⟨y, hy, hk⟩ := h.cov (j - 1) (by omega) x' hx'
        exact ⟨y, hy, by rw [hk, heq x' hx']⟩
    · simp only [Nat.add_sub_cancel] at hx''
      rw [hx] at hx''; cases hx''
      obtain ⟨y, hy, hk⟩ := h.last x' hpos hx'
      exact ⟨y, hy, by rw [hk, heq x' hx']⟩

/-! ## Raw stop records -/

section Raw

variable (P : Polygon) (J : Merge.Junction) (N : NF)

/-- The key of a raw record `(e, h, kind, k, b)` with leaving direction code `d`. -/
noncomputable def rKey (r : ℕ × ℕ × ℕ × ℕ × ℕ) (d : ℕ) : ℝ × ℕ := (offK P J r.1 r.2.1, d)

/-- The parameter of the position of a record. -/
noncomputable abbrev rPar (r : ℕ × ℕ × ℕ × ℕ × ℕ) : ℝ :=
  (chainModel J.whole).param (Qof P) ⟨r.1, r.2.1⟩

/-- The chord of a record. -/
noncomputable abbrev rSet (r : ℕ × ℕ × ℕ × ℕ × ℕ) : Set Point :=
  stopSet J (Qof P) N r.2.2.1 r.2.2.2.1 r.2.2.2.2

/-- **A valid raw record**: admissible codes with a free direction, the chord attached at the
position on the `C₁` part, which is its left end (`d = 1`) or its right end (`d = 0`). -/
def RawOK (r : ℕ × ℕ × ℕ × ℕ × ℕ) (d : ℕ) : Prop :=
  StOK P J N r.2.2.1 r.2.2.2.1 r.2.2.2.2 ∧
    FreeAt J.whole (stOrig J (Qof P) N r.2.2.1 r.2.2.2.1 r.2.2.2.2) (dirOf r.2.2.2.2) ∧
    SideAttach (chainModel J.whole).W (rSet P J N r) r.1 (rPar P J r) ∧
    (Lst J : ℝ) ≤ oW J (r.1 + rPar P J r) ∧ d ≤ 1 ∧
    sidePt (chainModel J.whole).W r.1 (rPar P J r) =
      (if d = 1 then Merge.lend (rSet P J N r) else Merge.rend (rSet P J N r))

end Raw

theorem offK_eq (P : Polygon) (J : Merge.Junction) (e h : ℕ) :
    offK P J e h = oW J (e + (chainModel J.whole).param (Qof P) ⟨e, h⟩) := rfl

variable {P : Polygon} {J : Merge.Junction} {N : NF}

/-- Two valid raw records with the same key have the same position and chord. -/
theorem raw_eq_of_key (hP : J.P.Simple) (hN : IsNF (chainModel J.right) (Qof P) N)
    {r r' : ℕ × ℕ × ℕ × ℕ × ℕ} {d d' : ℕ} (h : RawOK P J N r d) (h' : RawOK P J N r' d')
    (hk : rKey P J r d = rKey P J r' d') :
    r.1 = r'.1 ∧ rPar P J r = rPar P J r' ∧ rSet P J N r = rSet P J N r' := by
  have hS₂ := hN.1
  obtain ⟨hok, hf, hA, -, hd, hend⟩ := h
  obtain ⟨hok', hf', hA', -, hd', hend'⟩ := h'
  unfold rKey at hk
  obtain ⟨h1, h2⟩ := Prod.ext_iff.1 hk
  simp only at h1 h2
  rw [offK_eq, offK_eq] at h1
  obtain ⟨he, ht⟩ := pos_eq_of_oW hP hS₂.2.1 hS₂.1 hA.1 hA'.1 hA.2.1 hA.2.2.1 hA'.2.1
    hA'.2.2.1 h1
  refine ⟨he, ht, ?_⟩
  have hm := (stop_mem hP hN hok hf).1
  have hm' := (stop_mem hP hN hok' hf').1
  have ha : rSet P J N r ∈ Merge.augChords J.whole := F₂plus_subset J hS₂.2.1 hm
  have ha' : rSet P J N r' ∈ Merge.augChords J.whole := F₂plus_subset J hS₂.2.1 hm'
  have hpt : sidePt (chainModel J.whole).W r.1 (rPar P J r) =
      sidePt (chainModel J.whole).W r'.1 (rPar P J r') := by rw [he, ht]
  rw [hend, hend', h2] at hpt
  split_ifs at hpt
  · exact aug_eq_of_lend ha ha' hpt
  · exact aug_eq_of_rend ha ha' hpt

/-- The leaving direction code is determined by the position and the chord. -/
theorem raw_dc_eq (hP : J.P.Simple) (hN : IsNF (chainModel J.right) (Qof P) N)
    {r r' : ℕ × ℕ × ℕ × ℕ × ℕ} {d d' : ℕ} (h : RawOK P J N r d) (h' : RawOK P J N r' d')
    (he : r.1 = r'.1) (ht : rPar P J r = rPar P J r') (hs : rSet P J N r = rSet P J N r') :
    rKey P J r d = rKey P J r' d' := by
  have hS₂ := hN.1
  obtain ⟨hok, hf, -, -, hd, hend⟩ := h
  obtain ⟨-, -, -, -, hd', hend'⟩ := h'
  have hm := (stop_mem hP hN hok hf).1
  have ha := F₂plus_subset J hS₂.2.1 hm
  have hpt : sidePt (chainModel J.whole).W r.1 (rPar P J r) =
      sidePt (chainModel J.whole).W r'.1 (rPar P J r') := by rw [he, ht]
  rw [hend, hend', ← hs] at hpt
  have hne := lend_ne_rend ha
  have hdd : d = d' := by
    split_ifs at hpt with h1 h2 h2
    · omega
    · exact absurd hpt hne
    · exact absurd hpt.symm hne
    · omega
  unfold rKey
  rw [offK_eq, offK_eq, hdd]
  show ((oW J (r.1 + rPar P J r)), d') = (oW J (r'.1 + rPar P J r'), d')
  rw [he, ht]

/-- **The stop list from the deduped raw records** (a list `O` of raw items with strictly
increasing keys covering the keys of all raw items). -/
theorem stopsOK_of' {α : Type*} (hP : J.P.Simple) (hN : IsNF (chainModel J.right) (Qof P) N)
    {RS O : List α} {rec : α → ℕ × ℕ × ℕ × ℕ × ℕ} {dc : α → ℕ}
    (hok : ∀ x ∈ RS, RawOK P J N (rec x) (dc x))
    (hcomp : ∀ e ∈ F₂plus J (N.F (chainModel J.right) (Qof P)),
      StopChord2 J (N.F (chainModel J.right) (Qof P)) e → ∀ (p : ℕ) (t : ℝ),
      SideAttach (chainModel J.whole).W e p t → (Lst J : ℝ) ≤ oW J (p + t) →
      ∃ x ∈ RS, (rec x).1 = p ∧ rPar P J (rec x) = t ∧ rSet P J N (rec x) = e)
    (hsub : ∀ y ∈ O, y ∈ RS)
    (hinc : O.Pairwise (fun x y => KLt (rKey P J (rec x) (dc x)) (rKey P J (rec y) (dc y))))
    (hcov : ∀ x ∈ RS, ∃ y ∈ O, rKey P J (rec y) (dc y) = rKey P J (rec x) (dc x)) :
    StopsOK J (N.F (chainModel J.right) (Qof P)) (stopsOf J (Qof P) N (O.map rec)) := by
  have hO : ∀ y ∈ O, RawOK P J N (rec y) (dc y) := fun y hy => hok y (hsub y hy)
  have hst : stopsOf J (Qof P) N (O.map rec) =
      O.map (fun y => ((rec y).1, rPar P J (rec y), rSet P J N (rec y))) := by
    unfold stopsOf; rw [List.map_map]; rfl
  rw [hst]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hs
    obtain ⟨hk, hf, hA, hL, -, -⟩ := hO y hy
    obtain ⟨hm, hsc⟩ := stop_mem hP hN hk hf
    exact ⟨hm, hsc, hA, hL⟩
  · intro e he hsc p t hA hL
    obtain ⟨x, hx, h1, h2, h3⟩ := hcomp e he hsc p t hA hL
    obtain ⟨y, hy, hky⟩ := hcov x hx
    obtain ⟨e1, e2, e3⟩ := raw_eq_of_key hP hN (hO y hy) (hok x hx) hky
    refine List.mem_map.2 ⟨y, hy, ?_⟩
    rw [e1, e2, e3, h1, h2, h3]
  · rw [List.pairwise_map]
    exact hinc.imp fun {a b} h => by
      have := KLt.fst_le h
      simp only [rKey, offK_eq] at this
      exact this
  · rw [List.Nodup, List.pairwise_map]
    refine List.Pairwise.imp_of_mem (fun {a b} ha hb h heq => ?_) hinc
    obtain ⟨h1, h2⟩ := Prod.ext_iff.1 heq
    obtain ⟨h2, h3⟩ := Prod.ext_iff.1 h2
    exact KLt.ne h (raw_dc_eq hP hN (hO a ha) (hO b hb) h1 h2 h3)

end SweepStop

end

end Chazelle.Core
