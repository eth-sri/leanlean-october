module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.NFBuildOut
public import Chazelle.Core.NFBuildPassMath

/-!
# WP-C (BuildNF), RAM part 19: the layout of `buildNF` from the tables

`nfAt_of_tables`: a memory holding the header, the chord table, the arc table, the region table,
the list table and the sequence table written by the machine (for `K > 0`) holds the normal form
`buildNF M Q L E` (`NFAt`).  Also the bounds of the region indices (`topR_le`, …) and the size of
the list table (`offF_le`).
-/

namespace Chazelle.Core

namespace BuildNF

@[expose] public section

open List
open BuildRam (lstF cntF wmaxF lst2F cnt2F offF rtv hdrW)

variable {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {E : List ℕ}

/-! ## Region indices are at most `K` -/

theorem mem_foldl_step {st u : List ℕ} {x : ℕ} (h : x ∈ u.foldl BuildStack.step st) :
    x ∈ st ∨ x ∈ u := by
  induction u generalizing st with
  | nil => simp_all
  | cons y u ih =>
    rcases ih h with h' | h'
    · unfold BuildStack.step at h'
      split_ifs at h' with hy
      · rcases st with _ | ⟨z, st⟩
        all_goals simp_all
      grind
    simp_all

theorem ridx_label_le {w : List ℕ} {K : ℕ} (hw : ∀ x ∈ w, x < K) (m : ℕ) :
    ridx (BuildStack.label w m) ≤ K := by
  unfold BuildStack.label
  rcases hh : (BuildStack.run (w.take m)).head? with _ | x
  · simp [ridx]
  · simp only [ridx]
    have hx := mem_of_mem_head? hh
    unfold BuildStack.run at hx
    rcases mem_foldl_step hx with h' | h'
    all_goals grind

section
variable (h : Input M Q L E)
include h
theorem cw_lt : ∀ x ∈ cw E, x < L.length := by
  intro x hx
  unfold cw at hx
  obtain ⟨c, hc, rfl⟩ := mem_map.1 hx
  have := mem_range.1 (h.perm.mem_iff.1 hc)
  omega

theorem topR_le (m : ℕ) : topR E m ≤ L.length :=
  ridx_label_le (cw_lt h) m

theorem chordRec_up_le {i : ℕ} (hi : i < L.length) :
    (chordRec M Q L E i).up ≤ L.length ∧ (chordRec M Q L E i).dn ≤ L.length := by
  unfold chordRec outside
  rw [word_eq]
  have := ridx_label_le (w := E.map (· / 2)) (cw_lt h)
    ((evs M Q L E).idxOf (BuildRegions.e1 M Q L i))
  ram_grind

/-- Every chord occurs in the word. -/
theorem mem_cw {x : ℕ} (hx : x < L.length) : x ∈ cw E := by
  unfold cw
  exact mem_map.2 ⟨2 * x, h.perm.mem_iff.2 (mem_range.2 (by omega)), by omega⟩

/-! ## The machine functions -/


end

section
variable (M : Model) (Q : Polygon) (L : List (ℕ × ℕ × ℕ)) (E : List ℕ)
include M Q L E
/-- The region of arc `j`. -/
noncomputable def keyA (j : ℕ) : ℕ :=
  (arcRec M Q L E ((gapStarts M Q L E).getD j 0)).reg

/-- The weight of arc `j`. -/
noncomputable def wA (j : ℕ) : ℕ :=
  arcW M Q (arcRec M Q L E ((gapStarts M Q L E).getD j 0))

/-- The region above chord `i`. -/
noncomputable def upC (i : ℕ) : ℕ :=
  (chordRec M Q L E i).up

/-- The region below chord `i`. -/
noncomputable def dnC (i : ℕ) : ℕ :=
  (chordRec M Q L E i).dn


end

section
variable (hK : L.length ≠ 0)
include hK
theorem arcList_pos :
    arcList M Q L E = (gapStarts M Q L E).map (arcRec M Q L E) := by
  grind [arcList]

theorem arcList_getD {j : ℕ} (hj : j < (gapStarts M Q L E).length) :
    (arcList M Q L E).getD j ⟨0, ⟨0, 0⟩, ⟨0, 0⟩⟩ = arcRec M Q L E ((gapStarts M Q L E).getD j 0) := by
  rw [arcList_pos hK, getD_eq_getElem?_getD, getElem?_map, getElem?_eq_getElem hj,
    Option.map_some, Option.getD_some, getD_eq_getElem?_getD, getElem?_eq_getElem hj,
    Option.getD_some]

theorem regArcs_eq (r : ℕ) :
    regArcs M Q L E r = lstF (keyA M Q L E) (gapStarts M Q L E).length r := by
  unfold regArcs lstF
  rw [arcList_pos hK, length_map]
  apply filter_congr
  intro j hj
  rw [← arcList_pos hK, arcList_getD hK (mem_range.1 hj)]
  rfl


end

theorem regChords_eq (r : ℕ) :
    regChords M Q L E r = lst2F (upC M Q L E) (dnC M Q L E) L.length r := rfl

theorem regWt_eq (hK : L.length ≠ 0) (r : ℕ) :
    regWt M Q L E r = wmaxF (keyA M Q L E) (wA M Q L E) (gapStarts M Q L E).length r := by
  unfold regWt wmaxF
  rw [← regArcs_eq hK]
  congr 1
  apply map_congr_left
  intro j hj
  have hj' : j < (gapStarts M Q L E).length := by
    unfold regArcs at hj
    rw [arcList_pos hK, length_map] at hj
    simp_all
  rw [arcList_getD hK hj']
  rfl

/-! ## The layout -/

/-- **The normal form from the tables** (`K > 0`). -/
theorem nfAt_of_tables (h : Input M Q L E) (hK : L.length ≠ 0) {m : ℕ → ℕ}
    {H CT AT RT QT LT : ℕ}
    (hH : ∀ f, f < 12 → m (H + f) = hdrW L.length (gapStarts M Q L E).length (L.length + 1)
      CT AT RT QT LT H f)
    (hC : ∀ i, i < L.length → ∀ f, f < 5 → m (CT + 5 * i + f) = cf (chordRec M Q L E i) f)
    (hA : ∀ j, j < (gapStarts M Q L E).length → ∀ f, f < 5 →
      m (AT + 5 * j + f) = af (arcRec M Q L E ((gapStarts M Q L E).getD j 0)) f)
    (hR : ∀ r, r < L.length + 1 → ∀ f, f < 5 → m (RT + 5 * r + f) =
      rtv (cntF (keyA M Q L E) (gapStarts M Q L E).length)
        (cnt2F (upC M Q L E) (dnC M Q L E) L.length)
        (wmaxF (keyA M Q L E) (wA M Q L E) (gapStarts M Q L E).length) (5 * r + f))
    (hLa : ∀ r, r < L.length + 1 → ∀ t, t < cntF (keyA M Q L E) (gapStarts M Q L E).length r →
      m (LT + offF (cntF (keyA M Q L E) (gapStarts M Q L E).length)
        (cnt2F (upC M Q L E) (dnC M Q L E) L.length) r + t) =
        (lstF (keyA M Q L E) (gapStarts M Q L E).length r).getD t 0)
    (hLc : ∀ r, r < L.length + 1 → ∀ t, t < cnt2F (upC M Q L E) (dnC M Q L E) L.length r →
      m (LT + (offF (cntF (keyA M Q L E) (gapStarts M Q L E).length)
        (cnt2F (upC M Q L E) (dnC M Q L E) L.length) r +
          cntF (keyA M Q L E) (gapStarts M Q L E).length r) + t) =
        (lst2F (upC M Q L E) (dnC M Q L E) L.length r).getD t 0)
    (hQ : ∀ j, j < (gapStarts M Q L E).length → m (QT + j) = j) :
    NFAt m H (buildNF M Q L E) := by
  have hlenA : (buildNF M Q L E).arcs.length = (gapStarts M Q L E).length := by
    show (arcList M Q L E).length = _
    rw [arcList_pos hK, length_map]
  have h0 := hH 0 (by norm_num); have h1 := hH 1 (by norm_num); have h2 := hH 2 (by norm_num)
  have h3 := hH 3 (by norm_num); have h4 := hH 4 (by norm_num); have h5 := hH 5 (by norm_num)
  have h6 := hH 6 (by norm_num); have h7 := hH 7 (by norm_num); have h9 := hH 9 (by norm_num)
  have h11 := hH 11 (by norm_num)
  simp only [hdrW, Nat.add_zero] at h0 h1 h2 h3 h4 h5 h6 h7 h9 h11
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h9 h11
  refine ⟨?_, ?_, ?_, ?_, ?_, fun i hi => ?_, fun j hj => ?_, fun r hr => ?_, fun j hj => ?_,
    fun k hk => ?_, fun r hr => ?_⟩
  · grind [buildNF]
  · omega
  · grind [buildNF]
  · rw [h9]; rfl
  · rw [h11]; rfl
  · -- chords
    have hi' : i < L.length := by grind [buildNF]
    rw [h3, Input.chord_eq hi']
    have c0 := hC i hi' 0 (by norm_num); have c1 := hC i hi' 1 (by norm_num)
    have c2 := hC i hi' 2 (by norm_num); have c3 := hC i hi' 3 (by norm_num)
    have c4 := hC i hi' 4 (by norm_num)
    simp only [cf, Nat.add_zero] at c0 c1 c2 c3 c4
    ram_grind
  · -- arcs
    rw [hlenA] at hj
    have ha : (buildNF M Q L E).arc j = arcRec M Q L E ((gapStarts M Q L E).getD j 0) := by
      unfold NF.arc; exact arcList_getD hK hj
    rw [h4, ha]
    have c0 := hA j hj 0 (by norm_num); have c1 := hA j hj 1 (by norm_num)
    have c2 := hA j hj 2 (by norm_num); have c3 := hA j hj 3 (by norm_num)
    have c4 := hA j hj 4 (by norm_num)
    simp only [af, Nat.add_zero] at c0 c1 c2 c3 c4
    ram_grind
  · -- regions
    have hr' : r < L.length + 1 := by grind [buildNF]
    rw [h5, h.region_eq hr']
    simp only
    have c0 := hR r hr' 0 (by norm_num); have c1 := hR r hr' 1 (by norm_num)
    have c2 := hR r hr' 2 (by norm_num); have c3 := hR r hr' 3 (by norm_num)
    have c4 := hR r hr' 4 (by norm_num)
    rw [BuildRam.rtv_eq _ _ _ _ _ (by norm_num)] at c0 c1 c2 c3 c4
    norm_num at c0 c1 c2 c3 c4
    refine ⟨?_, ?_, ?_, fun t ht => ?_, fun t ht => ?_⟩
    · rw [c0, regArcs_eq hK]; rfl
    · rw [c2, regChords_eq]; rfl
    · rw [c4, regWt_eq hK]
    · rw [h7, c1]
      rw [regArcs_eq hK] at ht ⊢
      exact hLa r hr' t ht
    · rw [h7, c3]
      rw [regChords_eq] at ht ⊢
      exact hLc r hr' t ht
  · -- seq
    have hj' : j < (gapStarts M Q L E).length := by
      have : (buildNF M Q L E).seq = range (arcList M Q L E).length := rfl
      rw [this, length_range, arcList_pos hK, length_map] at hj; exact hj
    rw [h6, hQ j hj']
    show j = (range (arcList M Q L E).length).getD j 0
    rw [getD_eq_getElem?_getD, getElem?_range (by rw [arcList_pos hK, length_map]; exact hj'),
      Option.getD_some]
  all_goals (grind [buildNF])

end

end BuildNF

end Chazelle.Core
