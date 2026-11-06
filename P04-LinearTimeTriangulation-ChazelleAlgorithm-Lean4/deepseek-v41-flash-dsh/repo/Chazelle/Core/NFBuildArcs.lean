module

public import Chazelle.Golf

public import Chazelle.Core.NFBuildRegions

/-!
# WP-C (BuildNF): the arcs of a submap are the gaps of the sorted events

With the sorted attachment events `S` of a valid chord list (`BuildRegions.Ctx`), `kap S m` is the
key of the `m`-th event.  A **gap** is a pair of consecutive distinct keys `kap S m < kap S (m + 1)`,
or the wrapping pair `(kap S (|S| - 1), kap S 0)`.

## Results

* `Ctx.isCut_iff`: the cut keys of the family are exactly the event keys;
* `Ctx.arc_of_gap`, `Ctx.arc_of_wrap`: every gap is an arc of the region of its label
  (`label w (m + 1)`, resp. the root);
* `Ctx.gap_of_arc`: every arc of every region is a gap;
* `Ctx.arc_of_empty`, `Ctx.gap_of_arc_empty`: without chords, the only arc is the pinned `(0, 0)`
  of the root region.
-/

namespace Chazelle.Core

namespace BuildSort

@[expose] public section

open List

/-- The key of the `m`-th event. -/
noncomputable def kap (S : List Ev) (m : ℕ) : ℝ := (S.getD m (0, 0, 0)).2.1

theorem kap_eq {S : List Ev} {m : ℕ} (hm : m < S.length) : kap S m = (S[m]).2.1 := by
  unfold kap; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some]

/-- Every event is at some index. -/
theorem index_of_mem {S : List Ev} {e : Ev} (he : e ∈ S) : ∃ k < S.length, kap S k = e.2.1 := by
  obtain ⟨k, hk, rfl⟩ := mem_iff_getElem.1 he
  exact ⟨k, hk, kap_eq hk⟩

/-- The key at an index is an event key. -/
theorem kap_mem {S : List Ev} {m : ℕ} (hm : m < S.length) : ∃ e ∈ S, e.2.1 = kap S m :=
  ⟨S[m], getElem_mem hm, (kap_eq hm).symm⟩

/-- **Keys are sorted along the list.** -/
theorem kap_mono {n : ℝ} {S : List Ev} (hs : S.Pairwise (EvLe n)) {i j : ℕ} (hij : i ≤ j)
    (hj : j < S.length) : kap S i ≤ kap S j := by
  rcases hij.lt_or_eq with h | rfl
  · Ξ kap_eq (h.trans hj), kap_eq hj
    exact key_le_of_evLe (pairwise_iff_getElem.1 hs i j (h.trans hj) hj h)
  · exact le_rfl

/-- The events up to index `m` have keys at most `kap S m`, those after at least `kap S (m+1)`. -/
theorem key_le_or_ge {n : ℝ} {S : List Ev} (hs : S.Pairwise (EvLe n)) {m : ℕ}
    (hm : m + 1 < S.length) {e : Ev} (he : e ∈ S) : e.2.1 ≤ kap S m ∨ kap S (m + 1) ≤ e.2.1 := by
  obtain ⟨k, hk, hke⟩ := index_of_mem he
  Ξ ← hke
  rcases Nat.lt_or_ge m k with h | h
  · exact Or.inr (kap_mono hs h hk)
  · exact Or.inl (kap_mono hs h (⋄))

/-- **The number of events below a key inside a gap.** -/
theorem cntBelow_gap {n : ℝ} {S : List Ev} (hs : S.Pairwise (EvLe n)) {m : ℕ}
    (hm : m + 1 < S.length) {y : ℝ} (h1 : kap S m < y) (h2 : y < kap S (m + 1)) :
    cntBelow S y = m + 1 := by
  unfold cntBelow
  rw [← take_append_drop (m + 1) S, countP_append]
  have ht : (S.take (m + 1)).countP (fun e => decide (e.2.1 < y)) = m + 1 := by
    rw [countP_eq_length.2, length_take, min_eq_left (by omega)]
    intro a ha
    obtain ⟨j, hj, rfl⟩ := mem_take_iff_getElem.1 ha
    have := kap_mono hs (show j ≤ m by omega) (by omega)
    rw [kap_eq (by omega : j < S.length)] at this
    simp only [decide_eq_true_eq]; linarith
  have hd : (S.drop (m + 1)).countP (fun e => decide (e.2.1 < y)) = 0 := by
    rw [countP_eq_zero]
    intro a ha
    obtain ⟨j, hj, rfl⟩ := mem_drop_iff_getElem.1 ha
    have hj' : m + 1 + j < S.length := by omega
    have := kap_mono hs (show m + 1 ≤ m + 1 + j by omega) hj'
    rw [kap_eq hj'] at this
    simp only [decide_eq_true_eq, not_lt]; linarith
  rw [ht, hd, add_zero]

/-- No event below the first key. -/
theorem cntBelow_first {n : ℝ} {S : List Ev} (hs : S.Pairwise (EvLe n))
    {y : ℝ} (hy : y < kap S 0) : cntBelow S y = 0 := by
  unfold cntBelow
  Ξ countP_eq_zero
  intro a ha
  obtain ⟨k, hk, hka⟩ := index_of_mem ha
  have := kap_mono hs (Nat.zero_le k) hk
  simp only [decide_eq_true_eq, not_lt]; linarith

/-- Every event below a key above the last key. -/
theorem cntBelow_last {n : ℝ} {S : List Ev} (hs : S.Pairwise (EvLe n)) (hS : 0 < S.length)
    {y : ℝ} (hy : kap S (S.length - 1) < y) : cntBelow S y = S.length := by
  unfold cntBelow
  rw [countP_eq_length]
  intro a ha
  obtain ⟨k, hk, hka⟩ := index_of_mem ha
  have := kap_mono hs (show k ≤ S.length - 1 by omega) (by omega)
  simp only [decide_eq_true_eq]; linarith

end

end BuildSort

namespace BuildRegions

@[expose] public section

open Set List
open Chazelle.Chain (SideAttach sideInArc sidePt sideKey_inj TouchesIn)
open BuildSort (Ev EvLe cycDist cntBelow kap)
open BuildOrder (events evPair chordSet mem_events event_data getD_mem chordSet_inj chordSet_mem)

variable {M : Model} {Q : Polygon} {L : List (ℕ × ℕ × ℕ)} {S : List Ev}

namespace Ctx

variable (h : Ctx M Q L S)
include h

/-- **The cut keys are the event keys.** -/
theorem isCut_iff {k : ℝ} : M.IsCut (famOf M Q L) k ↔ ∃ e ∈ S, e.2.1 = k := by
  constructor
  · rintro ⟨c, hc, p, t, hA, rfl⟩
    obtain ⟨j, hj, rfl⟩ := h.fam_cases hc
    have hL := h.attL hj
    have hR := h.attR hj
    obtain ⟨e, -, -, -, -, -, hoth⟩ := h.walk.attach_other_end (h.adm (chordSet_mem hj)) hL
    have hRe := hoth _ _ hR (Ne.symm (h.pts_ne hj))
    by_cases hpt : sidePt M.W p t = sidePt M.W (crec L j).lp (M.param Q (crec L j).lpos)
    · obtain ⟨rfl, rfl⟩ := h.walk.attach_unique (h.adm (chordSet_mem hj)) hA hL hpt
      exact ⟨_, h.eL_mem hj, rfl⟩
    · have hpt' : sidePt M.W p t = sidePt M.W (crec L j).rp (M.param Q (crec L j).rpos) := by
        Ξ hoth _ _ hA hpt, hRe
      obtain ⟨rfl, rfl⟩ := h.walk.attach_unique (h.adm (chordSet_mem hj)) hA hR hpt'
      exact ⟨_, h.eR_mem hj, rfl⟩
  · rintro ⟨e, he, rfl⟩
    by_contra hc
    exact h.key_ne_of_not_cut hc e he rfl

/-- The keys of the events are in `[0, n)`. -/
theorem key_bounds_mem {e : Ev} (he : e ∈ S) : 0 ≤ e.2.1 ∧ e.2.1 < M.W.n := by
  obtain ⟨hi, hc⟩ := h.mem_cases he
  rcases hc with hc | hc <;> rw [hc]
  · exact h.kl_bounds hi
  · exact h.kr_bounds hi

theorem kap_bounds {m : ℕ} (hm : m < S.length) : 0 ≤ kap S m ∧ kap S m < M.W.n := by
  obtain ⟨e, he, hk⟩ := BuildSort.kap_mem hm
  rw [← hk]; exact h.key_bounds_mem he

theorem kap_cut {m : ℕ} (hm : m < S.length) : M.IsCut (famOf M Q L) (kap S m) :=
  h.isCut_iff.2 (BuildSort.kap_mem hm)

theorem length_S : S.length = 2 * L.length := by
  Ξ h.perm.length_eq
  unfold events
  Ξ length_flatMap
  have : ∀ i ∈ List.range L.length, (evPair M Q L i).length = 2 := fun i _ => rfl
  Ξ List.map_congr_left this, map_const', length_range, sum_replicate, smul_eq_mul, mul_comm

/-- **A gap is an arc** of the region of its label. -/
theorem arc_of_gap {m : ℕ} (hm : m + 1 < S.length) (hlt : kap S m < kap S (m + 1)) :
    M.IsArc (famOf M Q L) (reg M Q L S (BuildStack.label (S.map Prod.fst) (m + 1)))
      (kap S m) (kap S (m + 1)) := by
  have ha := h.kap_bounds (m := m) (⋄)
  have hb := h.kap_bounds hm
  have hin : ∀ x, sideInArc (kap S m) (kap S (m + 1)) x ↔ kap S m < x ∧ x < kap S (m + 1) := by
    intro x; unfold sideInArc; rw [ite_eq_left hlt]
  have hnocut : ∀ x, sideInArc (kap S m) (kap S (m + 1)) x → ¬ M.IsCut (famOf M Q L) x := by
    intro x hx hcut
    rw [hin] at hx
    obtain ⟨e, he, rfl⟩ := h.isCut_iff.1 hcut
    rcases BuildSort.key_le_or_ge h.sorted hm he with h1 | h1 <;> linarith [hx.1, hx.2]
  refine ⟨ha.1, ha.2, hb.1, hb.2, Or.inl ⟨h.kap_cut (⋄), h.kap_cut hm, hlt.ne⟩, hnocut,
    fun p t hp ht0 ht1 hx => ?_⟩
  have hcut := hnocut _ hx
  have hf := (h.faces_reg hp ⟨ht0, ht1⟩ hcut).2
  rw [hin] at hx
  unfold gapLabel at hf
  rwa [BuildSort.cntBelow_gap h.sorted hm hx.1 hx.2] at hf

/-- The label of the full word and of the empty prefix is the root. -/
theorem label_ends : BuildStack.label (S.map Prod.fst) 0 = none ∧
    BuildStack.label (S.map Prod.fst) S.length = none := by
  obtain ⟨hnc, htw⟩ := h.word
  refine ⟨rfl, ?_⟩
  unfold BuildStack.label
  Ξ ← length_map (f := Prod.fst), take_length, BuildStack.run_eq_nil htw hnc
  rfl

/-- **The wrapping gap is an arc of the root region.** -/
theorem arc_of_wrap (hK : 0 < L.length) :
    M.IsArc (famOf M Q L) (reg M Q L S none) (kap S (S.length - 1)) (kap S 0) := by
  have hlen := h.length_S
  have hS : 0 < S.length := by omega
  have ha := h.kap_bounds (m := S.length - 1) (by omega)
  have hb := h.kap_bounds hS
  -- the first key is below the last one
  have hlt : kap S 0 < kap S (S.length - 1) := by
    obtain ⟨k1, hk1, e1k⟩ := BuildSort.index_of_mem (h.e1_mem hK)
    obtain ⟨k2, hk2, e2k⟩ := BuildSort.index_of_mem (h.e2_mem hK)
    have := BuildSort.kap_mono h.sorted (Nat.zero_le k1) hk1
    have := BuildSort.kap_mono h.sorted (show k2 ≤ S.length - 1 by omega) (by omega)
    simp only [e1, e2] at e1k e2k
    linarith [h.lo_lt_hi hK]
  have hin : ∀ x, sideInArc (kap S (S.length - 1)) (kap S 0) x ↔
      kap S (S.length - 1) < x ∨ x < kap S 0 := by
    intro x; unfold sideInArc; rw [ite_eq_right (not_lt.2 hlt.le)]
  have hnocut : ∀ x, sideInArc (kap S (S.length - 1)) (kap S 0) x →
      ¬ M.IsCut (famOf M Q L) x := by
    intro x hx hcut
    rw [hin] at hx
    obtain ⟨e, he, rfl⟩ := h.isCut_iff.1 hcut
    obtain ⟨k, hk, hke⟩ := BuildSort.index_of_mem he
    have h1 := BuildSort.kap_mono h.sorted (Nat.zero_le k) hk
    have h2 := BuildSort.kap_mono h.sorted (show k ≤ S.length - 1 by omega) (by omega)
    rw [hke] at h1 h2
    rcases hx with hx | hx <;> linarith
  refine ⟨ha.1, ha.2, hb.1, hb.2, Or.inl ⟨h.kap_cut (by omega), h.kap_cut hS, hlt.ne'⟩, hnocut,
    fun p t hp ht0 ht1 hx => ?_⟩
  have hcut := hnocut _ hx
  have hf := (h.faces_reg hp ⟨ht0, ht1⟩ hcut).2
  rw [hin] at hx
  unfold gapLabel at hf
  rcases hx with hx | hx
  · rwa [BuildSort.cntBelow_last h.sorted hS hx, h.label_ends.2] at hf
  · rwa [BuildSort.cntBelow_first h.sorted hx, h.label_ends.1] at hf

/-- **Every arc is a gap** (with chords). -/
theorem gap_of_arc (hK : 0 < L.length) {U : Set Point} {a b : ℝ}
    (harc : M.IsArc (famOf M Q L) U a b) :
    (∃ m, m + 1 < S.length ∧ kap S m < kap S (m + 1) ∧ a = kap S m ∧ b = kap S (m + 1)) ∨
      (a = kap S (S.length - 1) ∧ b = kap S 0) := by
  classical
  have hne : (famOf M Q L) ≠ ∅ := Set.nonempty_iff_ne_empty.1 ⟨_, chordSet_mem hK⟩
  obtain ⟨-, -, -, -, hcuts, hfree, -⟩ := harc
  obtain ⟨hca, hcb, hab⟩ := hcuts.resolve_right fun h' => hne h'.1
  obtain ⟨ea, hea, hak⟩ := h.isCut_iff.1 hca
  obtain ⟨eb, heb, hbk⟩ := h.isCut_iff.1 hcb
  obtain ⟨k₁, hk₁, hk₁e⟩ := BuildSort.index_of_mem hea
  obtain ⟨k₂, hk₂, hk₂e⟩ := BuildSort.index_of_mem heb
  rw [hak] at hk₁e
  rw [hbk] at hk₂e
  have hlen : 0 < S.length := by omega
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · left
    have hin : ∀ x, sideInArc a b x ↔ a < x ∧ x < b := by
      intro x; unfold sideInArc; rw [ite_eq_left hlt]
    have hex : ∃ j, a < kap S j ∧ j < S.length := ⟨k₂, by rw [hk₂e]; exact hlt, hk₂⟩
    set j₀ := Nat.find hex with hj₀
    obtain ⟨hj₀a, hj₀l⟩ := Nat.find_spec hex
    have hmin : ∀ j < j₀, ¬ (a < kap S j ∧ j < S.length) := fun j hj => Nat.find_min hex hj
    have hj₀pos : j₀ ≠ 0 := by
      intro h0
      have := BuildSort.kap_mono h.sorted (Nat.zero_le k₁) hk₁
      rw [← h0, hk₁e] at *
      linarith
    have hk₁m : k₁ ≤ j₀ - 1 := by
      by_contra hc
      have := BuildSort.kap_mono h.sorted (show j₀ ≤ k₁ by omega) hk₁
      rw [hk₁e] at this; linarith
    have hm1 : kap S (j₀ - 1) ≤ a := by
      by_contra hc; push Not at hc
      exact hmin (j₀ - 1) (by omega) ⟨hc, by omega⟩
    have hm2 : a ≤ kap S (j₀ - 1) := by
      have := BuildSort.kap_mono h.sorted hk₁m (by omega)
      rwa [hk₁e] at this
    have hj₀k₂ : j₀ ≤ k₂ := Nat.find_min' hex ⟨by rw [hk₂e]; exact hlt, hk₂⟩
    have hb1 : kap S j₀ ≤ b := by
      have := BuildSort.kap_mono h.sorted hj₀k₂ hk₂; rwa [hk₂e] at this
    have hb2 : b ≤ kap S j₀ := by
      by_contra hc
      push Not at hc
      exact hfree _ ((hin _).2 ⟨hj₀a, hc⟩) (h.kap_cut hj₀l)
    refine ⟨j₀ - 1, by omega, ?_, by linarith, ?_⟩
    · rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hj₀pos)]; linarith
    · rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hj₀pos)]; linarith
  · right
    have hin : ∀ x, sideInArc a b x ↔ a < x ∨ x < b := by
      intro x; unfold sideInArc; rw [ite_eq_right (not_lt.2 hgt.le)]
    have h1 : kap S (S.length - 1) ≤ a := by
      by_contra hc; push Not at hc
      exact hfree _ ((hin _).2 (Or.inl hc)) (h.kap_cut (by omega))
    have h2 : a ≤ kap S (S.length - 1) := by
      have := BuildSort.kap_mono h.sorted (show k₁ ≤ S.length - 1 by omega) (by omega)
      rwa [hk₁e] at this
    have h3 : b ≤ kap S 0 := by
      by_contra hc; push Not at hc
      exact hfree _ ((hin _).2 (Or.inr hc)) (h.kap_cut hlen)
    have h4 : kap S 0 ≤ b := by
      have := BuildSort.kap_mono h.sorted (Nat.zero_le k₂) hk₂
      rwa [hk₂e] at this
    exact ⟨by linarith, by linarith⟩

/-- Without chords the family is empty. -/
theorem fam_empty (hK : L.length = 0) : famOf M Q L = ∅ := by
  have : L = [] := List.length_eq_zero_iff.1 hK
  subst this
  ext c; simp [famOf]

/-- **Without chords, the pinned arc `(0, 0)` is an arc of the root region.** -/
theorem arc_of_empty (hK : L.length = 0) :
    M.IsArc (famOf M Q L) (reg M Q L S none) 0 0 := by
  have hF := h.fam_empty hK
  have hS : S = [] := by
    Ξ List.eq_nil_iff_forall_not_mem
    intro e he
    have := (h.mem_cases he).1; omega
  have hnocut : ∀ x, ¬ M.IsCut (famOf M Q L) x := by
    rintro x ⟨c, hc, -⟩; rw [hF] at hc; exact hc
  -- the walk has an edge
  have hsys := h.walk.sys _ h.adm h.finite
  obtain ⟨-, hcard⟩ := hsys.regionsIn_finite_ncard h.walk.preconn h.walk.nonempty subset_rfl
  obtain ⟨U, hU⟩ : (M.regions (famOf M Q L)).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by
      change (Chazelle.Chain.regionsIn M.D (famOf M Q L)).ncard ≠ 0
      omega)
  obtain ⟨p, t, hp, -⟩ := h.walk.exists_faces_nc h.adm h.finite hU
  have hn : (0 : ℝ) < M.W.n := by exact_mod_cast (Nat.zero_lt_of_lt hp)
  refine ⟨le_rfl, hn, le_rfl, hn, Or.inr ⟨hF, rfl, rfl⟩, fun x _ => hnocut x,
    fun p t hp ht0 ht1 _ => ?_⟩
  have hf := (h.faces_reg hp ⟨ht0, ht1⟩ (hnocut _)).2
  have hlab : gapLabel S (p + t) = none := by unfold gapLabel; rw [hS]; rfl
  rwa [hlab] at hf

/-- **Without chords every arc is the pinned `(0, 0)`.** -/
theorem gap_of_arc_empty (hK : L.length = 0) {U : Set Point} {a b : ℝ}
    (harc : M.IsArc (famOf M Q L) U a b) : a = 0 ∧ b = 0 := by
  have hF := h.fam_empty hK
  obtain ⟨-, -, -, -, hcuts, -⟩ := harc
  rcases hcuts with ⟨⟨c, hc, -⟩, -⟩ | ⟨-, ha, hb⟩
  · rw [hF] at hc; exact absurd hc (Set.notMem_empty c)
  · exact ⟨ha, hb⟩


end Ctx

end

end BuildRegions

end Chazelle.Core
