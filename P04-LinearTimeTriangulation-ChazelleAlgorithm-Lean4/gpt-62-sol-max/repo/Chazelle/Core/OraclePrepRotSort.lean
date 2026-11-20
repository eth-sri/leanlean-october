module

public import Chazelle.Core.OraclePrepDarts

/-!
# Lemma 3.6 (WP-H), preprocessing part 21: sorting items by pairs of arrays

`sortCore`: with `Z1` in `60004`, `Z2` in `60005`, `n` in `60006`, the item array `0 … n - 1` is
built at the allocator and sorted by the lexicographic order of `(m (Z1 + i), m (Z2 + i))`; the
base of the sorted items is left in `60007` (`sortCore_exec`).
-/

namespace Chazelle.Core

namespace OracleR

open Machine Machine.Stmt Programs SignK WalkKey
open OracleQ

@[expose] public section

/-- **Build the items, sort them by the pairs of the two arrays.** -/
def sortCore : Stmt :=
  .seq itemS (.seq sortSet (.seq (SortR.sortStmt lexCmp) (.instr (.copyN 60007 30005))))

theorem sortCore_exec {P : Polygon} {W : ℕ} {c : Config} (hw : WordsBounded W c)
    {Z1 Z2 n A₀ : ℕ} (h4 : c.nreg 60004 = Z1) (h5 : c.nreg 60005 = Z2)
    (h6 : c.nreg 60006 = n) (h1 : c.nreg 120011 = 1) (hAl : c.nreg 9999 = A₀)
    (hZ1 : Z1 + n ≤ A₀) (hZ2 : Z2 + n ≤ A₀)
    (hroom : A₀ + n + SortR.sortCost 20 n ≤ W) :
    ∃ c' k, Exec P W sortCore c c' k ∧ k ≤ 7 * n + SortR.sortCost 20 n + 20 ∧
      FrameN dBands c c' ∧ A₀ + n ≤ c'.nreg ALLOC ∧
      c'.nreg ALLOC ≤ A₀ + n + SortR.sortCost 20 n ∧
      (∀ r, bandOf r = 6 → r ≠ 60007 → r ≠ 60016 → r ≠ 60017 → r ≠ 60020 →
        c'.nreg r = c.nreg r) ∧
      A₀ + n ≤ c'.nreg 60007 ∧ c'.nreg 60007 + n ≤ c'.nreg 9999 ∧
      SortedSeq (fun i => (c.nmem (Z1 + i), c.nmem (Z2 + i))) (fun t => c'.nmem (c'.nreg 60007 + t)) n ∧
      (∀ i, i < n → ∃ t, t < n ∧ c'.nmem (c'.nreg 60007 + t) = i) ∧
      (∀ t, t < n → c'.nmem (c'.nreg 60007 + t) < n) := by
  -- 1. the items
  obtain ⟨c₂, k₂, e₂, hk₂, n₂, m₂, rr₂, rm₂, o₂⟩ : ∃ c₂ k₂, Exec P W
      (block [.copyN 30003 9999, .addN 9999 9999 60006]) c c₂ k₂ ∧ k₂ = 2 ∧
      c₂.nreg = upd (upd c.nreg 30003 A₀) 9999 (A₀ + n) ∧ c₂.nmem = c.nmem ∧
      c₂.rreg = c.rreg ∧ c₂.rmem = c.rmem ∧ c₂.output = c.output := by
    exec_block
    · config_simp; rw [hAl, h6]; omega
    · exact ⟨rfl, by config_simp; rw [hAl, h6], rfl, rfl, rfl, rfl⟩
  have a30 : c₂.nreg 30003 = A₀ := by rw [n₂]; config_simp
  have a6 : c₂.nreg 60006 = n := by rw [n₂]; config_simp; exact h6
  have a11 : c₂.nreg 120011 = 1 := by rw [n₂]; config_simp; exact h1
  obtain ⟨c₃, k₃, e₃, hk₃, r₃, rr₃, mm₃, rm₃, o₃, -, -⟩ := scatS_exec (P := P) (W := W)
    (ri := 60020) (rn := 60006) (r1 := 120011) (ra := 60016) (rv := 60017)
    (body := block [.addN 60016 30003 60020, .copyN 60017 60020])
    (B := fun r => decide (r = 60016 ∨ r = 60017)) (by decide) (by decide) (by decide) (by decide)
    (by decide) (JK c₂ (fun r => decide (r = 30003)) A₀) A₀
    (fun d d' hJ hr hm => JK.stable (rs := [60020]) (fun r hr' => by
      simp only [decide_eq_true_eq] at hr'; subst hr'; decide) hJ
      (fun r a b => hr r a (by simpa using b)) hm)
    (n := n) (κ := 2) (fun i => A₀ + i) (fun i => i) (fun i _ => by omega)
    (fun i d hi hJ hwd hri => by
      have g30 : d.nreg 30003 = A₀ := by rw [hJ.1 _ (by decide), a30]
      obtain ⟨d', k, e, hk, v1, v2⟩ : ∃ d' k, Exec P W (block [.addN 60016 30003 60020,
          .copyN 60017 60020]) d d' k ∧ k = 2 ∧ d'.nreg 60016 = A₀ + i ∧ d'.nreg 60017 = i := by
        exec_block
        · rw [g30, hri]; omega
        · exact ⟨rfl, by config_simp; rw [g30, hri], by config_simp; exact hri⟩
      exact ⟨d', k, e, by omega, exec_frameB e (by decide), v1, v2⟩)
    e₂.wb_right (JK.refl _ _ _) a6 a11 (by omega)
  have R₃ : ∀ r, r ≠ 60016 → r ≠ 60017 → r ≠ 60020 → c₃.nreg r = c₂.nreg r := fun r a b c' =>
    r₃ r (by simp; omega) c'
  -- 2. the inputs of the sort
  obtain ⟨c₄, k₄, e₄, hk₄, n₄⟩ : ∃ c₄ k₄, Exec P W sortSet c₃ c₄ k₄ ∧ k₄ = 4 ∧
      c₄.nreg = upd (upd (upd (upd c₃.nreg 30004 n) 115000 Z1) 115001 Z2) 115005 n := by
    have w₃ := e₃.wb_right
    have b6 : c₃.nreg 60006 = n := by rw [R₃ _ (by decide) (by decide) (by decide), a6]
    have b4 : c₃.nreg 60004 = Z1 := by
      rw [R₃ _ (by decide) (by decide) (by decide), n₂]; config_simp; exact h4
    have b5 : c₃.nreg 60005 = Z2 := by
      rw [R₃ _ (by decide) (by decide) (by decide), n₂]; config_simp; exact h5
    unfold sortSet
    exec_block
    exact ⟨rfl, by config_simp; rw [b6, b4, b5]⟩
  have hm₄ : c₄.nmem = c₃.nmem :=
    (exec_frameB e₄ (B := fun r => decide (r = 30004 ∨ 115000 ≤ r ∧ r ≤ 115005)) (by decide)).2.2.1
  have R₄ : ∀ r, r ≠ 30004 → (r < 115000 ∨ 115005 < r) → c₄.nreg r = c₃.nreg r := fun r a b => by
    rw [n₄]; simp only [upd]; split_ifs <;> first | omega
  have g9 : c₄.nreg 9999 = A₀ + n := by
    rw [R₄ _ (by decide) (by decide), R₃ _ (by decide) (by decide) (by decide), n₂]; config_simp
  have g30 : c₄.nreg 30003 = A₀ := by
    rw [R₄ _ (by decide) (by decide), R₃ _ (by decide) (by decide) (by decide), a30]
  have hitems : SortL.seg c₄.nmem (c₄.nreg 30003) (List.range n).length = List.range n := by
    rw [g30, List.length_range, hm₄, mm₃]
    unfold SortL.seg
    apply List.ext_getElem (by simp)
    intro t h1 h2
    simp only [List.getElem_map, List.getElem_range]
    simp only [List.length_map, List.length_range] at h1
    exact scat_at (g := fun i => A₀ + i) (f := fun i => i) h1 (fun j _ hj => by omega)
  -- 3. the sort
  have hW' : A₀ + n ≤ W := by have := SortR.sortCost_ge 20 n; omega
  have hmem₄ : ∀ a, a < A₀ → c₄.nmem a = c.nmem a := fun a ha => by
    rw [hm₄, mm₃, scat_below (fun i _ => by omega) ha, m₂]
  obtain ⟨c₅, k₅, e₅, hk₅, J₅, F₅, s₁, s₂, L', hseg, hperm, hpw⟩ := SortR.sortStmt_exec (P := P)
    (W := W) (lexCmp_ok (m₀ := c₄.nmem) (A₀ := A₀ + n) (B1 := Z1) (B2 := Z2) (K := n)
      (by omega) (by omega) (by have := SortR.sortCost_ge 20 n; omega) hW') (by decide)
    (fun a b d h h' => lexLe_trans _ _ _ _ _ _ _ h h') (lexLe_total _ _ _ _)
    e₄.wb_right ⟨by rw [n₄]; config_simp, by rw [n₄]; config_simp, by rw [n₄]; config_simp,
      fun _ _ => rfl⟩ (by rw [show ALLOC = 9999 from rfl, g9]; exact lexJ_stable _ _ _ _ _) (List.range n) hitems
    (by rw [n₄]; simp [upd]) (by rw [g30, show ALLOC = 9999 from rfl, g9, List.length_range]) (by rw [show ALLOC = 9999 from rfl, g9, List.length_range]; omega)
  rw [List.length_range] at hseg s₂ hk₅
  rw [show ALLOC = 9999 from rfl, g9] at s₁
  -- 4. the base of the sorted items
  have e₆ := Exec.copyN (P := P) e₅.wb_right 60007 30005
  set c₆ : Config := { c₅ with nreg := upd c₅.nreg 60007 (c₅.nreg 30005) } with hc₆
  have ex : Exec P W sortCore c c₆ _ := .seq (.seq e₂ e₃) (.seq e₄ (.seq e₅ e₆))
  have hF5 : ∀ r, bandOf r = 6 → c₅.nreg r = c₄.nreg r := fun r hr =>
    F₅.1 r (by simp [hr, bSort]) (by unfold ALLOC; intro h; rw [h] at hr; simp [bandOf] at hr)
  have v7 : c₆.nreg 60007 = c₅.nreg 30005 := by rw [hc₆]; config_simp
  have hm₆ : c₆.nmem = c₅.nmem := rfl
  have hsd : ∀ t, t < n → c₆.nmem (c₆.nreg 60007 + t) = L'.getD t 0 := fun t ht => by
    rw [hm₆, v7, ← hseg, SortL.seg_getD t ht]
  have hL'len : L'.length = n := by rw [← hseg, SortL.seg_length]
  have hmemL : ∀ t, t < n → L'.getD t 0 < n := fun t ht => by
    have : L'.getD t 0 ∈ L' := by rw [NFLoc.getD_of_lt 0 (by omega)]; exact List.getElem_mem _
    exact List.mem_range.1 (hperm.subset this)
  have g9' : c₄.nreg ALLOC = A₀ + n := g9
  have hAl' : c.nreg ALLOC = A₀ := hAl
  refine ⟨c₆, _, ex, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := SortR.sortCost_ge 20 n; omega
  · -- the frame
    have F14 : FrameN dBands c c₄ := by
      refine PF.frameN (B := fun r => decide (r = 9999) || decide (60001 ≤ r ∧ r ≤ 60020) ||
        decide (30003 ≤ r ∧ r ≤ 30004) || decide (115000 ≤ r ∧ r ≤ 115005))
        ⟨fun r hr => ?_, fun r hr => ?_, fun a ha => ?_, fun a ha => ?_, ?_⟩ (fun r hr => ?_) ?_
      · simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr
        rw [R₄ r (by omega) (by omega), R₃ r (by omega) (by omega) (by omega), n₂]
        simp only [upd]; split_ifs <;> first | omega
      · have := (exec_frameB e₄ (B := fun r => decide (r = 30004 ∨ 115000 ≤ r ∧ r ≤ 115005))
          (by decide)).2.1 r (by simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢; omega)
        rw [this, rr₃ r (by simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hr ⊢; omega),
          rr₂]
      · rw [hmem₄ a (by rw [hAl'] at ha; exact ha)]
      · rw [(exec_frameB e₄ (B := fun r => decide (r = 30004 ∨ 115000 ≤ r ∧ r ≤ 115005))
          (by decide)).2.2.2.1, rm₃, rm₂]
      · rw [(exec_frameB e₄ (B := fun r => decide (r = 30004 ∨ 115000 ≤ r ∧ r ≤ 115005))
          (by decide)).2.2.2.2, o₃, o₂]
      · simp only [Bool.or_eq_true, decide_eq_true_eq] at hr
        rcases hr with ((h | h) | h) | h
        · exact Or.inr h
        · left; simp [dBands, bDecomp, bandOf]; omega
        · left; simp [dBands, bSort, bandOf]; omega
        · left; simp [dBands, bOPrep, bandOf]; omega
      · have := (exec_frameB e₄ (B := fun r => decide (r = 30004 ∨ 115000 ≤ r ∧ r ≤ 115005))
          (by decide)).2.1 ALLOC (by decide)
        rw [this, rr₃ _ (by decide), rr₂]
    have F56 : FrameN dBands c₅ c₆ :=
      Frame.toN (NFLoc.frame_of_frameB (exec_frameB e₆ (B := fun r => decide (r = 60007))
        (by decide)) (fun r hr => by
          simp at hr; subst hr; exact ⟨by simp [dBands, bDecomp, bandOf], by decide⟩) 1)
    exact (F14.trans (FrameN.mono (Frame.toN F₅) (by decide))
      (by rw [hAl', g9']; omega)).trans F56
      (by rw [hAl']; have := F₅.2.2.2.2.2.1; rw [g9'] at this; omega)
  · have := F₅.2.2.2.2.2.1; rw [g9'] at this
    rw [hc₆]; exact this
  · have := F₅.2.2.2.2.2.2; rw [g9'] at this
    rw [hc₆]; show c₅.nreg ALLOC ≤ _; omega
  · intro r hr a b c' d
    rw [hc₆]; config_simp
    rw [upd_other _ _ _ a, hF5 r hr, R₄ r (by unfold bandOf at hr; omega)
      (by unfold bandOf at hr; omega), R₃ r b c' d, n₂]
    rw [upd_other _ _ _ (by unfold bandOf at hr; omega),
      upd_other _ _ _ (by unfold bandOf at hr; omega)]
  · rw [v7]; exact s₁
  · rw [v7, hc₆]; config_simp; exact s₂
  · -- sorted
    intro t t' htt ht'
    beta_reduce
    rw [hsd t (by omega), hsd t' ht']
    have hA := hmemL t (by omega)
    have hB := hmemL t' ht'
    have hc4 : ∀ i, i < n → c₄.nmem (Z1 + i) = c.nmem (Z1 + i) ∧ c₄.nmem (Z2 + i) = c.nmem (Z2 + i) :=
      fun i hi => ⟨hmem₄ _ (by omega), hmem₄ _ (by omega)⟩
    rcases eq_or_lt_of_le htt with h | h
    · subst h; right; exact ⟨rfl, le_rfl⟩
    · have := List.pairwise_iff_getElem.1 hpw t t' (by omega) (by omega) h
      rw [← NFLoc.getD_of_lt 0 (by omega), ← NFLoc.getD_of_lt 0 (by omega)] at this
      unfold lexLe at this
      rw [ite_eq_left hA, ite_eq_left hB] at this
      simp only [decide_eq_true_eq] at this
      rw [(hc4 _ hA).1, (hc4 _ hB).1, (hc4 _ hA).2, (hc4 _ hB).2] at this
      exact this
  · intro i hi
    have : i ∈ L' := hperm.symm.subset (List.mem_range.2 hi)
    obtain ⟨t, ht, e⟩ := List.getElem_of_mem this
    exact ⟨t, by omega, by rw [hsd t (by omega), NFLoc.getD_of_lt 0 ht, e]⟩
  · intro t ht; rw [hsd t ht]; exact hmemL t ht

end

end OracleR

end Chazelle.Core
