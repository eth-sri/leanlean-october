module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseArcT

/-!
# WP-M (X, part 2): piecewise linear key maps

A key range `[β 0, β N]` of one walk, cut at breakpoints `β 0 < β 1 < … < β N`, is mapped onto the
key range `[c, c + N]` of another walk, linearly from `[β j, β (j + 1)]` onto `[c + j, c + j + 1]`
(`brk`).  This is the key map of the arc transfer (`ArcT.ArcCorr`) when the breakpoints are the
host keys of an arc (extraction) or the vertex keys (transition).

Main facts: strict monotonicity (`brk_strictMonoOn`), surjectivity (`brk_onto`), and that exactly
the breakpoints go to integer keys (`brk_int_iff`).
-/

namespace Chazelle.Core

namespace ArcT

@[expose] public section

open Set

variable (β : ℕ → ℝ) (N : ℕ)

/-- The index of the piece containing `x`: the number of inner breakpoints `≤ x`. -/
noncomputable def seg (x : ℝ) : ℕ := ((Finset.Ico 1 N).filter fun j => β j ≤ x).card

/-- **The piecewise linear key map.** -/
noncomputable def brk (c : ℝ) (x : ℝ) : ℝ :=
  c + seg β N x + (x - β (seg β N x)) / (β (seg β N x + 1) - β (seg β N x))

variable {β N}

/-- Increasing breakpoints. -/
def BrkInc (β : ℕ → ℝ) (N : ℕ) : Prop := ∀ j, j < N → β j < β (j + 1)

theorem BrkInc.lt (h : BrkInc β N) {i j : ℕ} (hij : i < j) (hj : j ≤ N) : β i < β j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | h'
    · exact lt_trans (ih h' (⋄)) (h j (⋄))
    · rw [h']; exact h j (⋄)

theorem BrkInc.le (h : BrkInc β N) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ N) : β i ≤ β j := by
  rcases hij.lt_or_eq with h' | h'
  · exact (h.lt h' hj).le
  · Ξ h'

/-- **The piece of a key.** -/
theorem seg_spec (h : BrkInc β N) (hN : 1 ≤ N) {x : ℝ} (hx0 : β 0 ≤ x) (hxN : x < β N) :
    seg β N x < N ∧ β (seg β N x) ≤ x ∧ x < β (seg β N x + 1) := by
  set S := (Finset.Ico 1 N).filter fun j => β j ≤ x with hS
  -- `S` is an initial segment `[1, k]`
  have hdown : ∀ j ∈ S, ∀ i, 1 ≤ i → i ≤ j → i ∈ S := by
    intro j hj i hi hij
    Ξ' hS, Finset.mem_filter, Finset.mem_Ico at hj ⊢
    exact ⟨⟨hi, ⋄⟩, le_trans (h.le hij (⋄)) hj.2⟩
  have hcard : ∀ k, k ≤ N - 1 → (∀ i, 1 ≤ i → i ≤ k → β i ≤ x) → k ≤ S.card := by
    intro k hk hall
    have : Finset.Icc 1 k ⊆ S := by
      intro i hi
      Ξ' Finset.mem_Icc at hi
      Ξ hS, Finset.mem_filter, Finset.mem_Ico
      exact ⟨⟨hi.1, ⋄⟩, hall i hi.1 hi.2⟩
    have := Finset.card_le_card this
    simpa using this
  have hsub : S ⊆ Finset.Icc 1 S.card := by
    intro j hj
    Ξ Finset.mem_Icc
    refine ⟨(Finset.mem_Ico.1 (Finset.mem_filter.1 hj).1).1, ?_⟩
    have : Finset.Icc 1 j ⊆ S := fun i hi => by
      Ξ' Finset.mem_Icc at hi; exact hdown j hj i hi.1 hi.2
    have := Finset.card_le_card this
    simpa using this
  set k := S.card with hk
  have hkN : k ≤ N - 1 := by
    have : S ⊆ Finset.Ico 1 N := Finset.filter_subset _ _
    have := Finset.card_le_card this
    simp at this; omega
  have hmem : ∀ j, j ∈ S ↔ 1 ≤ j ∧ j ≤ k := by
    intro j
    constructor
    · intro hj; have := hsub hj; Ξ' Finset.mem_Icc at this; exact this
    · rintro ⟨h1, h2⟩
      by_contra hn
      -- then `S ⊆ [1, j - 1]`, too small
      have : S ⊆ Finset.Icc 1 (j - 1) := by
        intro i hi
        Ξ Finset.mem_Icc
        refine ⟨(Finset.mem_Ico.1 (Finset.mem_filter.1 hi).1).1, ?_⟩
        by_contra hij
        exact hn (hdown i hi j h1 (⋄))
      have := Finset.card_le_card this
      simp at this; omega
  show k < N ∧ β k ≤ x ∧ x < β (k + 1)
  refine ⟨⋄, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0]; exact hx0
    · exact (Finset.mem_filter.1 ((hmem k).2 ⟨h0, le_rfl⟩)).2
  · by_cases hk1 : k + 1 = N
    · rw [hk1]; exact hxN
    · by_contra hlt
      push Not at hlt
      have : k + 1 ∈ S := by
        rw [hS, Finset.mem_filter, Finset.mem_Ico]; exact ⟨⟨⋄, ⋄⟩, hlt⟩
      have := ((hmem (k + 1)).1 this).2
      omega

theorem seg_top (h : BrkInc β N) (_hN : 1 ≤ N) : seg β N (β N) = N - 1 := by
  unfold seg
  have : (Finset.Ico 1 N).filter (fun j => β j ≤ β N) = Finset.Ico 1 N := by
    apply Finset.filter_true_of_mem
    intro j hj
    exact h.le (Finset.mem_Ico.1 hj).2.le le_rfl
  rw [this]; simp

variable {c : ℝ}

/-- The map on a piece. -/
theorem brk_piece (h : BrkInc β N) (hN : 1 ≤ N) {x : ℝ} (hx0 : β 0 ≤ x) (hxN : x < β N) :
    c + seg β N x ≤ brk β N c x ∧ brk β N c x < c + seg β N x + 1 := by
  obtain ⟨hk, h1, h2⟩ := seg_spec h hN hx0 hxN
  have hpos : 0 < β (seg β N x + 1) - β (seg β N x) := ⟡
  unfold brk
  constructor
  · have : 0 ≤ (x - β (seg β N x)) / (β (seg β N x + 1) - β (seg β N x)) :=
      div_nonneg (⟡) hpos.le
    linarith
  · have : (x - β (seg β N x)) / (β (seg β N x + 1) - β (seg β N x)) < 1 := by
      rw [div_lt_one hpos]; linarith
    linarith

theorem brk_top (h : BrkInc β N) (hN : 1 ≤ N) : brk β N c (β N) = c + N := by
  unfold brk
  Ξ seg_top h hN, Nat.sub_add_cancel hN
  have hpos : 0 < β N - β (N - 1) := by
    have := h (N - 1) (⋄); Ξ' Nat.sub_add_cancel hN at this; linarith
  Ξ div_self hpos.ne'
  have : ((N - 1 : ℕ) : ℝ) = N - 1 := by rw [Nat.cast_sub hN]; simp
  rw [this]; ring

theorem brk_bot (h : BrkInc β N) (_hN : 1 ≤ N) : brk β N c (β 0) = c := by
  have hs : seg β N (β 0) = 0 := by
    unfold seg
    Ξ Finset.card_eq_zero, Finset.filter_eq_empty_iff
    intro j hj
    exact not_le.2 (h.lt (Finset.mem_Ico.1 hj).1 (Finset.mem_Ico.1 hj).2.le)
  unfold brk; rw [hs]; simp

/-- **The key map is strictly increasing.** -/
theorem brk_strictMonoOn (h : BrkInc β N) (hN : 1 ≤ N) :
    StrictMonoOn (brk β N c) (Icc (β 0) (β N)) := by
  intro x hx y hy hxy
  have hxN : x < β N := lt_of_lt_of_le hxy hy.2
  have px := brk_piece (c := c) h hN hx.1 hxN
  rcases hy.2.lt_or_eq with hyN | hyN
  · have py := brk_piece (c := c) h hN hy.1 hyN
    obtain ⟨-, hx1, hx2⟩ := seg_spec h hN hx.1 hxN
    obtain ⟨-, hy1, hy2⟩ := seg_spec h hN hy.1 hyN
    rcases lt_trichotomy (seg β N x) (seg β N y) with hs | hs | hs
    · have : ((seg β N x : ℕ) : ℝ) + 1 ≤ seg β N y := by exact_mod_cast hs
      linarith [px.2, py.1]
    · unfold brk
      rw [hs] at hx1 hx2 ⊢
      have hpos : 0 < β (seg β N y + 1) - β (seg β N y) := ⟡
      have : (x - β (seg β N y)) / (β (seg β N y + 1) - β (seg β N y)) <
          (y - β (seg β N y)) / (β (seg β N y + 1) - β (seg β N y)) :=
        div_lt_div_of_pos_right (⟡) hpos
      linarith
    · exfalso
      have : seg β N y + 1 ≤ seg β N x := hs
      have := h.le this (by have := (seg_spec h hN hx.1 hxN).1; omega)
      linarith
  · Ξ hyN, brk_top h hN
    have := (seg_spec h hN hx.1 hxN).1
    have : ((seg β N x : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast this
    linarith [px.2]

/-- **The key map is onto.** -/
theorem brk_onto (h : BrkInc β N) (hN : 1 ≤ N) {y : ℝ} (hy0 : c ≤ y) (hyN : y ≤ c + N) :
    ∃ x ∈ Icc (β 0) (β N), brk β N c x = y := by
  rcases hyN.lt_or_eq with hyN | hyN
  swap
  · exact ⟨β N, ⟨h.le (Nat.zero_le _) le_rfl, le_rfl⟩, by rw [brk_top h hN, hyN]⟩
  set j := ⌊y - c⌋₊ with hj
  have hjN : j < N := by
    rw [hj, Nat.floor_lt (by linarith)]; linarith
  have hj1 : (j : ℝ) ≤ y - c := Nat.floor_le (by linarith)
  have hj2 : y - c < j + 1 := Nat.lt_floor_add_one _
  have hpos : 0 < β (j + 1) - β j := by linarith [h j hjN]
  set x := β j + (y - c - j) * (β (j + 1) - β j)
  have hx1 : β j ≤ x := by have := mul_nonneg (show 0 ≤ y - c - j by linarith) hpos.le; linarith
  have hx2 : x < β (j + 1) := by
    have : (y - c - j) * (β (j + 1) - β j) < 1 * (β (j + 1) - β j) :=
      mul_lt_mul_of_pos_right (by linarith) hpos
    linarith
  have hx0 : β 0 ≤ x := le_trans (h.le (Nat.zero_le _) hjN.le) hx1
  have hxN : x < β N := lt_of_lt_of_le hx2 (h.le (by omega) le_rfl)
  -- the piece of `x` is `j`
  have hseg : seg β N x = j := by
    obtain ⟨hk, h1, h2⟩ := seg_spec h hN hx0 hxN
    rcases lt_trichotomy (seg β N x) j with hs | hs | hs
    · have := h.le (show seg β N x + 1 ≤ j by omega) hjN.le; linarith
    · exact hs
    · have := h.le (show j + 1 ≤ seg β N x by omega) hk.le; linarith
  refine ⟨x, ⟨hx0, hxN.le⟩, ?_⟩
  unfold brk
  rw [hseg]
  have : (x - β j) / (β (j + 1) - β j) = y - c - j := by
    field_simp; ring
  rw [this]; ring

/-- **Breakpoints go to integer keys, and only they.** -/
theorem brk_int_iff (h : BrkInc β N) (hN : 1 ≤ N) {c₀ : ℕ} {x : ℝ} (hx0 : β 0 ≤ x)
    (hxN : x < β N) : (∃ k : ℕ, brk β N c₀ x = k) ↔ ∃ j, j < N ∧ x = β j := by
  obtain ⟨hk, h1, h2⟩ := seg_spec h hN hx0 hxN
  have p := brk_piece (c := (c₀ : ℝ)) h hN hx0 hxN
  constructor
  · rintro ⟨k, hk'⟩
    refine ⟨seg β N x, hk, ?_⟩
    rw [hk'] at p
    have e : (k : ℝ) = c₀ + seg β N x := by
      have a1 : c₀ + seg β N x ≤ k := by exact_mod_cast p.1
      have a2 : k < c₀ + seg β N x + 1 := by exact_mod_cast p.2
      have : k = c₀ + seg β N x := by omega
      rw [this]; push_cast; ring
    rw [e] at hk'
    unfold brk at hk'
    have hpos : 0 < β (seg β N x + 1) - β (seg β N x) := by linarith
    have : (x - β (seg β N x)) / (β (seg β N x + 1) - β (seg β N x)) = 0 := by linarith
    rw [div_eq_zero_iff] at this
    rcases this with h' | h'
    · linarith
    · linarith
  · rintro ⟨j, hj, rfl⟩
    have hseg : seg β N (β j) = j := by
      rcases lt_trichotomy (seg β N (β j)) j with hs | hs | hs
      · have := h.le (show seg β N (β j) + 1 ≤ j by omega) hj.le; linarith
      · exact hs
      · have := h.lt (show j < seg β N (β j) by omega) hk.le; linarith
    refine ⟨c₀ + j, ?_⟩
    unfold brk; rw [hseg]; simp

end

end ArcT

end Chazelle.Core
