module

public meta import Chazelle.Arithmetic

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
noncomputable def brk (c x : ℝ) : ℝ :=
  c + seg β N x + (x - β (seg β N x)) / (β (seg β N x + 1) - β (seg β N x))

variable {β N}

/-- Increasing breakpoints. -/
def BrkInc (β : ℕ → ℝ) (N : ℕ) : Prop := ∀ j, j < N → β j < β (j + 1)

section
variable (h : BrkInc β N)
include h
theorem BrkInc.lt {i j : ℕ} (hij : i < j) (hj : j ≤ N) : β i < β j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | h'
    · exact lt_trans (ih h' (by omega)) (h j (by omega))
    aesop

theorem BrkInc.le {i j : ℕ} (hij : i ≤ j) (hj : j ≤ N) : β i ≤ β j := by
  rcases hij.lt_or_eq with h' | h'
  · exact (h.lt h' hj).le
  · rw [h']

/-- **The piece of a key.** -/
theorem seg_spec (hN : 1 ≤ N) {x : ℝ} (hx0 : β 0 ≤ x) (hxN : x < β N) :
    seg β N x < N ∧ β (seg β N x) ≤ x ∧ x < β (seg β N x + 1) := by
  set S := (Finset.Ico 1 N).filter fun j => β j ≤ x with hS
  -- `S` is an initial segment `[1, k]`
  have hdown : ∀ j ∈ S, ∀ i, 1 ≤ i → i ≤ j → i ∈ S := by
    grind [Chazelle.Core.ArcT.BrkInc.le]
  
  have hsub : S ⊆ Finset.Icc 1 S.card := by
    intro j hj
    rw [Finset.mem_Icc]
    refine ⟨(Finset.mem_Ico.1 (Finset.mem_filter.1 hj).1).1, ?_⟩
    have : Finset.Icc 1 j ⊆ S := fun i hi => by
      grind
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
    · ram_grind
    · rintro ⟨h1, h2⟩
      by_contra hn
      -- then `S ⊆ [1, j - 1]`, too small
      have : S ⊆ Finset.Icc 1 (j - 1) := by
        grind
      have := Finset.card_le_card this
      simp at this; omega
  show k < N ∧ β k ≤ x ∧ x < β (k + 1)
  refine ⟨by omega, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos k with h0 | h0
    all_goals grind
  · by_cases hk1 : k + 1 = N
    · grind
    · by_contra hlt
      push Not at hlt
      have : k + 1 ∈ S := by
        grind
      grind

theorem seg_top (_hN : 1 ≤ N) : seg β N (β N) = N - 1 := by
  unfold seg
  have : (Finset.Ico 1 N).filter (fun j => β j ≤ β N) = Finset.Ico 1 N := by
    apply Finset.filter_true_of_mem
    intro j hj
    exact h.le (Finset.mem_Ico.1 hj).2.le le_rfl
  rw [this]; simp


end

variable {c : ℝ}

section
variable (h : BrkInc β N)
include h
section
variable (hN : 1 ≤ N)
include hN
/-- The map on a piece. -/
theorem brk_piece {x : ℝ} (hx0 : β 0 ≤ x) (hxN : x < β N) :
    c + seg β N x ≤ brk β N c x ∧ brk β N c x < c + seg β N x + 1 := by
  obtain ⟨hk, h1, h2⟩ := seg_spec h hN hx0 hxN
  have hpos : 0 < β (seg β N x + 1) - β (seg β N x) := by linarith
  unfold brk
  constructor
  · have : 0 ≤ (x - β (seg β N x)) / (β (seg β N x + 1) - β (seg β N x)) :=
      div_nonneg (by linarith) hpos.le
    linarith
  · have : (x - β (seg β N x)) / (β (seg β N x + 1) - β (seg β N x)) < 1 := by
      rw [div_lt_one hpos]; linarith
    linarith

theorem brk_top : brk β N c (β N) = c + N := by
  unfold brk
  rw [seg_top h hN, Nat.sub_add_cancel hN]
  have hpos : 0 < β N - β (N - 1) := by
    have := h (N - 1) (by omega); simp_all
  rw [div_self hpos.ne']
  have : ((N - 1 : ℕ) : ℝ) = N - 1 := by simp_all
  grind


end

theorem brk_bot (_hN : 1 ≤ N) : brk β N c (β 0) = c := by
  have hs : seg β N (β 0) = 0 := by
    unfold seg
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j hj
    exact not_le.2 (h.lt (Finset.mem_Ico.1 hj).1 (Finset.mem_Ico.1 hj).2.le)
  simp_all [brk] <;> omega_nf


end

section
variable (h : BrkInc β N) (hN : 1 ≤ N)
include h hN
/-- **The key map is strictly increasing.** -/
theorem brk_strictMonoOn :
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
      linarith
    · unfold brk
      rw [hs] at hx1 hx2 ⊢
      have hpos : 0 < β (seg β N y + 1) - β (seg β N y) := by linarith
      have : (x - β (seg β N y)) / (β (seg β N y + 1) - β (seg β N y)) <
          (y - β (seg β N y)) / (β (seg β N y + 1) - β (seg β N y)) :=
        div_lt_div_of_pos_right (by linarith) hpos
      linarith
    · exfalso
      have : seg β N y + 1 ≤ seg β N x := hs
      have := h.le this (by have := (seg_spec h hN hx.1 hxN).1; omega)
      linarith
  · rw [hyN, brk_top h hN]
    have := (seg_spec h hN hx.1 hxN).1
    have : ((seg β N x : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast this
    linarith

/-- **The key map is onto.** -/
theorem brk_onto {y : ℝ} (hy0 : c ≤ y) (hyN : y ≤ c + N) :
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
  have hx1 : β j ≤ x := by simp_all +zetaDelta 
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
  grind [brk]

/-- **Breakpoints go to integer keys, and only they.** -/
theorem brk_int_iff {c₀ : ℕ} {x : ℝ} (hx0 : β 0 ≤ x)
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
      simp_all
    grind [brk, div_eq_zero_iff]
  · rintro ⟨j, hj, rfl⟩
    have hseg : seg β N (β j) = j := by
      rcases lt_trichotomy (seg β N (β j)) j with hs | hs | hs
      all_goals (grind [Chazelle.Core.ArcT.BrkInc.le, Chazelle.Core.ArcT.BrkInc.lt])
    refine ⟨c₀ + j, ?_⟩
    simp_all [brk] 


end

end

end ArcT

end Chazelle.Core
