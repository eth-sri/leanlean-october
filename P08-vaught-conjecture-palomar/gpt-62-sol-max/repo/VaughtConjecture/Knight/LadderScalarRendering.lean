/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SupportLadderRows
public import VaughtConjecture.AmalgamationPlan.Plan
public import VaughtConjecture.Knight.Domain
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

namespace VaughtConjecture.Knight.LadderScalarRendering

open Transform Value ExtOrd

noncomputable section

open Classical in
/-- One-based rank on a finite set of positive values. -/
def rank (S : Finset ExtOrd) (x : ExtOrd) : ℕ := (S.filter (· ≤ x)).card

open Classical in
/-- The occupied initial segment followed by the constant ceiling tail. -/
def level (S : Finset ExtOrd) (C : ExtOrd) (i : ℕ) : ExtOrd :=
  if S.card < i then C else (S.filter (fun x => rank S x ≤ i)).sup id

theorem rank_le_card (S : Finset ExtOrd) (x : ExtOrd) : rank S x ≤ S.card := by
  classical
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem rank_mono (S : Finset ExtOrd) : Monotone (rank S) := by
  classical
  intro x y hxy
  apply Finset.card_le_card
  grind

theorem rank_strict {S : Finset ExtOrd} {x y : ExtOrd} (hy : y ∈ S) (hxy : x < y) :
    rank S x < rank S y := by
  classical
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · grind
  · intro he
    have hm : y ∈ S.filter (· ≤ y) := Finset.mem_filter.mpr ⟨hy, le_rfl⟩
    grind

theorem rank_pos {S : Finset ExtOrd} {x : ExtOrd} (hx : x ∈ S) : 0 < rank S x := by
  classical
  exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, le_rfl⟩⟩

theorem rank_bot {S : Finset ExtOrd} (hS : ⊥ ∉ S) : rank S ⊥ = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  simp_all

theorem level_zero (S : Finset ExtOrd) (C : ExtOrd) : level S C 0 = ⊥ := by
  classical
  rw [level, ite_eq_right (by omega)]
  have he : S.filter (fun x => rank S x ≤ 0) = ∅ := by
    grind [rank_pos]
  simp_all

theorem level_rank {S : Finset ExtOrd} {x : ExtOrd} (hx : x ∈ S) (C : ExtOrd) :
    level S C (rank S x) = x := by
  classical
  rw [level, ite_eq_right (not_lt.mpr (rank_le_card S x))]
  apply le_antisymm
  · apply Finset.sup_le
    intro y hy
    by_contra hn
    have hs := rank_strict (Finset.mem_filter.mp hy).1 (not_le.mp hn)
    grind
  · exact Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨hx, le_rfl⟩)

theorem level_le {S : Finset ExtOrd} {C : ExtOrd} (hC : ∀ x ∈ S, x ≤ C) (i : ℕ) :
    level S C i ≤ C := by
  classical
  unfold level
  aesop

theorem level_mono {S : Finset ExtOrd} {C : ExtOrd} (hC : ∀ x ∈ S, x ≤ C) :
    Monotone (level S C) := by
  classical
  intro i k hik
  grind [level, level_le]

theorem level_supported (S : Finset ExtOrd) (C : ExtOrd) (i : ℕ) :
    level S C i = ⊥ ∨ level S C i ∈ S ∨ level S C i = C := by
  classical
  unfold level
  split_ifs
  · simp
  · by_cases hn : (S.filter (fun x => rank S x ≤ i)).Nonempty
    · obtain ⟨x, hx, he⟩ := Finset.sup_mem_of_nonempty (f := id) hn
      simp_all
    simp_all

theorem rank_min' {S : Finset ExtOrd} (hS : S.Nonempty) : rank S (S.min' hS) = 1 := by
  classical
  have he : S.filter (· ≤ S.min' hS) = {S.min' hS} := by
    ext x
    constructor
    · intro hx
      exact Finset.mem_singleton.mpr (le_antisymm (Finset.mem_filter.mp hx).2
        (Finset.min'_le S x (Finset.mem_filter.mp hx).1))
    · intro hx
      rw [Finset.mem_singleton.mp hx]
      exact Finset.mem_filter.mpr ⟨Finset.min'_mem S hS, le_rfl⟩
  rw [rank, he, Finset.card_singleton]

theorem level_pos {S : Finset ExtOrd} {C : ExtOrd} (hS : ⊥ ∉ S)
    (hC : ∀ x ∈ S, x ≤ C) (hpos : C ≠ ⊥) {i : ℕ} (hi : 0 < i) :
    level S C i ≠ ⊥ := by
  classical
  by_cases hn : S.Nonempty
  · have hm := Finset.min'_mem S hn
    have hle : S.min' hn ≤ level S C i := by
      rw [← level_rank hm C, rank_min' hn]
      exact level_mono hC hi
    aesop
  simp_all [level]

open Classical in
/-- One more than the number of occupied values strictly below a cap. -/
def next (S : Finset ExtOrd) (h : ExtOrd) : ℕ := (S.filter (· < h)).card + 1

theorem next_le (S : Finset ExtOrd) (h : ExtOrd) : next S h ≤ S.card + 1 := by
  classical
  exact Nat.add_le_add_right (by grind) 1

theorem rank_lt_next {S : Finset ExtOrd} {x h : ExtOrd} (hx : x ∈ S) :
    rank S x < next S h ↔ x < h := by
  classical
  constructor
  · intro hr
    by_contra hn
    have hsub : S.filter (· < h) ⊂ S.filter (· ≤ x) := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨?_, ?_⟩
      · grind
      · intro he
        have hm : x ∈ S.filter (· ≤ x) := Finset.mem_filter.mpr ⟨hx, le_rfl⟩
        grind
    have hc := Finset.card_lt_card hsub
    grind [rank, next]
  · intro hxh
    have hc : (S.filter (· ≤ x)).card ≤ (S.filter (· < h)).card := by
      apply Finset.card_le_card
      grind
    exact Nat.lt_succ_of_le hc

theorem rank_congr_below {S T : Finset ExtOrd} {h x : ExtOrd}
    (hst : ∀ y, y < h → (y ∈ S ↔ y ∈ T)) (hx : x < h) : rank S x = rank T x := by
  classical
  unfold rank
  congr 1
  grind

open Classical in
theorem below_eq {S T : Finset ExtOrd} {h : ExtOrd}
    (hst : ∀ y, y < h → (y ∈ S ↔ y ∈ T)) : S.filter (· < h) = T.filter (· < h) := by aesop

theorem level_agree_below {S T : Finset ExtOrd} {C h : ExtOrd}
    (hst : ∀ y, y < h → (y ∈ S ↔ y ∈ T)) {i : ℕ} (hi : i < next S h) :
    level S C i = level T C i := by
  classical
  have he := below_eq hst
  have hn : next S h = next T h := congrArg (fun s : Finset ExtOrd => s.card + 1) he
  have hiS : ¬S.card < i := by have := next_le S h; omega
  have hiT : ¬T.card < i := by have := next_le T h; omega
  rw [level, ite_eq_right hiS, level, ite_eq_right hiT]
  congr 1
  ext x
  constructor
  · intro hx
    obtain ⟨hxS, hr⟩ := Finset.mem_filter.mp hx
    have hxh := (rank_lt_next hxS).mp (hr.trans_lt hi)
    grind [rank_congr_below]
  · intro hx
    obtain ⟨hxT, hr⟩ := Finset.mem_filter.mp hx
    have hxh := (rank_lt_next hxT).mp (hr.trans_lt (hn ▸ hi))
    grind [rank_congr_below]

theorem level_reaches (S : Finset ExtOrd) {C h : ExtOrd} (hh : h ≤ C) :
    h ≤ level S C (next S h) := by
  classical
  by_cases hc : S.card < next S h
  · rwa [level, ite_eq_left hc]
  · have hn : (S.filter (h ≤ ·)).Nonempty := by
      by_contra hn
      simp_all [next]
    let x := (S.filter (h ≤ ·)).min' hn
    have hxm := Finset.min'_mem (S.filter (h ≤ ·)) hn
    have hxS : x ∈ S := (Finset.mem_filter.mp hxm).1
    have hxh : h ≤ x := (Finset.mem_filter.mp hxm).2
    have he : S.filter (· ≤ x) = insert x (S.filter (· < h)) := by
      ext y
      constructor
      · intro hy
        obtain ⟨hyS, hyx⟩ := Finset.mem_filter.mp hy
        by_cases hyh : y < h
        · simp_all
        · exact Finset.mem_insert.mpr (Or.inl (le_antisymm hyx
            (Finset.min'_le _ y (Finset.mem_filter.mpr ⟨hyS, not_lt.mp hyh⟩))))
      grind
    have hr : rank S x = next S h := by
      rw [rank, he, Finset.card_insert_of_notMem]
      · rfl
      simp_all
    rwa [← hr, level_rank hxS]

variable {X : Type*} [Fintype X]

open Classical in
def values (p : X → ExtOrd) : Finset ExtOrd := (Finset.univ.image p).erase ⊥

theorem mem_values {p : X → ExtOrd} {x : ExtOrd} :
    x ∈ values p ↔ x ≠ ⊥ ∧ ∃ d, p d = x := by grind [values]

theorem bot_not_values (p : X → ExtOrd) : ⊥ ∉ values p := by
  rw [mem_values]
  simp

theorem values_card_le (p : X → ExtOrd) : (values p).card ≤ Fintype.card X := by
  classical
  exact (Finset.card_le_card (Finset.erase_subset _ _)).trans
    ((Finset.card_image_le).trans_eq (Finset.card_univ))

def fieldRank (p : X → ExtOrd) (d : X) : ℕ := rank (values p) (p d)

theorem fieldRank_le (p : X → ExtOrd) (d : X) : fieldRank p d ≤ Fintype.card X :=
  (rank_le_card _ _).trans (values_card_le p)

theorem field_readback (p : X → ExtOrd) (C : ExtOrd) (d : X) :
    level (values p) C (fieldRank p d) = p d := by
  by_cases hz : p d = ⊥
  · simp [fieldRank, hz, rank_bot (bot_not_values p), level_zero]
  · exact level_rank (mem_values.mpr ⟨hz, d, rfl⟩) C

theorem values_bound {p : X → ExtOrd} {C : ExtOrd} (hC : ∀ d, p d ≤ C) :
    ∀ x ∈ values p, x ≤ C := by
  intro x hx
  obtain ⟨_, d, rfl⟩ := mem_values.mp hx
  tauto

theorem level_visible {p : X → ExtOrd} {C : ExtOrd} (hp : ∀ d, SelfVis 1 (p d))
    (hC : SelfVis 1 C) (i : ℕ) : SelfVis 1 (level (values p) C i) := by
  rcases level_supported (values p) C i with hz | hv | hc
  · aesop
  · obtain ⟨_, d, hd⟩ := mem_values.mp hv
    grind
  aesop

private theorem eq_of_capped_lt {x y h : ExtOrd} (he : min x h = min y h) (hx : x < h) :
    x = y := by grind

theorem values_agree_below {p q : X → ExtOrd} {h : ExtOrd}
    (hag : ∀ d, min (p d) h = min (q d) h) :
    ∀ x, x < h → (x ∈ values p ↔ x ∈ values q) := by grind [mem_values]

/-- Capped scalar agreement constructs the common rank prefix. -/
theorem fieldRank_agreement {p q : X → ExtOrd} {h : ExtOrd} (hh : ⊥ < h)
    (hag : ∀ d, min (p d) h = min (q d) h) :
    FiniteProfileControllers.Agree (fieldRank p) (fieldRank q) (next (values p) h) := by
  have hs := values_agree_below hag
  have hn : next (values p) h = next (values q) h :=
    congrArg (fun s : Finset ExtOrd => s.card + 1) (below_eq hs)
  intro d
  by_cases hd : p d < h
  · have he := eq_of_capped_lt (hag d) hd
    exact congrArg (fun n => min n (next (values p) h))
      ((rank_congr_below hs hd).trans (congrArg (rank (values q)) he))
  · have hph : h ≤ p d := not_lt.mp hd
    have hqh : h ≤ q d := by
      grind
    have hpv : p d ∈ values p := mem_values.mpr ⟨ne_of_gt (hh.trans_le hph), d, rfl⟩
    have hqv : q d ∈ values q := mem_values.mpr ⟨ne_of_gt (hh.trans_le hqh), d, rfl⟩
    have hpr : next (values p) h ≤ fieldRank p d :=
      not_lt.mp (fun hr => hd ((rank_lt_next hpv).mp hr))
    have hqr : next (values p) h ≤ fieldRank q d := by
      rw [hn]
      exact not_lt.mp (fun hr => (not_lt_of_ge hqh) ((rank_lt_next hqv).mp hr))
    omega

/-- Both ladders reach the cap at a constructed common rank and agree
literally at all preceding rungs. No rank-cut hypothesis is supplied. -/
theorem common_rank_cut {p q : X → ExtOrd} {C h : ExtOrd}
    (hh : ⊥ < h) (hC : h ≤ C) (hag : ∀ d, min (p d) h = min (q d) h) :
    ∃ k, 0 < k ∧ k ≤ Fintype.card X + 1 ∧
      FiniteProfileControllers.Agree (fieldRank p) (fieldRank q) k ∧
      h ≤ level (values p) C k ∧ h ≤ level (values q) C k ∧
      ∀ i, i < k → level (values p) C i = level (values q) C i := by
  have hs := values_agree_below hag
  have hn : next (values p) h = next (values q) h :=
    congrArg (fun s : Finset ExtOrd => s.card + 1) (below_eq hs)
  refine ⟨next (values p) h, by unfold next; omega,
    (next_le _ _).trans (Nat.add_le_add_right (values_card_le p) 1),
    fieldRank_agreement hh hag, level_reaches _ hC, ?_, ?_⟩
  · rw [hn]
    exact level_reaches _ hC
  · exact fun _ hi => level_agree_below hs hi

variable {L : ℕ} {Q : Type*} [Finite Q] (profile : Q → X → ℕ)

/-- A selected table section. The anchor's ranks will be identified with
the ranks of the scalar input in the readback and prefix theorems. -/
def render (a : Q) (p : X → ExtOrd) (C : ExtOrd) :
    SupportLadderRows.Point L X Q → ExtOrd :=
  SupportLadderRows.image profile a (level (values p) C)

omit [Finite Q] in
/-- Scalar prefixes determine every physical rung and shadow cap, even
when the profiles reorder or split ties above the cap. -/
theorem render_cap_agreement {a b : Q} {p q : X → ExtOrd} {C h : ExtOrd}
    (hL : Fintype.card X + 1 ≤ L)
    (ha : ∀ d, profile a d = fieldRank p d) (hb : ∀ d, profile b d = fieldRank q d)
    (hp : ∀ d, p d ≤ C) (hq : ∀ d, q d ≤ C) (hC : h ≤ C)
    (hag : ∀ d, min (p d) h = min (q d) h) (v : SupportLadderRows.Point L X Q) :
    min (render profile a p C v) h = min (render profile b q C v) h := by
  by_cases hz : h = ⊥
  · simp_all
  · obtain ⟨k, _, hk, hr, hkp, hkq, he⟩ := common_rank_cut (bot_lt_iff_ne_bot.mpr hz) hC hag
    have hcut : k ≤ FiniteProfileControllers.cut L (profile a) (profile b) := by
      apply FiniteProfileControllers.le_cut (hk.trans hL)
      intro d
      rw [ha d, hb d]
      tauto
    exact SupportLadderRows.cap_agreement a b hcut (level (values p) C) (level (values q) C)
      (level_mono (values_bound hp)) (level_mono (values_bound hq)) hkp hkq
      (by grind) v

end

end VaughtConjecture.Knight.LadderScalarRendering
