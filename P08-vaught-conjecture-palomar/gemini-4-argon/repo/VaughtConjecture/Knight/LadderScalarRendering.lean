/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SupportLadderRows
public import VaughtConjecture.Knight.Domain
public import VaughtConjecture.AmalgamationPlan.Plan

/-! # Ceiling-filled scalar rendering for the support ladder

The distinct positive field values determine their ranks and all occupied
rung values. Every unused positive rung reads the supplied ceiling. The
common rank cut is constructed from the values strictly below the external
cap; it is not an extra receipt assumed of the physical source.

This is the grade-one base of new16's renderer. It does not construct the
higher semantic rows or claim bountifulness of a receiving scheme.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.LadderScalarRendering

open Transform Value ExtOrd

open Classical in
/-- One-based rank on a finite set of positive values. -/
def rank (S : Finset ExtOrd) (x : ExtOrd) : ℕ := (S.filter (· ≤ x)).card

open Classical in
/-- The occupied initial segment followed by the constant ceiling tail. -/
def level (S : Finset ExtOrd) (C : ExtOrd) (i : ℕ) : ExtOrd :=
  if S.card < i then C else (S.filter (fun x => rank S x ≤ i)).sup id

theorem rank_le_card (S : Finset ExtOrd) (x : ExtOrd) : rank S x ≤ S.card := by
  classical exact Finset.card_le_card (Finset.filter_subset _ _)

theorem rank_mono (S : Finset ExtOrd) : Monotone (rank S) := fun _ _ hxy => by
  classical
  exact Finset.card_le_card fun _ hz => Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2.trans hxy⟩

theorem rank_strict {S : Finset ExtOrd} {x y : ExtOrd} (hy : y ∈ S) (hxy : x < y) :
    rank S x < rank S y := by
  classical
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun z hz => Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2.trans hxy.le⟩).mpr
    ⟨y, Finset.mem_filter.mpr ⟨hy, le_rfl⟩, fun hm => hxy.not_ge (Finset.mem_filter.mp hm).2⟩)

theorem rank_pos {S : Finset ExtOrd} {x : ExtOrd} (hx : x ∈ S) : 0 < rank S x := by
  classical exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, le_rfl⟩⟩

theorem rank_bot {S : Finset ExtOrd} (hS : ⊥ ∉ S) : rank S ⊥ = 0 := by
  classical
  refine Finset.card_eq_zero.mpr (Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_)
  obtain ⟨hxS, hx⟩ := Finset.mem_filter.mp hx
  exact hS ((le_bot_iff.mp hx) ▸ hxS)

theorem level_zero (S : Finset ExtOrd) (C : ExtOrd) : level S C 0 = ⊥ := by
  classical
  rw [level, ite_eq_right (by omega)]
  exact le_bot_iff.mp (Finset.sup_le fun x hx =>
    absurd (Finset.mem_filter.mp hx).2 (not_le_of_gt (rank_pos (Finset.mem_filter.mp hx).1)))

theorem level_rank {S : Finset ExtOrd} {x : ExtOrd} (hx : x ∈ S) (C : ExtOrd) :
    level S C (rank S x) = x := by
  classical
  rw [level, ite_eq_right (not_lt.mpr (rank_le_card S x))]
  refine le_antisymm (Finset.sup_le fun y hy => not_lt.mp fun hn =>
    (rank_strict (Finset.mem_filter.mp hy).1 hn).not_ge (Finset.mem_filter.mp hy).2)
    (Finset.le_sup (f := id) (Finset.mem_filter.mpr ⟨hx, le_rfl⟩))

theorem level_le {S : Finset ExtOrd} {C : ExtOrd} (hC : ∀ x ∈ S, x ≤ C) (i : ℕ) :
    level S C i ≤ C := by
  classical
  unfold level; split_ifs
  · exact le_rfl
  · exact Finset.sup_le fun x hx => hC x (Finset.mem_filter.mp hx).1

theorem level_mono {S : Finset ExtOrd} {C : ExtOrd} (hC : ∀ x ∈ S, x ≤ C) :
    Monotone (level S C) := by
  classical
  intro i k hik
  by_cases hk : S.card < k
  · rw [show level S C k = C from ite_eq_left hk]; exact level_le hC i
  · rw [level, ite_eq_right (by omega : ¬S.card < i), level, ite_eq_right hk]
    exact Finset.sup_le fun x hx => Finset.le_sup (f := id) (Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2.trans hik⟩)

theorem level_supported (S : Finset ExtOrd) (C : ExtOrd) (i : ℕ) :
    level S C i = ⊥ ∨ level S C i ∈ S ∨ level S C i = C := by
  classical
  unfold level; split_ifs
  · exact Or.inr (Or.inr rfl)
  · by_cases hn : (S.filter fun x => rank S x ≤ i).Nonempty
    · obtain ⟨x, hx, he⟩ := Finset.sup_mem_of_nonempty (f := id) hn
      exact Or.inr (Or.inl (he ▸ (Finset.mem_filter.mp hx).1))
    · rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sup_empty]
      exact Or.inl rfl

theorem level_pos {S : Finset ExtOrd} {C : ExtOrd} (hS : ⊥ ∉ S)
    (hC : ∀ x ∈ S, x ≤ C) (hpos : C ≠ ⊥) {i : ℕ} (hi : 0 < i) :
    level S C i ≠ ⊥ := by
  classical
  by_cases hn : S.Nonempty
  · have hm := Finset.min'_mem S hn
    have hr : rank S (S.min' hn) ≤ i :=
      ((Finset.card_le_card fun x hx => Finset.mem_singleton.mpr
        (le_antisymm (Finset.mem_filter.mp hx).2
          (Finset.min'_le S x (Finset.mem_filter.mp hx).1))).trans_eq
        (Finset.card_singleton _)).trans hi
    have hle : S.min' hn ≤ level S C i := by
      rw [← level_rank hm C]; exact level_mono hC hr
    exact fun hz => hS (le_bot_iff.mp (hle.trans_eq hz) ▸ hm)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn, level, Finset.card_empty, ite_eq_left hi]
    exact hpos

open Classical in
/-- One more than the number of occupied values strictly below a cap. -/
def next (S : Finset ExtOrd) (h : ExtOrd) : ℕ := (S.filter (· < h)).card + 1

theorem rank_lt_next {S : Finset ExtOrd} {x h : ExtOrd} (hx : x ∈ S) :
    rank S x < next S h ↔ x < h := by
  classical
  refine ⟨fun hr => not_le.mp fun hn => ?_, fun hxh => Nat.lt_succ_of_le (Finset.card_le_card
    fun y hy => Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1,
      (Finset.mem_filter.mp hy).2.trans_lt hxh⟩)⟩
  have hsub : S.filter (· < h) ⊂ S.filter (· ≤ x) :=
    (Finset.ssubset_iff_of_subset fun y hy => Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hy).1, (Finset.mem_filter.mp hy).2.le.trans hn⟩).mpr
      ⟨x, Finset.mem_filter.mpr ⟨hx, le_rfl⟩, fun hm => hn.not_gt (Finset.mem_filter.mp hm).2⟩
  have hc := Finset.card_lt_card hsub
  dsimp only [rank, next] at hr; omega

theorem rank_congr_below {S T : Finset ExtOrd} {h x : ExtOrd}
    (hst : ∀ y, y < h → (y ∈ S ↔ y ∈ T)) (hx : x < h) : rank S x = rank T x := by
  classical
  unfold rank; congr 1; ext y
  simp only [Finset.mem_filter]
  exact and_congr_left fun hy => hst y (hy.trans_lt hx)

theorem level_reaches (S : Finset ExtOrd) {C h : ExtOrd} (hh : h ≤ C) :
    h ≤ level S C (next S h) := by
  classical
  by_cases hc : S.card < next S h
  · rw [level, ite_eq_left hc]; exact hh
  · have hn : (S.filter (h ≤ ·)).Nonempty := by
      by_contra hn
      have he : S.filter (· < h) = S := Finset.filter_eq_self.mpr fun x hx =>
        not_le.mp fun hnx => hn ⟨x, Finset.mem_filter.mpr ⟨hx, hnx⟩⟩
      simp only [next, he] at hc; omega
    let x := (S.filter (h ≤ ·)).min' hn
    obtain ⟨hxS, hxh⟩ := Finset.mem_filter.mp (Finset.min'_mem (S.filter (h ≤ ·)) hn)
    have he : S.filter (· ≤ x) = insert x (S.filter (· < h)) := by
      ext y; rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_filter]
      exact ⟨fun ⟨hyS, hyx⟩ => (lt_or_ge y h).elim (fun hyh => Or.inr ⟨hyS, hyh⟩)
          fun hyh => Or.inl (le_antisymm hyx (Finset.min'_le _ y (Finset.mem_filter.mpr ⟨hyS, hyh⟩))),
        fun h => h.elim (fun hy => ⟨hy ▸ hxS, hy.le⟩) fun ⟨hyS, hyh⟩ => ⟨hyS, hyh.le.trans hxh⟩⟩
    have hr : rank S x = next S h := by
      rw [rank, he, Finset.card_insert_of_notMem]
      · rfl
      · exact fun hx => not_lt.mpr hxh (Finset.mem_filter.mp hx).2
    rw [← hr, level_rank hxS]; exact hxh

variable {X : Type*} [Fintype X]

open Classical in
def values (p : X → ExtOrd) : Finset ExtOrd := (Finset.univ.image p).erase ⊥

theorem mem_values {p : X → ExtOrd} {x : ExtOrd} :
    x ∈ values p ↔ x ≠ ⊥ ∧ ∃ d, p d = x := by
  classical simp only [values, Finset.mem_erase, Finset.mem_image, Finset.mem_univ, true_and]

theorem bot_not_values (p : X → ExtOrd) : ⊥ ∉ values p := by
  simp [mem_values]

theorem values_card_le (p : X → ExtOrd) : (values p).card ≤ Fintype.card X := by
  classical
  exact (Finset.card_le_card (Finset.erase_subset _ _)).trans
    (Finset.card_image_le.trans_eq Finset.card_univ)

def fieldRank (p : X → ExtOrd) (d : X) : ℕ := rank (values p) (p d)

theorem fieldRank_le (p : X → ExtOrd) (d : X) : fieldRank p d ≤ Fintype.card X :=
  (rank_le_card _ _).trans (values_card_le p)

theorem field_readback (p : X → ExtOrd) (C : ExtOrd) (d : X) :
    level (values p) C (fieldRank p d) = p d := by
  by_cases hz : p d = ⊥
  · simp only [fieldRank, hz, rank_bot (bot_not_values p), level_zero]
  · exact level_rank (mem_values.mpr ⟨hz, d, rfl⟩) C

theorem values_bound {p : X → ExtOrd} {C : ExtOrd} (hC : ∀ d, p d ≤ C) :
    ∀ x ∈ values p, x ≤ C := by
  intro x hx; obtain ⟨_, d, rfl⟩ := mem_values.mp hx; exact hC d

theorem level_visible {p : X → ExtOrd} {C : ExtOrd} (hp : ∀ d, SelfVis 1 (p d))
    (hC : SelfVis 1 C) (i : ℕ) : SelfVis 1 (level (values p) C i) := by
  rcases level_supported (values p) C i with hz | hv | hc
  · rw [hz]; exact selfVis_bot 1
  · obtain ⟨_, d, hd⟩ := mem_values.mp hv; exact hd ▸ hp d
  · rw [hc]; exact hC

private theorem eq_of_capped_lt {x y h : ExtOrd} (he : min x h = min y h) (hx : x < h) :
    x = y := by
  have hy : y < h := not_le.mp fun hn => hx.ne (by rwa [min_eq_left hx.le, min_eq_right hn] at he)
  simpa only [min_eq_left hx.le, min_eq_left hy.le] using he

theorem values_agree_below {p q : X → ExtOrd} {h : ExtOrd}
    (hag : ∀ d, min (p d) h = min (q d) h) :
    ∀ x, x < h → (x ∈ values p ↔ x ∈ values q) := fun x hx => by
  rw [mem_values, mem_values]
  exact ⟨fun ⟨hz, d, hd⟩ => ⟨hz, d, (eq_of_capped_lt (hag d) (hd ▸ hx)).symm.trans hd⟩,
    fun ⟨hz, d, hd⟩ => ⟨hz, d, (eq_of_capped_lt (hag d).symm (hd ▸ hx)).symm.trans hd⟩⟩

/-- Capped scalar agreement constructs the common rank prefix. -/
theorem fieldRank_agreement {p q : X → ExtOrd} {h : ExtOrd} (hh : ⊥ < h)
    (hag : ∀ d, min (p d) h = min (q d) h) :
    FiniteProfileControllers.Agree (fieldRank p) (fieldRank q) (next (values p) h) := by
  classical
  have hs := values_agree_below hag
  have hn : next (values p) h = next (values q) h := by
    unfold next; congr 2; ext y; simp only [Finset.mem_filter]; exact and_congr_left (hs y)
  intro d
  by_cases hd : p d < h
  · exact congrArg (fun n => min n (next (values p) h))
      ((rank_congr_below hs hd).trans
        (congrArg (rank (values q)) (eq_of_capped_lt (hag d) hd)))
  · have hph : h ≤ p d := not_lt.mp hd
    have hqh : h ≤ q d := by
      have he := hag d; rw [min_eq_right hph] at he; exact he.le.trans (min_le_left _ _)
    have hpv : p d ∈ values p := mem_values.mpr ⟨ne_of_gt (hh.trans_le hph), d, rfl⟩
    have hqv : q d ∈ values q := mem_values.mpr ⟨ne_of_gt (hh.trans_le hqh), d, rfl⟩
    have hpr : next (values p) h ≤ fieldRank p d :=
      not_lt.mp fun hr => hd ((rank_lt_next hpv).mp hr)
    have hqr : next (values p) h ≤ fieldRank q d :=
      hn ▸ not_lt.mp fun hr => hqh.not_gt ((rank_lt_next hqv).mp hr)
    rw [min_eq_right hpr, min_eq_right hqr]

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
  classical
  by_cases hz : h = ⊥
  · simp only [hz, min_eq_right bot_le]
  · have hs := values_agree_below hag
    let k := next (values p) h
    have hn : k = next (values q) h := by
      unfold k next; congr 2; ext y; simp only [Finset.mem_filter]; exact and_congr_left (hs y)
    have hkS (r : X → ExtOrd) : next (values r) h ≤ (values r).card + 1 :=
      Nat.add_le_add_right (Finset.card_le_card (Finset.filter_subset _ _)) 1
    have hcut : k ≤ FiniteProfileControllers.cut L (profile a) (profile b) := by
      refine FiniteProfileControllers.le_cut
        (((hkS p).trans (Nat.add_le_add_right (values_card_le p) 1)).trans hL) fun d => ?_
      rw [ha d, hb d]
      exact fieldRank_agreement (bot_lt_iff_ne_bot.mpr hz) hag d
    refine SupportLadderRows.cap_agreement a b hcut (level (values p) C) (level (values q) C)
      (level_mono (values_bound hp)) (level_mono (values_bound hq)) (level_reaches _ hC)
      (hn ▸ level_reaches _ hC) (fun i hi => ?_) v
    have hiP : ¬(values p).card < i := by have := hkS p; omega
    have hiQ : ¬(values q).card < i := by have := hkS q; omega
    have heq : level (values p) C i = level (values q) C i := by
      rw [level, ite_eq_right hiP, level, ite_eq_right hiQ]
      congr 1; ext x; rw [Finset.mem_filter, Finset.mem_filter]
      exact ⟨fun ⟨hxP, hr⟩ => by
          have hxh := (rank_lt_next hxP).mp (hr.trans_lt hi)
          exact ⟨(hs x hxh).mp hxP, rank_congr_below hs hxh ▸ hr⟩,
        fun ⟨hxQ, hr⟩ => by
          have hxh := (rank_lt_next hxQ).mp (hr.trans_lt (hn ▸ hi))
          exact ⟨(hs x hxh).mpr hxQ, (rank_congr_below hs hxh).symm ▸ hr⟩⟩
    rw [heq]

