module

public import Chazelle.Core.ShootCutWalk

/-!
# WP-G, part 8: breakpoints of the walk of a host chain

The main loop of the arc-cutter walks the double boundary of a host chain `C` in stretches: a
stretch stops where the tour turns (chain index `0` or `m`), where the host item changes, or where
the index of `Q` wraps (`0` or `n - 1`).  These **breakpoints** are few: at most `2 + 2 · 4 |H|`
among the tour positions (`card_brk_le`), so the loop makes `O(|H|)` iterations.

* `HostBreak n H u`: the host point `u` is a point item, the first or last point of a run, or a
  run point with index `0` or `n - 1` of `Q`;
* `card_hostBreak_le`: at most `4 |H|` host points are breaks;
* `uOf C i`: the host point at tour position `i`; at most two tour positions share one
  (`card_fiber_le`);
* `card_brk_le`: at most `2 + 8 |H|` tour positions `i < 2m` are breaks.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (sideE)

namespace ShootCut

/-- The host point `u` is a break: a point item, the first or last point of a run, or a run
point whose vertex of `Q` has index `0` or `n - 1`. -/
def HostBreak (n : ℕ) (H : Host) (u : ℕ) : Prop :=
  ∃ r, r < H.length ∧ NFLoc.preLen n H r ≤ u ∧ u < NFLoc.preLen n H (r + 1) ∧
    match H.getD r (.run 0 0) with
    | .pt _ => True
    | .run a ℓ => u - NFLoc.preLen n H r = 0 ∨ u - NFLoc.preLen n H r = ℓ ∨
        (a + (u - NFLoc.preLen n H r)) % n = 0 ∨ (a + (u - NFLoc.preLen n H r)) % n = n - 1

noncomputable instance (n : ℕ) (H : Host) : DecidablePred (HostBreak n H) :=
  Classical.decPred _

/-- The (at most four) break offsets of an item. -/
def brkOffs (n : ℕ) : HostItem → Finset ℕ
  | .pt _ => {0}
  | .run a ℓ => {0, ℓ, (n - a % n) % n, (2 * n - 1 - a % n) % n}

theorem card_brkOffs (n : ℕ) (it : HostItem) : (brkOffs n it).card ≤ 4 := by
  cases it with
  | pt x => simp [brkOffs]
  | run a ℓ =>
    unfold brkOffs
    refine (Finset.card_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
    simp

/-- All break host points. -/
def brkSet (n : ℕ) (H : Host) : Finset ℕ :=
  (Finset.range H.length).biUnion fun r =>
    (brkOffs n (H.getD r (.run 0 0))).image fun t => NFLoc.preLen n H r + t

theorem card_brkSet (n : ℕ) (H : Host) : (brkSet n H).card ≤ 4 * H.length := by
  unfold brkSet
  refine Finset.card_biUnion_le.trans ?_
  calc ∑ r ∈ Finset.range H.length,
        ((brkOffs n (H.getD r (.run 0 0))).image fun t => NFLoc.preLen n H r + t).card
      ≤ ∑ _r ∈ Finset.range H.length, 4 :=
        Finset.sum_le_sum fun r _ => Finset.card_image_le.trans (card_brkOffs n _)
    _ = 4 * H.length := by simp [mul_comm]

/-- The unique offset in `[0, n)` with a given residue. -/
theorem off_of_mod {n a t c : ℕ} (hn : 0 < n) (ht : t < n) (_hc : c < n) (h : (a + t) % n = c) :
    t = (n + c - a % n) % n := by
  have e := Nat.div_add_mod a n
  have e2 := Nat.div_add_mod (a + t) n
  have ha := Nat.mod_lt a hn
  rw [h] at e2
  -- `a % n + t ≡ c`
  have h2 : (a % n + t) % n = c := by rw [← h, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rcases (show a % n + t < n ∨ n ≤ a % n + t by omega) with h3 | h3
  · rw [Nat.mod_eq_of_lt h3] at h2
    rw [show n + c - a % n = t + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt ht]
  · rw [Nat.mod_eq_sub_mod h3, Nat.mod_eq_of_lt (by omega)] at h2
    rw [show n + c - a % n = t by omega, Nat.mod_eq_of_lt ht]

/-- **Break host points lie in `brkSet`** (for well-formed hosts: runs shorter than `n`). -/
theorem hostBreak_mem {n : ℕ} {H : Host} (hn : 0 < n) (hwf : HostWF n H) {u : ℕ}
    (h : HostBreak n H u) : u ∈ brkSet n H := by
  obtain ⟨r, hr, h1, h2, hc⟩ := h
  unfold brkSet
  refine Finset.mem_biUnion.2 ⟨r, Finset.mem_range.2 hr, Finset.mem_image.2 ?_⟩
  refine ⟨u - NFLoc.preLen n H r, ?_, by omega⟩
  have hsucc := NFLoc.preLen_succ n H hr
  have hget : H.getD r (.run 0 0) = H[r] := by simp [List.getD_eq_getElem?_getD, hr]
  rw [hget] at hc ⊢
  have hit := hwf H[r] (List.getElem_mem hr)
  generalize H[r] = it at hc hsucc hit
  cases it with
  | pt x =>
    simp only [NFLoc.itemCnt] at hsucc
    simp only [brkOffs, Finset.mem_singleton]
    omega
  | run a ℓ =>
    simp only [NFLoc.itemCnt] at hsucc
    simp only at hit
    have ht : u - NFLoc.preLen n H r < n := by omega
    simp only [brkOffs, Finset.mem_insert, Finset.mem_singleton]
    rcases hc with hc | hc | hc | hc
    · exact Or.inl hc
    · exact Or.inr (Or.inl hc)
    · right; right; left
      rw [off_of_mod hn ht hn hc, Nat.add_zero]
    · right; right; right
      rw [off_of_mod hn ht (by omega) hc]
      congr 1
      omega

theorem card_hostBreak_le {n : ℕ} {H : Host} (hn : 0 < n) (hwf : HostWF n H) (N : ℕ) :
    ((Finset.range N).filter (HostBreak n H)).card ≤ 4 * H.length := by
  classical
  refine le_trans (Finset.card_le_card fun u hu => ?_) (card_brkSet n H)
  exact hostBreak_mem hn hwf (Finset.mem_filter.1 hu).2

/-! ## Tour positions -/

variable (C : Chain)

/-- The host point index of tour position `i`. -/
noncomputable def uOf (i : ℕ) : ℕ := (C.s + sideE C.m (tJ C i)) % C.P.n

theorem uOf_lt (i : ℕ) : uOf C i < C.P.n := Nat.mod_lt _ C.n_pos

/-- The tour coordinate is injective on the tour positions. -/
theorem tJ_inj {i i' : ℕ} (hi : i < 2 * C.m) (hi' : i' < 2 * C.m) (h : tJ C i = tJ C i') :
    i = i' := by
  unfold tJ at h
  have hS := C.sideS_lt C.sideBeta
  rcases (show C.sideS C.sideBeta + i < 2 * C.m ∨ 2 * C.m ≤ C.sideS C.sideBeta + i by omega)
    with h1 | h1 <;>
  rcases (show C.sideS C.sideBeta + i' < 2 * C.m ∨ 2 * C.m ≤ C.sideS C.sideBeta + i' by omega)
    with h2 | h2
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h; omega
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_sub_mod h2, Nat.mod_eq_of_lt (by omega)] at h; omega
  · rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt h2] at h; omega
  · rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_sub_mod h2,
      Nat.mod_eq_of_lt (by omega)] at h; omega

/-- At most one tour position has a given tour coordinate. -/
theorem card_tJ_eq (j : ℕ) : ((Finset.range (2 * C.m)).filter fun i => tJ C i = j).card ≤ 1 := by
  refine Finset.card_le_one.2 fun i hi i' hi' => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hi hi'
  exact tJ_inj C hi.1 hi'.1 (hi.2.trans hi'.2.symm)

/-- **At most two tour positions share a host point.** -/
theorem card_fiber_le (u : ℕ) :
    ((Finset.range (2 * C.m)).filter fun i => uOf C i = u).card ≤ 2 := by
  classical
  -- the chain index is determined by the host point
  have hk : ∀ i i', uOf C i = uOf C i' → sideE C.m (tJ C i) = sideE C.m (tJ C i') := by
    intro i i' h
    unfold uOf at h
    have h1 := Chazelle.Chain.sideE_le (m := C.m) (j := tJ C i) (tJ_lt C i).le
    have h2 := Chazelle.Chain.sideE_le (m := C.m) (j := tJ C i') (tJ_lt C i').le
    have hm := C.m_lt
    have e1 := Nat.div_add_mod (C.s + sideE C.m (tJ C i)) C.P.n
    have e2 := Nat.div_add_mod (C.s + sideE C.m (tJ C i')) C.P.n
    rw [h] at e1
    rcases le_total (C.s + sideE C.m (tJ C i')) (C.s + sideE C.m (tJ C i)) with hle | hle
    · obtain ⟨q, hq⟩ := (Nat.modEq_iff_dvd' hle).1 (by unfold Nat.ModEq; exact h.symm)
      have hq0 : q = 0 := by
        by_contra h0
        have : C.P.n ≤ C.P.n * q := Nat.le_mul_of_pos_right _ (by omega)
        omega
      subst hq0; omega
    · obtain ⟨q, hq⟩ := (Nat.modEq_iff_dvd' hle).1 (by unfold Nat.ModEq; exact h)
      have hq0 : q = 0 := by
        by_contra h0
        have : C.P.n ≤ C.P.n * q := Nat.le_mul_of_pos_right _ (by omega)
        omega
      subst hq0; omega
  refine le_trans (Finset.card_le_card (t := ((Finset.range (2 * C.m)).filter fun i =>
      tJ C i = sideE C.m (tJ C (Classical.epsilon fun i => i < 2 * C.m ∧ uOf C i = u))) ∪
    ((Finset.range (2 * C.m)).filter fun i =>
      tJ C i = 2 * C.m - sideE C.m (tJ C (Classical.epsilon fun i => i < 2 * C.m ∧ uOf C i = u))))
    ?_) ((Finset.card_union_le _ _).trans (by
      have := card_tJ_eq C (sideE C.m (tJ C (Classical.epsilon fun i => i < 2 * C.m ∧ uOf C i = u)))
      have := card_tJ_eq C (2 * C.m -
        sideE C.m (tJ C (Classical.epsilon fun i => i < 2 * C.m ∧ uOf C i = u)))
      omega))
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_range] at hi
  have hex : ∃ i, i < 2 * C.m ∧ uOf C i = u := ⟨i, hi.1, hi.2⟩
  have hsp := Classical.epsilon_spec hex
  have hki := hk _ _ (hi.2.trans hsp.2.symm)
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range]
  have hlt := tJ_lt C i
  unfold sideE at hki
  split_ifs at hki with h1 h2 h2
  · left; exact ⟨hi.1, by unfold sideE; rw [ite_eq_left h2]; exact hki⟩
  · left; exact ⟨hi.1, by unfold sideE; rw [ite_eq_right h2]; exact hki⟩
  · right; refine ⟨hi.1, ?_⟩; unfold sideE; rw [ite_eq_left h2]; omega
  · right; refine ⟨hi.1, ?_⟩; unfold sideE; rw [ite_eq_right h2]; omega

/-- **Few tour positions are breaks**: turns of the tour or break host points. -/
theorem card_brk_le {n : ℕ} {H : Host} (hn : 0 < n) (hwf : HostWF n H) :
    ((Finset.range (2 * C.m)).filter fun i =>
      tJ C i = 0 ∨ tJ C i = C.m ∨ HostBreak n H (uOf C i)).card ≤ 2 + 8 * H.length := by
  classical
  have e : ((Finset.range (2 * C.m)).filter fun i =>
      tJ C i = 0 ∨ tJ C i = C.m ∨ HostBreak n H (uOf C i)) ⊆
      ((Finset.range (2 * C.m)).filter fun i => tJ C i = 0) ∪
      (((Finset.range (2 * C.m)).filter fun i => tJ C i = C.m) ∪
      ((Finset.range (2 * C.m)).filter fun i => HostBreak n H (uOf C i))) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_union] at hi ⊢
    rcases hi.2 with h | h | h
    · exact Or.inl ⟨hi.1, h⟩
    · exact Or.inr (Or.inl ⟨hi.1, h⟩)
    · exact Or.inr (Or.inr ⟨hi.1, h⟩)
  have hA := card_tJ_eq C 0
  have hB := card_tJ_eq C C.m
  have hC : ((Finset.range (2 * C.m)).filter fun i => HostBreak n H (uOf C i)).card ≤
      2 * (((Finset.range (2 * C.m)).filter fun i => HostBreak n H (uOf C i)).image
        (uOf C)).card :=
    Finset.card_le_mul_card_image (f := uOf C) _ 2 fun u _ => by
      refine le_trans (Finset.card_le_card ?_) (card_fiber_le C u)
      intro i hi
      simp only [Finset.mem_filter] at hi ⊢
      exact ⟨hi.1.1, hi.2⟩
  have hI : (((Finset.range (2 * C.m)).filter fun i => HostBreak n H (uOf C i)).image
      (uOf C)).card ≤ 4 * H.length := by
    refine le_trans (Finset.card_le_card fun u hu => ?_) (card_hostBreak_le hn hwf C.P.n)
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hu
    simp only [Finset.mem_filter] at hi ⊢
    exact ⟨Finset.mem_range.2 (uOf_lt C i), hi.2⟩
  have hU1 := Finset.card_union_le ((Finset.range (2 * C.m)).filter fun i => tJ C i = 0)
    (((Finset.range (2 * C.m)).filter fun i => tJ C i = C.m) ∪
      ((Finset.range (2 * C.m)).filter fun i => HostBreak n H (uOf C i)))
  have hU2 := Finset.card_union_le ((Finset.range (2 * C.m)).filter fun i => tJ C i = C.m)
    ((Finset.range (2 * C.m)).filter fun i => HostBreak n H (uOf C i))
  have := Finset.card_le_card e
  omega

end ShootCut

end

end Chazelle.Core
