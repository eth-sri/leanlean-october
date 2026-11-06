module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.GranNF

/-!
# WP-F, part 5: the ring of live cut positions

The granularity procedure keeps the cuts of the current submap as a doubly linked cyclic list of
positions of the sequence table (the positions whose start key is still a cut).  This file
proves the combinatorics of that list with cyclic betweenness on positions (`cyc a b i`, the
cyclic interval of `ℕ` read in `ℝ`):

* `RingOK Lv A nxt prv`: `nxt`/`prv` are the cyclic successor/predecessor among the live
  positions `Lv`;
* `ringOK_unlink`: deleting a live position (`nxt (prv d) := nxt d`, `prv (nxt d) := prv d`)
  keeps `RingOK` on the remaining positions, if at least two remain;
* `IsPredIn`/`IsSuccIn`: the neighbours of a dead position among live ones, `gap_of_pred_succ`:
  they bound a gap containing it;
* `sideInArc_mono_iff`: for strictly increasing keys, cyclic betweenness of positions is cyclic
  betweenness of keys.
-/

namespace Chazelle.Core

namespace Gran

@[expose] public section

open Set
open Chazelle.Chain (sideInArc)

/-- Cyclic betweenness of positions. -/
def cyc (a b i : ℕ) : Prop := sideInArc (a : ℝ) b i

/-! ## Cyclic facts on reals -/

section
variable {l r x y : ℝ} (hx : sideInArc l r x)
include hx
theorem cyc_sub_mid (hy : sideInArc l x y) :
    sideInArc l r y := by
  core_grind

theorem cyc_sub_mid' (hy : sideInArc x r y) :
    sideInArc l r y := by
  core_grind


end

theorem cyc_end_eq {a b b' : ℝ} (hb : a ≠ b) (hb' : a ≠ b') (h1 : ¬ sideInArc a b b')
    (h2 : ¬ sideInArc a b' b) : b = b' := by
  core_grind

theorem cyc_start_eq' {a a' b : ℝ} (ha : a ≠ b) (ha' : a' ≠ b) (h1 : ¬ sideInArc a b a')
    (h2 : ¬ sideInArc a' b a) : a = a' := Chazelle.Core.cyc_start_eq ha ha' h1 h2

/-- For three distinct keys, `m` is between `a` and `b` or `b` is between `a` and `m`. -/
theorem cyc_three {a b m : ℝ} (hab : a ≠ b) (ham : a ≠ m) (hbm : b ≠ m) :
    sideInArc a b m ∨ sideInArc a m b := by
  by_cases h : sideInArc a b m
  · simp_all
  · exact Or.inr (NFLoc.sideInArc_swap hab ham hbm h)

/-- Everything but `a` lies in `(a, m)`, is `m`, or lies in `(m, a)`. -/
theorem cyc_cover {a m x : ℝ} (ham : a ≠ m) (hx : x ≠ a) :
    sideInArc a m x ∨ x = m ∨ sideInArc m a x := by
  core_grind

/-! ## Transfer along strictly increasing keys -/

/-- **Cyclic betweenness transfers along strictly increasing keys.** -/
theorem sideInArc_mono_iff {f : ℕ → ℝ} {A : ℕ}
    (hf : ∀ i i', i < i' → i' < A → f i < f i') {a b i : ℕ} (ha : a < A) (hb : b < A)
    (hi : i < A) : sideInArc (f a) (f b) (f i) ↔ cyc a b i := by
  have key : ∀ x y, x < A → y < A → (f x < f y ↔ x < y) := by
    intro x y hx hy
    constructor
    · intro h
      by_contra h'
      rcases lt_or_eq_of_le (not_lt.1 h') with h'' | h''
      all_goals grind
    simp_all
  grind [cyc, sideInArc, Nat.cast_lt]

/-! ## The ring -/

section
variable (Lv : ℕ → Prop)
include Lv
/-- **The ring invariant**: for every live position `j < A`, `nxt j` is the next live position
cyclically and `prv j` the previous one. -/
def RingOK (A : ℕ) (nxt prv : ℕ → ℕ) : Prop :=
  ∀ j, j < A → Lv j →
    (nxt j < A ∧ Lv (nxt j) ∧ nxt j ≠ j ∧ ∀ i, i < A → Lv i → ¬ cyc j (nxt j) i) ∧
    (prv j < A ∧ Lv (prv j) ∧ prv j ≠ j ∧ ∀ i, i < A → Lv i → ¬ cyc (prv j) j i)

/-- `p` is the live predecessor of `n` (which need not be live). -/
def IsPredIn (A n p : ℕ) : Prop :=
  p < A ∧ Lv p ∧ p ≠ n ∧ ∀ i, i < A → Lv i → ¬ cyc p n i

/-- `s` is the live successor of `n`. -/
def IsSuccIn (A n s : ℕ) : Prop :=
  s < A ∧ Lv s ∧ s ≠ n ∧ ∀ i, i < A → Lv i → ¬ cyc n s i


end

theorem natCast_ne {a b : ℕ} (h : a ≠ b) : (a : ℝ) ≠ b := by simp_all

section
variable {Lv : ℕ → Prop}
/-- Predecessors are unique. -/
theorem pred_unique {A n p p' : ℕ} (h : IsPredIn Lv A n p)
    (h' : IsPredIn Lv A n p') : p = p' := by
  have := cyc_start_eq' (natCast_ne h.2.2.1) (natCast_ne h'.2.2.1)
    (h.2.2.2 p' h'.1 h'.2.1) (h'.2.2.2 p h.1 h.2.1)
  simp_all

/-- Successors are unique. -/
theorem succ_unique {A n s s' : ℕ} (h : IsSuccIn Lv A n s)
    (h' : IsSuccIn Lv A n s') : s = s' := by
  have := cyc_end_eq (natCast_ne h.2.2.1.symm) (natCast_ne h'.2.2.1.symm)
    (h.2.2.2 s' h'.1 h'.2.1) (h'.2.2.2 s h.1 h.2.1)
  simp_all


end

section
variable {Lv : ℕ → Prop} {A : ℕ} {nxt prv : ℕ → ℕ} (h : RingOK Lv A nxt prv) {j : ℕ} (hj : j < A) (hL : Lv j)
include nxt prv h hj hL
/-- In a ring, `nxt` and `prv` are the successor and predecessor. -/
theorem RingOK.succ : IsSuccIn Lv A j (nxt j) := by
  obtain ⟨⟨a, b, c, d⟩, -⟩ := h j hj hL; core_grind

theorem RingOK.pred : IsPredIn Lv A j (prv j) := by
  obtain ⟨-, ⟨a, b, c, d⟩⟩ := h j hj hL; core_grind


end

section
variable {Lv : ℕ → Prop}
/-- **The neighbours of a position bound a gap containing it**: if `p` and `s` are the live
predecessor and successor of a non-live `n` and differ, then `n` lies strictly between them and
no live position does. -/
theorem gap_of_pred_succ {A n p s : ℕ} (hn : n < A) (hnL : ¬ Lv n)
    (hp : IsPredIn Lv A n p) (hs : IsSuccIn Lv A n s) (hps : p ≠ s) :
    cyc p s n ∧ ∀ i, i < A → Lv i → ¬ cyc p s i := by
  have h1 : cyc p s n := by
    rcases cyc_three (natCast_ne hps) (natCast_ne hp.2.2.1) (natCast_ne hs.2.2.1) with h | h
    · exact h
    · exact absurd h (hp.2.2.2 s hs.1 hs.2.1)
  refine ⟨h1, fun i hi hiL hin => ?_⟩
  rcases sideInArc_split hin h1 with h | h | h
  · exact hp.2.2.2 i hi hiL h
  · simp_all
  · exact hs.2.2.2 i hi hiL h

/-- If a non-live position has equal predecessor and successor, that is the only live
position. -/
theorem only_of_pred_eq_succ {A n p : ℕ} (_hn : n < A) (hnL : ¬ Lv n)
    (hp : IsPredIn Lv A n p) (hs : IsSuccIn Lv A n p) {i : ℕ} (hi : i < A) (hiL : Lv i) :
    i = p := by
  by_contra hip
  have hin : i ≠ n := fun e => hnL (e ▸ hiL)
  rcases cyc_cover (natCast_ne hp.2.2.1) (natCast_ne hip) with h | h | h
  · exact hp.2.2.2 i hi hiL h
  · simp_all
  · exact hs.2.2.2 i hi hiL h

/-- **Unlinking a live position** keeps the ring on the remaining live positions, provided its
two neighbours differ. -/
theorem ringOK_unlink {A : ℕ} {nxt prv : ℕ → ℕ} (h : RingOK Lv A nxt prv)
    {d : ℕ} (hd : d < A) (hdL : Lv d) (hne : prv d ≠ nxt d) :
    RingOK (fun j => Lv j ∧ j ≠ d) A (Function.update nxt (prv d) (nxt d))
      (Function.update prv (nxt d) (prv d)) := by
  obtain ⟨hs, hp⟩ := h d hd hdL
  set p := prv d
  set s := nxt d
  -- the new neighbours of `p` and `s`
  have hsp : IsSuccIn (fun j => Lv j ∧ j ≠ d) A d s :=
    ⟨hs.1, ⟨hs.2.1, hs.2.2.1⟩, hs.2.2.1, fun i hi hiL => hs.2.2.2 i hi hiL.1⟩
  have hpp : IsPredIn (fun j => Lv j ∧ j ≠ d) A d p :=
    ⟨hp.1, ⟨hp.2.1, hp.2.2.1⟩, hp.2.2.1, fun i hi hiL => hp.2.2.2 i hi hiL.1⟩
  obtain ⟨hgap1, hgap2⟩ := gap_of_pred_succ hd (fun h => h.2 rfl) hpp hsp hne
  intro j hj ⟨hjL, hjd⟩
  constructor
  · by_cases hjp : j = p
    · ram_simp <;> omega_nf
    · rw [Function.update_of_ne hjp]
      obtain ⟨a, b, c, e⟩ := (h j hj hjL).1
      have hnd : nxt j ≠ d := by
        intro hnd
        have h1 : IsPredIn Lv A d j := ⟨hj, hjL, hjd, by grind⟩
        exact hjp (pred_unique h1 (h.pred hd hdL))
      simp_all
  · by_cases hjs : j = s
    · simp_all
    · rw [Function.update_of_ne hjs]
      obtain ⟨a, b, c, e⟩ := (h j hj hjL).2
      have hpd : prv j ≠ d := by
        intro hpd
        have h1 : IsSuccIn Lv A d j := ⟨hj, hjL, hjd, by grind⟩
        exact hjs (succ_unique h1 (h.succ hd hdL))
      simp_all

/-- The ring on no live position. -/
theorem ringOK_empty {A : ℕ} (h : ∀ j, j < A → ¬ Lv j) (nxt prv : ℕ → ℕ) :
    RingOK Lv A nxt prv := fun j hj hL => absurd hL (h j hj)


end

/-- A ring is insensitive to the pointers at dead positions. -/
theorem RingOK.congr {Lv Lv' : ℕ → Prop} {A : ℕ} {nxt prv nxt' prv' : ℕ → ℕ}
    (h : RingOK Lv A nxt prv) (hL : ∀ j, j < A → (Lv' j ↔ Lv j))
    (hn : ∀ j, j < A → Lv j → nxt' j = nxt j) (hp : ∀ j, j < A → Lv j → prv' j = prv j) :
    RingOK Lv' A nxt' prv' := by
  intro j hj hjL
  have hjL' := (hL j hj).1 hjL
  obtain ⟨⟨a, b, c, e⟩, ⟨a', b', c', e'⟩⟩ := h j hj hjL'
  simp_all

/-- No position lies strictly between `j` and `j + 1`. -/
theorem not_cyc_succ (j i : ℕ) : ¬ cyc j (j + 1) i := by
  unfold cyc sideInArc
  push_cast
  rw [ite_eq_left (by linarith)]
  rintro ⟨a, b⟩
  have h1 : j < i := by simp_all
  have h2 : (i : ℝ) < ((j + 1 : ℕ) : ℝ) := by simp_all
  have h3 : i < j + 1 := by exact_mod_cast h2
  omega

/-- No position below `A` lies strictly (cyclically) between `A - 1` and `0`. -/
theorem not_cyc_wrap {A : ℕ} (hA : 1 ≤ A) {i : ℕ} (hi : i < A) : ¬ cyc (A - 1) 0 i := by
  unfold cyc sideInArc
  by_cases h : ((A - 1 : ℕ) : ℝ) < ((0 : ℕ) : ℝ)
  · simp_all
  · rw [ite_eq_right h]
    rintro (a | b)
    · have : A - 1 < i := by exact_mod_cast a
      omega
    grind

/-- **The initial ring**: all positions `< A` live, `nxt i = i + 1 mod A`, `prv i = i - 1 mod A`
(for `A ≥ 2`). -/
theorem ringOK_full {A : ℕ} (hA : 2 ≤ A) :
    RingOK (fun _ => True) A (fun i => if i + 1 < A then i + 1 else 0)
      (fun i => if 0 < i then i - 1 else A - 1) := by
  intro j hj _
  simp only
  refine ⟨⟨by grind, trivial, by grind, fun i hi _ => ?_⟩,
    ⟨by grind, trivial, by grind, fun i hi _ => ?_⟩⟩
  · by_cases h : j + 1 < A
    · rw [ite_eq_left h]; exact not_cyc_succ j i
    · rw [ite_eq_right h, show j = A - 1 by omega]; exact not_cyc_wrap (by omega) hi
  · by_cases h : 0 < j
    · rw [ite_eq_left h]
      have := not_cyc_succ (j - 1) i
      simp_all +arith
    · rw [ite_eq_right h, show j = 0 by omega]; exact not_cyc_wrap (by omega) hi

/-- **The live predecessor after deleting at most two positions** `n` and `m` (the predecessor of
`n`, skipping `prv n` if it is deleted too), provided a live position remains. -/
theorem pred_skip {Lv : ℕ → Prop} {A : ℕ} {nxt prv : ℕ → ℕ} (h : RingOK Lv A nxt prv)
    {Dd : ℕ → Prop} [DecidablePred Dd] {n m : ℕ} (hn : n < A) (hnL : Lv n) (hDn : Dd n)
    (hD : ∀ j, Dd j → j = n ∨ j = m) (hex : ∃ i, i < A ∧ Lv i ∧ ¬ Dd i) :
    IsPredIn (fun j => Lv j ∧ ¬ Dd j) A n (if Dd (prv n) then prv (prv n) else prv n) := by
  have hp := h.pred hn hnL
  set p := prv n
  by_cases hDp : Dd p
  · rw [ite_eq_left hDp]
    have hpm : p = m := (hD p hDp).resolve_left hp.2.2.1
    have hpp := h.pred hp.1 hp.2.1
    set pp := prv p
    obtain ⟨i, hi, hiL, hiD⟩ := hex
    have hin : i ≠ n := fun e => hiD (e ▸ hDn)
    have hip : i ≠ p := fun e => hiD (e ▸ hDp)
    have hppn : pp ≠ n := by
      intro e
      rcases cyc_cover (natCast_ne hp.2.2.1.symm) (natCast_ne hin) with h1 | h1 | h1
      · rw [← e] at h1; exact hpp.2.2.2 i hi hiL h1
      · simp_all
      · exact hp.2.2.2 i hi hiL h1
    have hDpp : ¬ Dd pp := by
      intro hd
      rcases hD pp hd with e | e
      · exact hppn e
      · exact hpp.2.2.1 (e.trans hpm.symm)
    have hmid : cyc pp n p := by
      rcases cyc_three (natCast_ne hppn) (natCast_ne hpp.2.2.1) (natCast_ne hp.2.2.1.symm)
        with h1 | h1
      · exact h1
      · exact absurd h1 (hpp.2.2.2 n hn hnL)
    refine ⟨hpp.1, ⟨hpp.2.1, hDpp⟩, hppn, fun j hj hjL h1 => ?_⟩
    rcases sideInArc_split h1 hmid with h2 | h2 | h2
    · exact hpp.2.2.2 j hj hjL.1 h2
    · simp_all
    · exact hp.2.2.2 j hj hjL.1 h2
  · rw [ite_eq_right hDp]
    exact ⟨hp.1, ⟨hp.2.1, hDp⟩, hp.2.2.1, fun j hj hjL => hp.2.2.2 j hj hjL.1⟩

/-- **The live successor after deleting at most two positions.** -/
theorem succ_skip {Lv : ℕ → Prop} {A : ℕ} {nxt prv : ℕ → ℕ} (h : RingOK Lv A nxt prv)
    {Dd : ℕ → Prop} [DecidablePred Dd] {n m : ℕ} (hn : n < A) (hnL : Lv n) (hDn : Dd n)
    (hD : ∀ j, Dd j → j = n ∨ j = m) (hex : ∃ i, i < A ∧ Lv i ∧ ¬ Dd i) :
    IsSuccIn (fun j => Lv j ∧ ¬ Dd j) A n (if Dd (nxt n) then nxt (nxt n) else nxt n) := by
  have hs := h.succ hn hnL
  set s := nxt n
  by_cases hDs : Dd s
  · rw [ite_eq_left hDs]
    have hsm : s = m := (hD s hDs).resolve_left hs.2.2.1
    have hss := h.succ hs.1 hs.2.1
    set ss := nxt s
    obtain ⟨i, hi, hiL, hiD⟩ := hex
    have hin : i ≠ n := fun e => hiD (e ▸ hDn)
    have his : i ≠ s := fun e => hiD (e ▸ hDs)
    have hssn : ss ≠ n := by
      intro e
      rcases cyc_cover (natCast_ne hs.2.2.1.symm) (natCast_ne hin) with h1 | h1 | h1
      · exact hs.2.2.2 i hi hiL h1
      · simp_all
      · rw [← e] at h1; exact hss.2.2.2 i hi hiL h1
    have hDss : ¬ Dd ss := by
      intro hd
      rcases hD ss hd with e | e
      · exact hssn e
      · exact hss.2.2.1 (e.trans hsm.symm)
    have hmid : cyc n ss s := by
      rcases cyc_three (natCast_ne hssn.symm) (natCast_ne hs.2.2.1.symm)
        (natCast_ne hss.2.2.1) with h1 | h1
      · exact h1
      · -- `ss` lies between `n` and `s`, impossible
        exact absurd h1 (hs.2.2.2 ss hss.1 hss.2.1)
    refine ⟨hss.1, ⟨hss.2.1, hDss⟩, hssn, fun j hj hjL h1 => ?_⟩
    rcases sideInArc_split h1 hmid with h2 | h2 | h2
    · exact hs.2.2.2 j hj hjL.1 h2
    · simp_all
    · exact hss.2.2.2 j hj hjL.1 h2
  · rw [ite_eq_right hDs]
    exact ⟨hs.1, ⟨hs.2.1, hDs⟩, hs.2.2.1, fun j hj hjL => hs.2.2.2 j hj hjL.1⟩

end

end Gran

end Chazelle.Core
