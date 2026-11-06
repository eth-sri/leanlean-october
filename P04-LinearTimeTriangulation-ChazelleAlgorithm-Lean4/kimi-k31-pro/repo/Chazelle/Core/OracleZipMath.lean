module

public import Chazelle.Core.OracleQueryMeets
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.UnfoldTactics
public import Chazelle.SimpTactics
public import Chazelle.MiscTactics
public import Chazelle.ChainTactics

/-!
# Lemma 3.6 (WP-H), part 29: the mirror of the chain in walk keys

The walk keys `κ ∈ [6, 2 m + 6]` are the tour positions of the double boundary of the chain; two
of them have the same point iff they are equal or their sum is `12 - 2 S` modulo `2 m`
(`mirror_sum`, and its converse `same_point_of_sum`).  In walk keys the mirror is two reflections:
of `[6, κT]` and of `[κT, 2 m + 6]` (`mk`), where `κT` is the key of the second visit of the top.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (sidePt sideE sideInArc)
open Chazelle.Geometry (lerp lerp_zero)

namespace OracleQ

variable (C : Chain)

/-- **Tour positions with opposite tour coordinates have the same point.** -/
theorem same_point_of_opp {i i' : ℕ} (hi : i < 2 * C.m) (hi' : i' < 2 * C.m) {t t' : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) (ht' : 0 ≤ t') (ht1' : t' < 1)
    (h : ((tj C i + tj C i' : ℕ) : ℝ) + t + t' = 2 * C.m ∨
      ((tj C i + tj C i' : ℕ) : ℝ) + t + t' = 0) :
    sidePt (C.sideWalk C.sideBeta) (i + 6) t = sidePt (C.sideWalk C.sideBeta) (i' + 6) t' := by
  rw [tour_pt C i hi, tour_pt C i' hi']
  have ha := tj_lt C i
  have hb := tj_lt C i'
  set a := tj C i with hadef
  set b := tj C i' with hbdef
  push_cast at h
  -- the fractional parts
  have hint : ∀ z : ℤ, (a : ℝ) + b + t + t' = z → t + t' = 0 ∨ t + t' = 1 := by
    intro z hz
    have h1 : ((z - a - b : ℤ) : ℝ) = t + t' := by pcl
    have h2 : (z - a - b : ℤ) < 2 := by
      have : ((z - a - b : ℤ) : ℝ) < 2 := by rwli [h1]
      exact_mod_cast this
    have h3 : 0 ≤ (z - a - b : ℤ) := by
      have : (0 : ℝ) ≤ ((z - a - b : ℤ) : ℝ) := by rwli [h1]
      exact_mod_cast this
    rcases (by omega : (z - a - b : ℤ) = 0 ∨ (z - a - b : ℤ) = 1) with e | e
    · left; rws [← h1, e]
    · right; rws [← h1, e]
  have hm := C.one_le
  rcases h with h | h
  · rcases hint (2 * C.m) (by pcl) with h0 | h1
    · have ht0 : t = 0 := by linarith
      have ht0' : t' = 0 := by linarith
      subst ht0 ht0'
      have hab : a + b = 2 * C.m := by
        have : ((a + b : ℕ) : ℝ) = ((2 * C.m : ℕ) : ℝ) := by pcl
        exact_mod_cast this
      unfold tk
      rw [← hadef, ← hbdef]
      split_ifs <;> simp at * <;> first | (exfalso; omega) | (congr 1; omega) | simp_all
    · have htp : 0 < t := by
        by_contra hc; push Not at hc
        have : t = 0 := le_antisymm hc ht
        rwli [this] at h1
      have htp' : 0 < t' := by
        by_contra hc; push Not at hc
        have : t' = 0 := le_antisymm hc ht'
        rwli [this] at h1
      have hab : a + b + 1 = 2 * C.m := by
        have : ((a + b + 1 : ℕ) : ℝ) = ((2 * C.m : ℕ) : ℝ) := by pcl
        exact_mod_cast this
      unfold tk
      rw [← hadef, ← hbdef, ite_eq_right htp.ne', ite_eq_right htp'.ne']
      split_ifs with h1' h2'
      · exfalso; omega
      · show cp C a t = cp C (2 * C.m - b - 1) (1 - t')
        rw [show 2 * C.m - b - 1 = a by omega, show 1 - t' = t by linarith]
      · show cp C (2 * C.m - a - 1) (1 - t) = cp C b t'
        rw [show 2 * C.m - a - 1 = b by omega, show 1 - t = t' by linarith]
      · exfalso; omega
  · have ht0 : t = 0 := by
      have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      have : (0 : ℝ) ≤ b := Nat.cast_nonneg b
      linarith
    have ht0' : t' = 0 := by
      have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      have : (0 : ℝ) ≤ b := Nat.cast_nonneg b
      linarith
    subst ht0 ht0'
    have hab : a + b = 0 := by
      have : ((a + b : ℕ) : ℝ) = 0 := by pcl
      exact_mod_cast this
    unfold tk
    rw [← hadef, ← hbdef]
    rw [show a = 0 by omega, show b = 0 by omega]

/-- A walk position with key in `[6, 2 m + 6]` is a tour position, up to the closing vertex. -/
theorem tour_norm {p : ℕ} (hp : p < 2 * C.m + 7) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1)
    (h6 : (6 : ℝ) ≤ p + t) (h7 : (p : ℝ) + t ≤ 2 * C.m + 6) :
    ∃ i : ℕ, ∃ e : ℕ, i < 2 * C.m ∧ (e = 0 ∨ e = 2 * C.m) ∧ (p : ℝ) + t = 6 + i + t + e ∧
      sidePt (C.sideWalk C.sideBeta) p t = sidePt (C.sideWalk C.sideBeta) (i + 6) t := by
  have hm := C.one_le
  have hp6 : 6 ≤ p := by
    have : (5 : ℝ) < p := by linarith
    have : 5 < p := by exact_mod_cast this
    omega
  rcases Nat.lt_or_ge p (2 * C.m + 6) with h | h
  · refine ⟨p - 6, 0, by omega, Or.inl rfl, ?_, by rw [show p - 6 + 6 = p by omega]⟩
    rw [Nat.cast_sub hp6]; pcr
  · have hp' : p = 2 * C.m + 6 := by omega
    subst hp'
    have ht0 : t = 0 := by push_cast at h7; linarith
    subst ht0
    exact ⟨0, 2 * C.m, by omega, Or.inr rfl, by pcr, sidePt_last C⟩

/-- **Keys with sum `12 - 2 S` modulo `2 m` have the same point.** -/
theorem same_point_of_sum {p p' : ℕ} (hp : p < 2 * C.m + 7) (hp' : p' < 2 * C.m + 7)
    {t t' : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (ht' : 0 ≤ t') (ht1' : t' < 1)
    (h6 : (6 : ℝ) ≤ p + t) (h7 : (p : ℝ) + t ≤ 2 * C.m + 6)
    (h6' : (6 : ℝ) ≤ p' + t') (h7' : (p' : ℝ) + t' ≤ 2 * C.m + 6)
    {z : ℤ} (hz : ((p : ℝ) + t) + (p' + t') = 12 - 2 * C.sideS C.sideBeta + 2 * C.m * z) :
    sidePt (C.sideWalk C.sideBeta) p t = sidePt (C.sideWalk C.sideBeta) p' t' := by
  have hm := C.one_le
  obtain ⟨i, e, hi, he, hk, hpt⟩ := tour_norm C hp ht ht1 h6 h7
  obtain ⟨i', e', hi', he', hk', hpt'⟩ := tour_norm C hp' ht' ht1' h6' h7'
  rw [hpt, hpt']
  refine same_point_of_opp C hi hi' ht ht1 ht' ht1' ?_
  -- the tour indices
  have e1 := Nat.mod_add_div (C.sideS C.sideBeta + i) (2 * C.m)
  have e2 := Nat.mod_add_div (C.sideS C.sideBeta + i') (2 * C.m)
  have ha : tj C i = (C.sideS C.sideBeta + i) % (2 * C.m) := rfl
  have hb : tj C i' = (C.sideS C.sideBeta + i') % (2 * C.m) := rfl
  set qa := (C.sideS C.sideBeta + i) / (2 * C.m)
  set qb := (C.sideS C.sideBeta + i') / (2 * C.m)
  have e1r : ((tj C i : ℕ) : ℝ) + 2 * C.m * qa = C.sideS C.sideBeta + i := by
    rw [ha]; exact_mod_cast e1
  have e2r : ((tj C i' : ℕ) : ℝ) + 2 * C.m * qb = C.sideS C.sideBeta + i' := by
    rw [hb]; exact_mod_cast e2
  have hA := tj_lt C i
  have hB := tj_lt C i'
  set A : ℝ := ((tj C i + tj C i' : ℕ) : ℝ) + t + t' with hAdef
  have hAz : ∃ w : ℤ, A = 2 * C.m * w := by
    have ee : (e : ℝ) + e' = 2 * C.m * ((if e = 0 then 0 else 1) + (if e' = 0 then 0 else 1) : ℤ) := by
      rcases he with rfl | rfl <;> rcases he' with rfl | rfl <;>
        simp [show 2 * C.m ≠ 0 by omega]; ring
    refine ⟨z - qa - qb - ((if e = 0 then 0 else 1) + (if e' = 0 then 0 else 1)), ?_⟩
    rw [hAdef]; push_cast at ee ⊢
    have := hk; have := hk'
    linarith
  obtain ⟨w, hw⟩ := hAz
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hA4 : A < 4 * C.m := by
    rw [hAdef]; push_cast
    have : ((tj C i : ℕ) : ℝ) + 1 ≤ 2 * C.m := by exact_mod_cast hA
    have : ((tj C i' : ℕ) : ℝ) + 1 ≤ 2 * C.m := by exact_mod_cast hB
    linarith
  have hm0 : (0 : ℝ) < C.m := by exact_mod_cast hm
  have hw0 : 0 ≤ w := by
    by_contra hc; push Not at hc
    have : (w : ℝ) ≤ -1 := by exact_mod_cast (show w ≤ -1 by omega)
    nlinarith
  have hw2 : w < 2 := by
    by_contra hc; push Not at hc
    have : (2 : ℝ) ≤ w := by exact_mod_cast hc
    nlinarith
  rcases (by omega : w = 0 ∨ w = 1) with rfl | rfl
  · right; simpa using hw
  · left; simpa using hw

/-- The tour index of the second visit of the top. -/
noncomputable def rT : ℕ := (4 * C.m - 2 * C.sideS C.sideBeta) % (2 * C.m)

/-- The key of the second visit of the top. -/
noncomputable def κT : ℝ := 6 + rT C

open Classical in
/-- **The mirror of the chain in walk keys**: the reflections of `[6, κT]` and `[κT, 2 m + 6]`. -/
noncomputable def mk (κ : ℝ) : ℝ := if κ ≤ κT C then 6 + κT C - κ else κT C + 2 * C.m + 6 - κ

theorem rT_lt : rT C < 2 * C.m := Nat.mod_lt _ (by have := C.one_le; omega)

theorem κT_ge : (6 : ℝ) ≤ κT C := by unfold κT; linarith [(Nat.cast_nonneg (rT C) : (0 : ℝ) ≤ _)]

theorem κT_lt : κT C < 2 * C.m + 6 := by
  unfold κT
  have : ((rT C : ℕ) : ℝ) + 1 ≤ 2 * C.m := by exact_mod_cast rT_lt C
  linarith

/-- The mirror stays in the tour range, and the sum of a key and its mirror is `12 - 2 S`
modulo `2 m`. -/
theorem mk_facts {κ : ℝ} (h6 : 6 ≤ κ) (h7 : κ ≤ 2 * C.m + 6) :
    6 ≤ mk C κ ∧ mk C κ ≤ 2 * C.m + 6 ∧
      ∃ z : ℤ, κ + mk C κ = 12 - 2 * C.sideS C.sideBeta + 2 * C.m * z := by
  have hS := C.sideS_lt C.sideBeta
  have hr := Nat.mod_add_div (4 * C.m - 2 * C.sideS C.sideBeta) (2 * C.m)
  set q := (4 * C.m - 2 * C.sideS C.sideBeta) / (2 * C.m)
  have hrr : ((rT C : ℕ) : ℝ) + 2 * C.m * q = 4 * C.m - 2 * C.sideS C.sideBeta := by
    have : ((rT C + 2 * C.m * q : ℕ) : ℝ) = ((4 * C.m - 2 * C.sideS C.sideBeta : ℕ) : ℝ) := by
      unfold rT; rw [hr]
    rw [Nat.cast_sub (by omega)] at this; push_cast at this; linarith
  have hT6 := κT_ge C
  have hT7 := κT_lt C
  unfold mk
  split_ifs with h
  · refine ⟨by linarith, by linarith, 2 - q, ?_⟩
    unfold κT at *; pcl
  · push Not at h
    refine ⟨by linarith, by linarith, 3 - q, ?_⟩
    unfold κT at *; pcl

/-- **Keys of one point**: a key with sum `12 - 2 S` (mod `2 m`) with `κ` is `mk κ`, up to `2 m`. -/
theorem eq_mk_of_sum {κ κ' : ℝ} (h6 : 6 ≤ κ) (h7 : κ ≤ 2 * C.m + 6) (h6' : 6 ≤ κ')
    (h7' : κ' ≤ 2 * C.m + 6) {z : ℤ}
    (hz : κ + κ' = 12 - 2 * C.sideS C.sideBeta + 2 * C.m * z) :
    κ' = mk C κ ∨ κ' + 2 * C.m = mk C κ ∨ κ' = mk C κ + 2 * C.m := by
  obtain ⟨a1, a2, z0, hz0⟩ := mk_facts C h6 h7
  have hm : (0 : ℝ) < C.m := by exact_mod_cast C.one_le
  have hd : κ' - mk C κ = 2 * C.m * ((z - z0 : ℤ) : ℝ) := by pcl
  have hlt : ((z - z0 : ℤ) : ℝ) < 2 := by nlinarith
  have hgt : -2 < ((z - z0 : ℤ) : ℝ) := by nlinarith
  have h1 : z - z0 < 2 := by exact_mod_cast hlt
  have h2 : -2 < z - z0 := by exact_mod_cast hgt
  rcases (by omega : z - z0 = 0 ∨ z - z0 = 1 ∨ z - z0 = -1) with e | e | e <;> rw [e] at hd <;>
    push_cast at hd
  · left; linarith
  · right; right; linarith
  · right; left; linarith

/-! ## The zipper pairs -/

section Zip

variable {C} {Q : Polygon} {N : NF}

/-- The arc at spine position `q` contains the keys just before `y`. -/
def Before (C : Chain) (Q : Polygon) (N : NF) (q : ℕ) (y : ℝ) : Prop :=
  ∃ δ > (0 : ℝ), ∀ ε, 0 < ε → ε < δ →
    sideInArc (sk (chainModel C) Q N q) (ek (chainModel C) Q N q) (y - ε)

/-- The arc at spine position `q` contains the keys just after `y`. -/
def After (C : Chain) (Q : Polygon) (N : NF) (q : ℕ) (y : ℝ) : Prop :=
  ∃ δ > (0 : ℝ), ∀ ε, 0 < ε → ε < δ →
    sideInArc (sk (chainModel C) Q N q) (ek (chainModel C) Q N q) (y + ε)

/-- The interior of an arc is free of cuts. -/
theorem not_cut_of_int (hN : IsNF (chainModel C) Q N) (hne : (N.F (chainModel C) Q).Nonempty)
    {p : ℕ} (hp : p < N.arcs.length) {x : ℝ}
    (hx : sideInArc (sk (chainModel C) Q N p) (ek (chainModel C) Q N p) x) :
    ¬ (chainModel C).IsCut (N.F (chainModel C) Q) x :=
  (arc_facts hN hne hp).2.2.2 x hx

/-- **An interval ending at an interior key and free of cuts lies in the arc.** -/
theorem int_of_noCut_left (hN : IsNF (chainModel C) Q N) (hne : (N.F (chainModel C) Q).Nonempty)
    {p : ℕ} (hp : p < N.arcs.length) {L κ : ℝ}
    (hκ : sideInArc (sk (chainModel C) Q N p) (ek (chainModel C) Q N p) κ)
    (hno : ∀ x, L < x → x ≤ κ → ¬ (chainModel C).IsCut (N.F (chainModel C) Q) x)
    {x : ℝ} (h1 : L < x) (h2 : x ≤ κ) :
    sideInArc (sk (chainModel C) Q N p) (ek (chainModel C) Q N p) x := by
  obtain ⟨hs, he, -, -⟩ := arc_facts hN hne hp
  set s := sk (chainModel C) Q N p
  set e := ek (chainModel C) Q N p
  have hsL : ¬ (L < s ∧ s ≤ κ) := fun h => hno s h.1 h.2 hs
  have heL : ¬ (L < e ∧ e ≤ κ) := fun h => hno e h.1 h.2 he
  unfold sideInArc at hκ ⊢
  split_ifs at hκ ⊢ with h
  · constructor
    · by_contra hc; push Not at hc; exact hsL ⟨by linarith, by linarith⟩
    · linarith [hκ.2]
  · rcases hκ with hk | hk
    · left; by_contra hc; push Not at hc; exact hsL ⟨by linarith, by linarith⟩
    · right; linarith

/-- **An interval starting at an interior key and free of cuts lies in the arc.** -/
theorem int_of_noCut_right (hN : IsNF (chainModel C) Q N) (hne : (N.F (chainModel C) Q).Nonempty)
    {q : ℕ} (hq : q < N.arcs.length) {κ R : ℝ}
    (hκ : sideInArc (sk (chainModel C) Q N q) (ek (chainModel C) Q N q) κ)
    (hno : ∀ x, κ ≤ x → x < R → ¬ (chainModel C).IsCut (N.F (chainModel C) Q) x)
    {x : ℝ} (h1 : κ ≤ x) (h2 : x < R) :
    sideInArc (sk (chainModel C) Q N q) (ek (chainModel C) Q N q) x := by
  obtain ⟨hs, he, -, -⟩ := arc_facts hN hne hq
  set s := sk (chainModel C) Q N q
  set e := ek (chainModel C) Q N q
  have hsL : ¬ (κ ≤ s ∧ s < R) := fun h => hno s h.1 h.2 hs
  have heL : ¬ (κ ≤ e ∧ e < R) := fun h => hno e h.1 h.2 he
  unfold sideInArc at hκ ⊢
  split_ifs at hκ ⊢ with h
  · constructor
    · linarith [hκ.1]
    · by_contra hc; push Not at hc; exact heL ⟨by linarith, by linarith⟩
  · rcases hκ with hk | hk
    · left; linarith
    · right; by_contra hc; push Not at hc; exact heL ⟨by linarith, by linarith⟩

/-- A cut just before an interval inside an arc is the start of the arc. -/
theorem start_eq_of (hN : IsNF (chainModel C) Q N) (hne : (N.F (chainModel C) Q).Nonempty)
    {p : ℕ} (hp : p < N.arcs.length) {c κ : ℝ} (hc : (chainModel C).IsCut (N.F (chainModel C) Q) c)
    (hcκ : c < κ)
    (hin : ∀ x, c < x → x ≤ κ → sideInArc (sk (chainModel C) Q N p) (ek (chainModel C) Q N p) x) :
    sk (chainModel C) Q N p = c := by
  obtain ⟨-, -, -, hfree⟩ := arc_facts hN hne hp
  set s := sk (chainModel C) Q N p
  set e := ek (chainModel C) Q N p
  have hss : ¬ sideInArc s e s := by unfold sideInArc; split_ifs <;> simp; linarith
  have hκ := hin κ hcκ le_rfl
  by_contra hne'
  have hs1 : ¬ (c < s ∧ s ≤ κ) := fun h => hss (hin s h.1 h.2)
  apply hfree c _ hc
  unfold sideInArc at hκ ⊢
  split_ifs at hκ ⊢ with h
  · refine ⟨?_, by linarith [hκ.2]⟩
    rcases lt_or_gt_of_ne hne' with h' | h'
    · exact h'
    · exfalso; exact hs1 ⟨h', by linarith [hκ.1]⟩
  · rcases hκ with hk | hk
    · left
      rcases lt_or_gt_of_ne hne' with h' | h'
      · exact h'
      · exfalso; exact hs1 ⟨h', hk.le⟩
    · right; linarith

/-- A cut just after an interval inside an arc is the end of the arc. -/
theorem end_eq_of (hN : IsNF (chainModel C) Q N) (hne : (N.F (chainModel C) Q).Nonempty)
    {q : ℕ} (hq : q < N.arcs.length) {c κ : ℝ} (hc : (chainModel C).IsCut (N.F (chainModel C) Q) c)
    (hcκ : κ < c)
    (hin : ∀ x, κ ≤ x → x < c → sideInArc (sk (chainModel C) Q N q) (ek (chainModel C) Q N q) x) :
    ek (chainModel C) Q N q = c := by
  obtain ⟨-, -, -, hfree⟩ := arc_facts hN hne hq
  set s := sk (chainModel C) Q N q
  set e := ek (chainModel C) Q N q
  have hee : ¬ sideInArc s e e := by unfold sideInArc; split_ifs <;> simp; linarith
  have hκ := hin κ le_rfl hcκ
  by_contra hne'
  have he1 : ¬ (κ ≤ e ∧ e < c) := fun h => hee (hin e h.1 h.2)
  apply hfree c _ hc
  unfold sideInArc at hκ ⊢
  split_ifs at hκ ⊢ with h
  · refine ⟨by linarith [hκ.1], ?_⟩
    rcases lt_or_gt_of_ne hne' with h' | h'
    · exfalso; exact he1 ⟨by linarith [hκ.2], h'⟩
    · exact h'
  · rcases hκ with hk | hk
    · left; linarith
    · right
      rcases lt_or_gt_of_ne hne' with h' | h'
      · exfalso; exact he1 ⟨hk.le, h'⟩
      · exact h'

/-- **The core of the zipper**: two arcs containing `κ` and its reflection `a + b - κ` in the
interval `[a, b]` meet at the ends of `[a, b]`, at the start of the first (its reflection in the
second), or at the end of the second (its reflection in the first). -/
theorem zip_core (hN : IsNF (chainModel C) Q N) (hP : C.P.Simple)
    (hne : (N.F (chainModel C) Q).Nonempty) {p q : ℕ} (hp : p < N.arcs.length)
    (hq : q < N.arcs.length) {a b κ : ℝ} (haκ : a < κ) (hκb : κ < b)
    (hmk : ∀ x, a < x → x < b → mk C x = a + b - x)
    (hκp : sideInArc (sk (chainModel C) Q N p) (ek (chainModel C) Q N p) κ)
    (hκq : sideInArc (sk (chainModel C) Q N q) (ek (chainModel C) Q N q) (a + b - κ)) :
    (After C Q N p a ∧ Before C Q N q b) ∨
      (a < sk (chainModel C) Q N p ∧ sk (chainModel C) Q N p < b ∧
        Before C Q N q (mk C (sk (chainModel C) Q N p))) ∨
      (a < ek (chainModel C) Q N q ∧ ek (chainModel C) Q N q < b ∧
        After C Q N p (mk C (ek (chainModel C) Q N q))) := by
  classical
  have hGM : GoodModel (chainModel C) := Or.inl ⟨C, hP, rfl⟩
  have hM := walkAx_of_goodModel hGM
  set F := N.F (chainModel C) Q
  have hCu : {x : ℝ | (chainModel C).IsCut F x}.Finite := hM.finite_cuts hN.1.2.1 hN.1.1
  set Cu := hCu.toFinset
  set Z : Finset ℝ := insert a ((Cu.filter (fun c => a < c ∧ c < κ)) ∪
    ((Cu.filter (fun c => a < c ∧ c < b ∧ a + b - c < κ)).image (fun c => a + b - c))) with hZ
  have haZ : a ∈ Z := Finset.mem_insert_self _ _
  set L := Z.max' ⟨a, haZ⟩ with hL
  have hLa : a ≤ L := Z.le_max' a haZ
  have hZlt : ∀ x ∈ Z, x < κ := by
    intro x hx
    rw [hZ, Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_image] at hx
    rcases hx with rfl | ⟨-, -, h⟩ | ⟨c, hc, rfl⟩
    · exact haκ
    · exact h
    · rw [Finset.mem_filter] at hc; exact hc.2.2.2
  have hLκ : L < κ := hZlt L (Z.max'_mem _)
  have hcutκ : ¬ (chainModel C).IsCut F κ := not_cut_of_int hN hne hp hκp
  have hcutκ' : ¬ (chainModel C).IsCut F (a + b - κ) := not_cut_of_int hN hne hq hκq
  -- no cut after `L`
  have hno1 : ∀ x, L < x → x ≤ κ → ¬ (chainModel C).IsCut F x := by
    intro x h1 h2 hx
    rcases eq_or_lt_of_le h2 with e | e
    · rw [e] at hx; exact hcutκ hx
    have : x ∈ Z := by
      rw [hZ, Finset.mem_insert, Finset.mem_union, Finset.mem_filter]
      exact Or.inr (Or.inl ⟨hCu.mem_toFinset.2 hx, by linarith, e⟩)
    have := Z.le_max' x this
    linarith
  -- no cut before the reflection of `L`
  have hno2 : ∀ x, a + b - κ ≤ x → x < a + b - L → ¬ (chainModel C).IsCut F x := by
    intro x h1 h2 hx
    rcases eq_or_lt_of_le h1 with e | e
    · rw [← e] at hx; exact hcutκ' hx
    have : a + b - x ∈ Z := by
      rw [hZ, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
      refine Or.inr (Or.inr ⟨x, ?_, rfl⟩)
      rw [Finset.mem_filter]
      exact ⟨hCu.mem_toFinset.2 hx, by linarith, by linarith, by linarith⟩
    have := Z.le_max' _ this
    linarith
  have hin1 : ∀ x, L < x → x ≤ κ →
      sideInArc (sk (chainModel C) Q N p) (ek (chainModel C) Q N p) x :=
    fun x h1 h2 => int_of_noCut_left hN hne hp hκp hno1 h1 h2
  have hin2 : ∀ x, a + b - κ ≤ x → x < a + b - L →
      sideInArc (sk (chainModel C) Q N q) (ek (chainModel C) Q N q) x :=
    fun x h1 h2 => int_of_noCut_right hN hne hq hκq hno2 h1 h2
  -- the origin of `L`
  have hLZ := Z.max'_mem ⟨a, haZ⟩
  rw [← hL, hZ, Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_image] at hLZ
  rcases hLZ with hLa' | ⟨hc, h1, h2⟩ | ⟨c, hc, hcL⟩
  · -- the end of the interval
    left
    refine ⟨⟨κ - a, by linarith, fun ε h1 h2 => hin1 _ (by linarith) (by linarith)⟩,
      ⟨κ - a, by linarith, fun ε h1 h2 => hin2 _ (by linarith) (by linarith)⟩⟩
  · -- the start of `p`
    right; left
    have hs := start_eq_of hN hne hp (hCu.mem_toFinset.1 hc) hLκ hin1
    rw [hs]
    refine ⟨h1, by linarith, κ - L, by linarith, fun ε e1 e2 => ?_⟩
    rw [hmk L h1 (by linarith)]
    exact hin2 _ (by linarith) (by linarith)
  · -- the end of `q`
    right; right
    rw [Finset.mem_filter] at hc
    obtain ⟨hc, c1, c2, c3⟩ := hc
    have hcL' : c = a + b - L := by linarith
    have he := end_eq_of hN hne hq (hCu.mem_toFinset.1 hc) (show a + b - κ < c by linarith)
      (fun x h1 h2 => hin2 x h1 (by linarith))
    rw [he]
    refine ⟨c1, c2, κ - L, by linarith, fun ε e1 e2 => ?_⟩
    rw [hmk c c1 c2]
    exact hin1 _ (by linarith) (by linarith)

/-- The keys of the top. -/
def TopKey (C : Chain) (x : ℝ) : Prop := x = 6 ∨ x = κT C ∨ x = 2 * C.m + 6

/-- The open halves of the tour range. -/
def InI (C : Chain) (x : ℝ) : Prop := (6 < x ∧ x < κT C) ∨ (κT C < x ∧ x < 2 * C.m + 6)

/-- **The generating cases of the zipper pairs.** -/
def ZipGen (C : Chain) (Q : Polygon) (N : NF) (p q : ℕ) : Prop :=
  (∃ x y, TopKey C x ∧ TopKey C y ∧ x ≠ y ∧
    sideInArc (sk (chainModel C) Q N p) (ek (chainModel C) Q N p) x ∧
    sideInArc (sk (chainModel C) Q N q) (ek (chainModel C) Q N q) y) ∨
  (InI C (sk (chainModel C) Q N p) ∧ Before C Q N q (mk C (sk (chainModel C) Q N p))) ∨
  (InI C (ek (chainModel C) Q N q) ∧ After C Q N p (mk C (ek (chainModel C) Q N q))) ∨
  (6 < κT C ∧ After C Q N p 6 ∧ Before C Q N q (κT C)) ∨
  (After C Q N p (κT C) ∧ Before C Q N q (2 * C.m + 6))

/-- **Every zipper pair is generated.** -/
theorem zip_cases (hN : IsNF (chainModel C) Q N) (hP : C.P.Simple)
    (hne : (N.F (chainModel C) Q).Nonempty) {p q : ℕ} (hp : p < N.arcs.length)
    (hq : q < N.arcs.length) (hpq : p ≠ q) (hZ : ZipRel C Q N p q) : ZipGen C Q N p q := by
  have hGM : GoodModel (chainModel C) := Or.inl ⟨C, hP, rfl⟩
  obtain ⟨p₁, p₂, t₁, t₂, h1, h2, h3, h4, h5, h6, hx, he, i1, i2⟩ := hZ
  have hnW : (chainModel C).W.n = 2 * C.m + 7 := walk_n C
  rw [hnW] at h1 h2
  have hx' : sidePt (chainModel C).W p₂ t₂ ∈ C.set := he ▸ hx
  obtain ⟨r1, r2⟩ := key_range C h1 h3 h4 hx
  obtain ⟨r1', r2'⟩ := key_range C h2 h5 h6 hx'
  have hkk : (p₁ : ℝ) + t₁ ≠ p₂ + t₂ := fun e => hpq (interior_unique hN hGM hne hp hq i1 (e ▸ i2))
  have ms := mirror_sum C hP h1 h2 h3 h4 h5 h6 hx he hkk
  generalize (p₁ : ℝ) + t₁ = κ at r1 r2 i1 hkk ms
  generalize (p₂ : ℝ) + t₂ = κ' at r1' r2' i2 hkk ms
  have hT6 := κT_ge C
  have hT7 := κT_lt C
  have top : ∀ x y, TopKey C x → TopKey C y → x ≠ y →
      sideInArc (sk (chainModel C) Q N p) (ek (chainModel C) Q N p) x →
      sideInArc (sk (chainModel C) Q N q) (ek (chainModel C) Q N q) y → ZipGen C Q N p q :=
    fun x y a b c d e => Or.inl ⟨x, y, a, b, c, d, e⟩
  rcases ms with ⟨z, hz⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
  swap
  · exact top κ κ' (Or.inl e1) (Or.inr (Or.inr (by rw [e2]))) hkk i1 i2
  swap
  · exact top κ κ' (Or.inr (Or.inr (by rw [e1]))) (Or.inl e2) hkk i1 i2
  have hmk6 : mk C 6 = κT C := by urring mk [ite_eq_left hT6]
  have hmkT : mk C (κT C) = 6 := by urring mk [ite_eq_left le_rfl]
  have hmkl : mk C (2 * C.m + 6) = κT C := by
    urring mk [ite_eq_right (by linarith)]
  rcases eq_mk_of_sum C (by linarith) (by linarith) (by linarith) (by linarith) hz with e | e | e
  swap
  · -- `κ' + 2 m = mk κ`: impossible
    exfalso
    unfold mk at e
    split_ifs at e <;> linarith
  swap
  · -- `κ' = mk κ + 2 m`: `κ = κT`, `κ' = 2 m + 6`
    unfold mk at e
    split_ifs at e with h
    swap
    · exfalso; exact hkk (le_antisymm (by linarith) (by linarith))
    have hk : κ = κT C := le_antisymm h (by linarith)
    have hk' : κ' = 2 * C.m + 6 := by rwring [e, hk]
    exact top κ κ' (Or.inr (Or.inl hk)) (Or.inr (Or.inr hk')) hkk i1 i2
  -- the mirror
  by_cases h6k : κ = 6
  · exact top κ κ' (Or.inl h6k) (Or.inr (Or.inl (by rw [e, h6k, hmk6]))) hkk i1 i2
  by_cases hTk : κ = κT C
  · exact top κ κ' (Or.inr (Or.inl hTk)) (Or.inl (by rw [e, hTk, hmkT])) hkk i1 i2
  by_cases hlk : κ = 2 * C.m + 6
  · exact top κ κ' (Or.inr (Or.inr hlk)) (Or.inr (Or.inl (by rw [e, hlk, hmkl]))) hkk i1 i2
  rcases lt_or_gt_of_ne hTk with hlt | hgt
  · -- the first half
    have h6' : 6 < κ := lt_of_le_of_ne (by linarith) (Ne.symm h6k)
    have hmk : ∀ x, 6 < x → x < κT C → mk C x = 6 + κT C - x := fun x a b => by
      unfold mk; rw [ite_eq_left b.le]
    have hq' : sideInArc (sk (chainModel C) Q N q) (ek (chainModel C) Q N q) (6 + κT C - κ) := by
      rwx [← hmk κ h6' hlt, ← e]
    rcases zip_core hN hP hne hp hq h6' hlt hmk i1 hq' with ⟨a1, a2⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by linarith, a1, a2⟩)))
    · exact Or.inr (Or.inl ⟨Or.inl ⟨a1, a2⟩, a3⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨Or.inl ⟨a1, a2⟩, a3⟩))
  · -- the second half
    have hl' : κ < 2 * C.m + 6 := lt_of_le_of_ne (by linarith) hlk
    have hmk : ∀ x, κT C < x → x < 2 * C.m + 6 → mk C x = κT C + (2 * C.m + 6) - x :=
      fun x a b => by urring mk [ite_eq_right (not_le.2 a)]
    have hq' : sideInArc (sk (chainModel C) Q N q) (ek (chainModel C) Q N q)
        (κT C + (2 * C.m + 6) - κ) := by
      rwx [← hmk κ hgt hl', ← e]
    rcases zip_core hN hP hne hp hq hgt hl' hmk i1 hq' with ⟨a1, a2⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a1, a2⟩)))
    · exact Or.inr (Or.inl ⟨Or.inr ⟨a1, a2⟩, a3⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨Or.inr ⟨a1, a2⟩, a3⟩))

/-- A key of the tour range is the key of a walk position. -/
theorem key_decomp {κ : ℝ} (h6 : 6 ≤ κ) (h7 : κ ≤ 2 * C.m + 6) :
    ∃ p : ℕ, ∃ t : ℝ, p < 2 * C.m + 7 ∧ 0 ≤ t ∧ t < 1 ∧ (p : ℝ) + t = κ := by
  have h0 : 0 ≤ κ := by linarith
  refine ⟨⌊κ⌋₊, κ - ⌊κ⌋₊, ?_, by linarith [Nat.floor_le h0], by
    linarith [Nat.lt_floor_add_one κ], by ring⟩
  have : (⌊κ⌋₊ : ℝ) ≤ 2 * C.m + 6 := (Nat.floor_le h0).trans h7
  have : ⌊κ⌋₊ ≤ 2 * C.m + 6 := by exact_mod_cast this
  omega

/-- The point of a key of the tour range is on the chain. -/
theorem pt_on_chain {p : ℕ} (hp : p < 2 * C.m + 7) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1)
    (h6 : (6 : ℝ) ≤ p + t) (h7 : (p : ℝ) + t ≤ 2 * C.m + 6) :
    sidePt (C.sideWalk C.sideBeta) p t ∈ C.set := by
  obtain ⟨i, e, hi, -, -, hpt⟩ := tour_norm C hp ht ht1 h6 h7
  rw [hpt, C.sidePt_tour C.sideBeta hi]
  refine ⟨tci C i, tci_lt C i, ?_⟩
  rw [← tour_seg C i]; exact ⟨t, ht, ht1.le, rfl⟩

/-- **A key and its mirror in two arcs make a zipper pair.** -/
theorem zipRel_of_mk {p q : ℕ} {κ : ℝ} (h6 : 6 ≤ κ) (h7 : κ ≤ 2 * C.m + 6)
    (hp : sideInArc (sk (chainModel C) Q N p) (ek (chainModel C) Q N p) κ)
    (hq : sideInArc (sk (chainModel C) Q N q) (ek (chainModel C) Q N q) (mk C κ)) :
    ZipRel C Q N p q := by
  obtain ⟨a1, a2, z, hz⟩ := mk_facts C h6 h7
  obtain ⟨p₁, t₁, h1, h2, h3, e1⟩ := key_decomp h6 h7
  obtain ⟨p₂, t₂, h1', h2', h3', e2⟩ := key_decomp a1 a2
  have hnW  := walk_n C
  refine ⟨p₁, p₂, t₁, t₂, by rwx [hnW], by rwx [hnW], h2, h3, h2', h3',
    pt_on_chain h1 h2 h3 (by rwx [e1]) (by rwx [e1]), ?_,
    by rwx [e1], by rwx [e2]⟩
  exact same_point_of_sum C h1 h1' h2 h3 h2' h3' (by rwx [e1]) (by rwx [e1])
    (by rwx [e2]) (by rwx [e2]) (z := z) (by rwx [e1, e2])

/-- The top keys have one point: the top. -/
theorem top_keys_same {x y : ℝ} (hx : TopKey C x) (hy : TopKey C y) :
    ∃ p₁ p₂ : ℕ, p₁ < 2 * C.m + 7 ∧ p₂ < 2 * C.m + 7 ∧ (p₁ : ℝ) = x ∧ (p₂ : ℝ) = y ∧
      sidePt (C.sideWalk C.sideBeta) p₁ 0 = sidePt (C.sideWalk C.sideBeta) p₂ 0 := by
  have hm := C.one_le
  have hr := rT_lt C
  -- the three keys as naturals with the top as point
  have key : ∀ x, TopKey C x → ∃ p : ℕ, p < 2 * C.m + 7 ∧ (p : ℝ) = x ∧
      sidePt (C.sideWalk C.sideBeta) p 0 = sidePt (C.sideWalk C.sideBeta) 6 0 := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨6, by omega, by norm_num, rfl⟩
    · refine ⟨6 + rT C, by omega, by unfold κT; pcr, ?_⟩
      have hsum := mk_facts C (κT_ge C) (le_of_lt (κT_lt C))
      obtain ⟨-, -, z, hz⟩ := hsum
      have hmkT : mk C (κT C) = 6 := by urring mk [ite_eq_left le_rfl]
      rw [hmkT] at hz
      refine same_point_of_sum C (by omega) (by omega) le_rfl one_pos le_rfl one_pos
        (by push_cast; linarith [(Nat.cast_nonneg (rT C) : (0:ℝ) ≤ _)])
        (by
          have hrR : ((rT C : ℕ) : ℝ) + 1 ≤ 2 * C.m := by exact_mod_cast hr
          push_cast; linarith [hrR])
        (by norm_num) (by pcl) (z := z) ?_
      push_cast; ufl κT at hz
    · refine ⟨2 * C.m + 6, by omega, by pcr, ?_⟩
      have := sidePt_last C; simpa using this
  obtain ⟨p₁, a1, b1, c1⟩ := key x hx
  obtain ⟨p₂, a2, b2, c2⟩ := key y hy
  exact ⟨p₁, p₂, a1, a2, b1, b2, c1.trans c2.symm⟩

/-- **Every generated pair is a zipper pair.** -/
theorem zipRel_of_gen (hN : IsNF (chainModel C) Q N) (_hP : C.P.Simple)
    (hne : (N.F (chainModel C) Q).Nonempty) {p q : ℕ} (hp : p < N.arcs.length)
    (hq : q < N.arcs.length) (hG : ZipGen C Q N p q) : ZipRel C Q N p q := by
  have hT6 := κT_ge C
  have hT7 := κT_lt C
  have hnW  := walk_n C
  obtain ⟨-, -, hne_p, -⟩ := arc_facts hN hne hp
  obtain ⟨-, -, hne_q, -⟩ := arc_facts hN hne hq
  -- points just after the start / before the end of an arc are inside it
  have after_start : ∀ r, r < N.arcs.length → After C Q N r (sk (chainModel C) Q N r) := by
    intro r hr
    obtain ⟨-, -, hne', -⟩ := arc_facts hN hne hr
    by_cases h : sk (chainModel C) Q N r < ek (chainModel C) Q N r
    · refine ⟨ek (chainModel C) Q N r - sk (chainModel C) Q N r, by linarith, fun ε e1 e2 => ?_⟩
      unfold sideInArc; rw [ite_eq_left h]; constructor <;> linarith
    · refine ⟨1, one_pos, fun ε e1 e2 => ?_⟩
      unfold sideInArc; rw [ite_eq_right h]; left; linarith
  have before_end : ∀ r, r < N.arcs.length → Before C Q N r (ek (chainModel C) Q N r) := by
    intro r hr
    obtain ⟨-, -, hne', -⟩ := arc_facts hN hne hr
    by_cases h : sk (chainModel C) Q N r < ek (chainModel C) Q N r
    · refine ⟨ek (chainModel C) Q N r - sk (chainModel C) Q N r, by linarith, fun ε e1 e2 => ?_⟩
      unfold sideInArc; rw [ite_eq_left h]; constructor <;> linarith
    · refine ⟨1, one_pos, fun ε e1 e2 => ?_⟩
      unfold sideInArc; rw [ite_eq_right h]; right; linarith
  have mk1 : ∀ x, 6 < x → x < κT C → mk C x = 6 + κT C - x := fun x a b => by
    unfold mk; rw [ite_eq_left b.le]
  have mk2 : ∀ x, κT C < x → x < 2 * C.m + 6 → mk C x = κT C + (2 * C.m + 6) - x :=
    fun x a b => by urring mk [ite_eq_right (not_le.2 a)]
  rcases hG with ⟨x, y, hx, hy, -, i1, i2⟩ | ⟨hI, δ, hδ, hB⟩ | ⟨hI, δ, hδ, hA⟩ |
      ⟨h6T, ⟨δ, hδ, hA⟩, ⟨δ', hδ', hB⟩⟩ | ⟨⟨δ, hδ, hA⟩, ⟨δ', hδ', hB⟩⟩
  · -- the top
    obtain ⟨p₁, p₂, a1, a2, b1, b2, c⟩ := top_keys_same hx hy
    refine ⟨p₁, p₂, 0, 0, by rwx [hnW], by rwx [hnW], le_rfl, one_pos, le_rfl,
      one_pos, ?_, c, by rwx [add_zero, b1], by rwx [add_zero, b2]⟩
    have hx6 : 6 ≤ x ∧ x ≤ 2 * C.m + 6 := by
      rcases hx with rfl | rfl | rfl <;> constructor <;> linarith
    exact pt_on_chain a1 le_rfl one_pos (by rws [b1]; exact hx6.1)
      (by rws [b1]; exact hx6.2)
  · -- the start of `p`
    obtain ⟨δ', hδ', hAs⟩ := after_start p hp
    set s := sk (chainModel C) Q N p
    obtain ⟨a, b, h6a, has, hsb, hb, hmk⟩ : ∃ a b : ℝ, 6 ≤ a ∧ a < s ∧ s < b ∧ b ≤ 2 * C.m + 6 ∧
        ∀ x, a < x → x < b → mk C x = a + b - x := by
      rcases hI with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨6, κT C, le_rfl, h1, h2, hT7.le, mk1⟩
      · exact ⟨κT C, 2 * C.m + 6, hT6, h1, h2, le_rfl, mk2⟩
    set ε := min (min δ δ') (b - s) / 2 with hε
    have hε0 : 0 < ε := by
      have := lt_min (lt_min hδ hδ') (show 0 < b - s by linarith); linarith
    have hε1 : ε < δ := by have := min_le_left (min δ δ') (b - s); have := min_le_left δ δ'; linarith
    have hε2 : ε < δ' := by
      have := min_le_left (min δ δ') (b - s); have := min_le_right δ δ'; linarith
    have hε3 : ε < b - s := by have := min_le_right (min δ δ') (b - s); linarith
    refine zipRel_of_mk (κ := s + ε) (by linarith) (by linarith) (hAs ε hε0 hε2) ?_
    rw [hmk _ (by linarith) (by linarith)]
    have := hB ε hε0 hε1
    rw [hmk s has hsb] at this
    convert this using 1; ring
  · -- the end of `q`
    obtain ⟨δ', hδ', hBe⟩ := before_end q hq
    set e := ek (chainModel C) Q N q
    obtain ⟨a, b, h6a, has, hsb, hb, hmk⟩ : ∃ a b : ℝ, 6 ≤ a ∧ a < e ∧ e < b ∧ b ≤ 2 * C.m + 6 ∧
        ∀ x, a < x → x < b → mk C x = a + b - x := by
      rcases hI with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨6, κT C, le_rfl, h1, h2, hT7.le, mk1⟩
      · exact ⟨κT C, 2 * C.m + 6, hT6, h1, h2, le_rfl, mk2⟩
    set ε := min (min δ δ') (e - a) / 2 with hε
    have hε0 : 0 < ε := by
      have := lt_min (lt_min hδ hδ') (show 0 < e - a by linarith); linarith
    have hε1 : ε < δ := by have := min_le_left (min δ δ') (e - a); have := min_le_left δ δ'; linarith
    have hε2 : ε < δ' := by
      have := min_le_left (min δ δ') (e - a); have := min_le_right δ δ'; linarith
    have hε3 : ε < e - a := by have := min_le_right (min δ δ') (e - a); linarith
    have hme  := hmk e has hsb
    refine zipRel_of_mk (κ := mk C e + ε) (by rwli [hme]) (by rwli [hme])
      (hA ε hε0 hε1) ?_
    rw [hmk _ (by rwli [hme]) (by rwli [hme]), hme]
    convert hBe ε hε0 hε2 using 1; ring
  · -- the first half from its ends
    have hmk6 : mk C 6 = κT C := by urring mk [ite_eq_left hT6]
    set ε := min (min δ δ') (κT C - 6) / 2 with hε
    have hε0 : 0 < ε := by
      have := lt_min (lt_min hδ hδ') (show 0 < κT C - 6 by linarith); linarith
    have hε1 : ε < δ := by
      have := min_le_left (min δ δ') (κT C - 6); have := min_le_left δ δ'; linarith
    have hε2 : ε < δ' := by
      have := min_le_left (min δ δ') (κT C - 6); have := min_le_right δ δ'; linarith
    have hε3 : ε < κT C - 6 := by have := min_le_right (min δ δ') (κT C - 6); linarith
    refine zipRel_of_mk (κ := 6 + ε) (by linarith) (by linarith) (hA ε hε0 hε1) ?_
    rw [mk1 _ (by linarith) (by linarith)]
    convert hB ε hε0 hε2 using 1; ring
  · -- the second half from its ends
    set ε := min (min δ δ') (2 * C.m + 6 - κT C) / 2 with hε
    have hε0 : 0 < ε := by
      have := lt_min (lt_min hδ hδ') (show 0 < 2 * C.m + 6 - κT C by linarith); linarith
    have hε1 : ε < δ := by
      have := min_le_left (min δ δ') (2 * C.m + 6 - κT C); have := min_le_left δ δ'; linarith
    have hε2 : ε < δ' := by
      have := min_le_left (min δ δ') (2 * C.m + 6 - κT C); have := min_le_right δ δ'; linarith
    have hε3 : ε < 2 * C.m + 6 - κT C := by
      have := min_le_right (min δ δ') (2 * C.m + 6 - κT C); linarith
    refine zipRel_of_mk (κ := κT C + ε) (by linarith) (by linarith) (hA ε hε0 hε1) ?_
    rw [mk2 _ (by linarith) (by linarith)]
    convert hB ε hε0 hε2 using 1; ring

theorem succP_predP {A p : ℕ} (hp : p < A) : succP A (predP A p) = p := by
  unfold succP predP; splao

/-- Every arc ends where its successor starts. -/
theorem ek_eq_sk_succ (hN : IsNF (chainModel C) Q N) (hP : C.P.Simple)
    (hne : (N.F (chainModel C) Q).Nonempty) {p : ℕ} (hp : p < N.arcs.length) :
    ek (chainModel C) Q N p = sk (chainModel C) Q N (succP N.arcs.length p) := by
  have hGM : GoodModel (chainModel C) := Or.inl ⟨C, hP, rfl⟩
  obtain ⟨-, hc, -, -⟩ := arc_facts hN hne hp
  obtain ⟨U, hU, b, hab⟩ := (arcCover (chainModel C) Q _ hGM hN.1).2 _ hc
  obtain ⟨j, hj, hjs, -⟩ := NFLoc.listed_of_isArc hN hU hab
  obtain ⟨r, hr, hrj⟩ := NFLoc.seq_surj hN hj
  have hsr : sk (chainModel C) Q N r = ek (chainModel C) Q N p := by
    show (chainModel C).key Q (N.arc (N.seq.getD r 0)).s = _
    rw [hrj, hjs]
  have := end_start_adj hN hGM hne hp hr hsr.symm
  rw [← this, hsr]

/-- Points just after the start of an arc are inside it. -/
theorem after_start (hN : IsNF (chainModel C) Q N) (hne : (N.F (chainModel C) Q).Nonempty)
    {r : ℕ} (hr : r < N.arcs.length) : After C Q N r (sk (chainModel C) Q N r) := by
  obtain ⟨-, -, hne', -⟩ := arc_facts hN hne hr
  by_cases h : sk (chainModel C) Q N r < ek (chainModel C) Q N r
  · refine ⟨ek (chainModel C) Q N r - sk (chainModel C) Q N r, by linarith, fun ε e1 e2 => ?_⟩
    unfold sideInArc; rw [ite_eq_left h]; constructor <;> linarith
  · refine ⟨1, one_pos, fun ε e1 e2 => ?_⟩
    unfold sideInArc; rw [ite_eq_right h]; left; linarith

/-- Points just before the end of an arc are inside it. -/
theorem before_end (hN : IsNF (chainModel C) Q N) (hne : (N.F (chainModel C) Q).Nonempty)
    {r : ℕ} (hr : r < N.arcs.length) : Before C Q N r (ek (chainModel C) Q N r) := by
  obtain ⟨-, -, hne', -⟩ := arc_facts hN hne hr
  by_cases h : sk (chainModel C) Q N r < ek (chainModel C) Q N r
  · refine ⟨ek (chainModel C) Q N r - sk (chainModel C) Q N r, by linarith, fun ε e1 e2 => ?_⟩
    unfold sideInArc; rw [ite_eq_left h]; constructor <;> linarith
  · refine ⟨1, one_pos, fun ε e1 e2 => ?_⟩
    unfold sideInArc; rw [ite_eq_right h]; right; linarith

/-- Interior points have their neighbours inside. -/
theorem int_nhd {s e x : ℝ} (h : sideInArc s e x) : ∃ δ > (0 : ℝ), ∀ ε, 0 < ε → ε < δ →
    sideInArc s e (x - ε) ∧ sideInArc s e (x + ε) := by
  unfold sideInArc at h ⊢
  split_ifs at h ⊢ with hse
  · refine ⟨min (x - s) (e - x), lt_min (by linarith [h.1]) (by linarith [h.2]), fun ε e1 e2 => ?_⟩
    have := min_le_left (x - s) (e - x); have := min_le_right (x - s) (e - x)
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  · rcases h with h | h
    · refine ⟨x - s, by linarith, fun ε e1 e2 => ⟨Or.inl (by linarith), Or.inl (by linarith)⟩⟩
    · refine ⟨e - x, by linarith, fun ε e1 e2 => ⟨Or.inr (by linarith), Or.inr (by linarith)⟩⟩

open Classical in
/-- **The arc just before a located key.** -/
theorem before_of_loc (hN : IsNF (chainModel C) Q N) (hP : C.P.Simple)
    (hne : (N.F (chainModel C) Q).Nonempty) {j : ℕ} (hj : j < N.arcs.length) {y : ℝ}
    (hl1 : ¬ (chainModel C).IsCut (N.F (chainModel C) Q) y →
      sideInArc (sk (chainModel C) Q N j) (ek (chainModel C) Q N j) y)
    (hl2 : (chainModel C).IsCut (N.F (chainModel C) Q) y →
      sk (chainModel C) Q N j = y ∨ ek (chainModel C) Q N j = y) :
    Before C Q N (if sk (chainModel C) Q N j = y then predP N.arcs.length j else j) y := by
  by_cases hc : (chainModel C).IsCut (N.F (chainModel C) Q) y
  · split_ifs with hs
    · have hpj := predP_lt hj
      have := ek_eq_sk_succ hN hP hne hpj
      rw [succP_predP hj, hs] at this
      rw [← this]; exact before_end hN hne hpj
    · rcases hl2 hc with h | h
      · exact absurd h hs
      · rw [← h]; exact before_end hN hne hj
  · have hin := hl1 hc
    have hs : ¬ sk (chainModel C) Q N j = y := by
      intro h; rw [← h] at hin; unfold sideInArc at hin; split_ifs at hin <;> simp at hin
      linarith
    rw [ite_eq_right hs]
    obtain ⟨δ, hδ, h⟩ := int_nhd hin
    exact ⟨δ, hδ, fun ε e1 e2 => (h ε e1 e2).1⟩

open Classical in
/-- **The arc just after a located key.** -/
theorem after_of_loc (hN : IsNF (chainModel C) Q N) (hP : C.P.Simple)
    (hne : (N.F (chainModel C) Q).Nonempty) {j : ℕ} (hj : j < N.arcs.length) {y : ℝ}
    (hl1 : ¬ (chainModel C).IsCut (N.F (chainModel C) Q) y →
      sideInArc (sk (chainModel C) Q N j) (ek (chainModel C) Q N j) y)
    (hl2 : (chainModel C).IsCut (N.F (chainModel C) Q) y →
      sk (chainModel C) Q N j = y ∨ ek (chainModel C) Q N j = y) :
    After C Q N (if ek (chainModel C) Q N j = y then succP N.arcs.length j else j) y := by
  by_cases hc : (chainModel C).IsCut (N.F (chainModel C) Q) y
  · split_ifs with he
    · have := ek_eq_sk_succ hN hP hne hj
      rw [he] at this
      rw [this]; exact after_start hN hne (succP_lt hj)
    · rcases hl2 hc with h | h
      · rw [← h]; exact after_start hN hne hj
      · exact absurd h he
  · have hin := hl1 hc
    have he : ¬ ek (chainModel C) Q N j = y := by
      intro h; rw [← h] at hin; unfold sideInArc at hin; split_ifs at hin <;> simp at hin
      linarith
    rw [ite_eq_right he]
    obtain ⟨δ, hδ, h⟩ := int_nhd hin
    exact ⟨δ, hδ, fun ε e1 e2 => (h ε e1 e2).2⟩

theorem before_unique (hN : IsNF (chainModel C) Q N) (hP : C.P.Simple)
    (hne : (N.F (chainModel C) Q).Nonempty) {q q' : ℕ} (hq : q < N.arcs.length)
    (hq' : q' < N.arcs.length) {y : ℝ} (h : Before C Q N q y) (h' : Before C Q N q' y) :
    q = q' := by
  have hGM : GoodModel (chainModel C) := Or.inl ⟨C, hP, rfl⟩
  obtain ⟨δ, hδ, h⟩ := h
  obtain ⟨δ', hδ', h'⟩ := h'
  have e0 : 0 < min δ δ' / 2 := by have := lt_min hδ hδ'; linarith
  have e1 : min δ δ' / 2 < δ := by have := min_le_left δ δ'; linarith
  have e2 : min δ δ' / 2 < δ' := by have := min_le_right δ δ'; linarith
  exact interior_unique hN hGM hne hq hq' (h _ e0 e1) (h' _ e0 e2)

theorem after_unique (hN : IsNF (chainModel C) Q N) (hP : C.P.Simple)
    (hne : (N.F (chainModel C) Q).Nonempty) {q q' : ℕ} (hq : q < N.arcs.length)
    (hq' : q' < N.arcs.length) {y : ℝ} (h : After C Q N q y) (h' : After C Q N q' y) :
    q = q' := by
  have hGM : GoodModel (chainModel C) := Or.inl ⟨C, hP, rfl⟩
  obtain ⟨δ, hδ, h⟩ := h
  obtain ⟨δ', hδ', h'⟩ := h'
  have e0 : 0 < min δ δ' / 2 := by have := lt_min hδ hδ'; linarith
  have e1 : min δ δ' / 2 < δ := by have := min_le_left δ δ'; linarith
  have e2 : min δ δ' / 2 < δ' := by have := min_le_right δ δ'; linarith
  exact interior_unique hN hGM hne hq hq' (h _ e0 e1) (h' _ e0 e2)

end Zip

end OracleQ

end

end Chazelle.Core
