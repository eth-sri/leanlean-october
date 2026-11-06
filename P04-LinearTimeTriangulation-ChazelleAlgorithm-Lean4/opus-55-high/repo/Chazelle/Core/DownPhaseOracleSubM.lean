module

public import Chazelle.Core.DownPhaseOracleTop
public import Chazelle.Core.BruteCorner

/-!
# WP-M (E7-B, part 8): the mathematics of one sub-query

A sub-query of the interior oracles serves a subarc of `L ≤ n - 1` walk edges of the interior
walk of `Q` from the walk vertex `u` through the chain `C = ch Q u L` of `Q` (start
`cs = cStart Q u L`, `L` edges).  This file collects the facts the RAM needs about `C`:

* `ch_vertex`: the chain vertices are `Q.vtx ((cs + k) mod n)`;
* `rng_of`, `of_rng`: the vertex set of `C` is the union of the index ranges
  `[cs, y₁] ∪ [x₂, y₂]` (`y₁ = min (cs + L) (n - 1)`; the second range is `[0, cs + L - n]` when the
  chain passes the last edge, `[cs, cs]` otherwise);
* `topIdx_ch`: the top index is `(v + n - cs) mod n` for the highest chain vertex `v`;
* `sideBeta_ch`: the orientation bit from six sign tests at the top (indices modulo `n`);
* `cVtx_ch`, `hitSym_ch`: the boundary symbolic point of a chain-model hit, in closed form;
* `firstHit_union`, `noHit_union`: first hits on a union of two point sets.
-/

namespace Chazelle.Core

namespace IOrc

@[expose] public section

open Set
open Chazelle.Chain (sideE sideInArc)
open Chazelle.Visibility (rayPt)

variable {Q : Polygon}

/-! ## The chain of a stretch -/

theorem ch_vertex {u L : ℕ} {h1 : 1 ≤ L} {h2 : L + 1 ≤ Q.n} (k : ℕ) :
    (ch Q u L h1 h2).vertex k = Q.vtx ((cStart Q u L + k) % Q.n) := rfl

/-! ## The vertex ranges of a chain -/

/-- The end of the first index range. -/
def rY1 (n cs L : ℕ) : ℕ := if cs + L < n then cs + L else n - 1

/-- The start of the second index range. -/
def rX2 (n cs L : ℕ) : ℕ := if cs + L < n then cs else 0

/-- The end of the second index range. -/
def rY2 (n cs L : ℕ) : ℕ := if cs + L < n then cs else cs + L - n

/-- The vertex indices of a chain of `L ≤ n - 1` edges from `cs`. -/
def InCh (n cs L v : ℕ) : Prop := ∃ k, k ≤ L ∧ v = (cs + k) % n

theorem rng_of {n cs L k : ℕ} (hcs : cs < n) (hL : L < n) (hk : k ≤ L) :
    (cs ≤ (cs + k) % n ∧ (cs + k) % n ≤ rY1 n cs L) ∨
      (rX2 n cs L ≤ (cs + k) % n ∧ (cs + k) % n ≤ rY2 n cs L) := by
  unfold rY1 rX2 rY2
  by_cases h : cs + k < n
  · left; rw [Nat.mod_eq_of_lt h]; split_ifs <;> omega
  · right
    rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    split_ifs <;> omega

theorem of_rng1 {n cs L v : ℕ} (hcs : cs < n) (h1 : cs ≤ v) (h2 : v ≤ rY1 n cs L) :
    InCh n cs L v := by
  unfold rY1 at h2
  refine ⟨v - cs, by split_ifs at h2 <;> omega, ?_⟩
  rw [show cs + (v - cs) = v by omega, Nat.mod_eq_of_lt (by split_ifs at h2 <;> omega)]

theorem of_rng2 {n cs L v : ℕ} (hcs : cs < n) (hL : L < n) (h1 : rX2 n cs L ≤ v)
    (h2 : v ≤ rY2 n cs L) : InCh n cs L v := by
  unfold rX2 rY2 at *
  by_cases h : cs + L < n
  · rw [ite_eq_left h] at h1 h2
    exact ⟨0, by omega, by rw [Nat.add_zero, Nat.mod_eq_of_lt hcs]; omega⟩
  · rw [ite_eq_right h] at h1 h2
    refine ⟨v + n - cs, by omega, ?_⟩
    rw [show cs + (v + n - cs) = v + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem rY1_lt {n cs L : ℕ} (hcs : cs < n) : rY1 n cs L < n := by
  unfold rY1; split_ifs <;> omega

theorem rY2_lt {n cs L : ℕ} (hcs : cs < n) (hL : L < n) : rY2 n cs L < n := by
  unfold rY2; split_ifs <;> omega

theorem rX2_le {n cs L : ℕ} (_hcs : cs < n) (_hL : L < n) : rX2 n cs L ≤ rY2 n cs L := by
  unfold rX2 rY2; split_ifs <;> omega

theorem cs_le_rY1 {n cs L : ℕ} (hcs : cs < n) : cs ≤ rY1 n cs L := by
  unfold rY1; split_ifs <;> omega

theorem rY1_sub {n cs L : ℕ} : rY1 n cs L - cs ≤ L := by
  unfold rY1; split_ifs <;> omega

theorem rY2_sub {n cs L : ℕ} (hcs : cs < n) : rY2 n cs L - rX2 n cs L ≤ L := by
  unfold rX2 rY2; split_ifs <;> omega

/-! ## The top of the chain -/

/-- **The top index of the chain of a stretch** from its highest vertex `v` (distinct heights). -/
theorem topIdx_ch (hD : DistinctHeights Q) {u L : ℕ} {h1 : 1 ≤ L} {h2 : L + 1 ≤ Q.n}
    {v : ℕ} (hv : InCh Q.n (cStart Q u L) L v)
    (hmax : ∀ k, k ≤ L → (Q.vtx ((cStart Q u L + k) % Q.n)).2 ≤ (Q.vtx v).2)
    (hu : cStart Q u L < Q.n) :
    (ch Q u L h1 h2).topIdx = (v + Q.n - cStart Q u L) % Q.n ∧
      (cStart Q u L + (ch Q u L h1 h2).topIdx) % Q.n = v := by
  obtain ⟨j, hj, rfl⟩ := hv
  have hT : (ch Q u L h1 h2).topIdx = j :=
    topIdx_of_max (C := ch Q u L h1 h2) hD hj (fun k hk => by
      rw [ch_vertex, ch_vertex]; exact hmax k hk)
  refine ⟨?_, by rw [hT]⟩
  rw [hT]
  have hjn : j < Q.n := by omega
  by_cases h : cStart Q u L + j < Q.n
  · have e1 : (cStart Q u L + j) % Q.n = cStart Q u L + j := Nat.mod_eq_of_lt h
    rw [e1, show cStart Q u L + j + Q.n - cStart Q u L = j + Q.n by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt hjn]
  · have e1 : (cStart Q u L + j) % Q.n = cStart Q u L + j - Q.n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [e1, show cStart Q u L + j - Q.n + Q.n - cStart Q u L = j by omega, Nat.mod_eq_of_lt hjn]

/-! ## The orientation bit -/

/-- The combination of the six sign tests giving the orientation bit (`BruteCorner.sideBeta_iff`)
for the vertices `A`, `T`, `B` before, at and after the top. -/
def BetaF (A T B : Point) : Prop :=
  (0 < det A T B ∧ T.1 < B.1 ∧ A.1 < T.1) ∨
    (¬ 0 < det A T B ∧ ¬ det A T B = 0 ∧ (T.1 < B.1 ∨ A.1 < T.1)) ∨
    (det A T B = 0 ∧ T.2 < B.2 ∧ T.1 < B.1) ∨ (det A T B = 0 ∧ B.2 < T.2)

theorem prev_idx {n s T : ℕ} (hn : 1 < n) (hT : 1 ≤ T) :
    (s + (T - 1)) % n = ((s + T) % n + n - 1) % n := sub_idx (by omega) hT (by omega)

/-- **The orientation bit of a chain of `Q`** (top not the first vertex), with the vertex indices
of `Q` taken modulo `n`. -/
theorem sideBeta_ch {C : Chain} (hC : C.P = Q) (hD : DistinctHeights Q) (hT0 : 0 < C.topIdx)
    {v : ℕ} (hv : v = (C.s + C.topIdx) % Q.n) :
    C.sideBeta = true ↔ BetaF (Q.vtx ((v + Q.n - 1) % Q.n)) (Q.vtx v) (Q.vtx ((v + 1) % Q.n)) := by
  have hDH : DistinctHeights C.P := by rw [hC]; exact hD
  have hn : 1 < Q.n := by have := C.add_one_le; have := C.one_le; rw [hC] at *; omega
  have eA : C.vertex (C.topIdx - 1) = Q.vtx ((v + Q.n - 1) % Q.n) := by
    show C.P.vtx ((C.s + (C.topIdx - 1)) % C.P.n) = _
    rw [hC, prev_idx hn hT0, hv]
  have eT : C.top = Q.vtx v := by
    show C.P.vtx ((C.s + C.topIdx) % C.P.n) = _
    rw [hC, hv]
  have eB : C.vertex (C.topIdx + 1) = Q.vtx ((v + 1) % Q.n) := by
    show C.P.vtx ((C.s + (C.topIdx + 1)) % C.P.n) = _
    rw [hC, hv, Nat.mod_add_mod, Nat.add_assoc]
  rw [Brute.sideBeta_iff (C := C) hDH hT0, eA, eT, eB]
  unfold BetaF
  constructor
  · rintro (h | ⟨h1, h3⟩ | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨not_lt.2 h1.le, h1.ne, h3⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rintro (h | ⟨h1, h2, h3⟩ | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨lt_of_le_of_ne (not_lt.1 h1) h2, h3⟩)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

/-! ## The boundary symbolic point of a hit, in closed form -/

/-- The tour start: `sideS`. -/
def sSV (β : Bool) (T L : ℕ) : ℕ := if β then T else 2 * L - T

/-- `j mod 2L` for `j < 6L`, by two conditional subtractions. -/
def mod2 (L j : ℕ) : ℕ :=
  if 2 * L ≤ (if 2 * L ≤ j then j - 2 * L else j) then (if 2 * L ≤ j then j - 2 * L else j) - 2 * L
  else (if 2 * L ≤ j then j - 2 * L else j)

theorem mod2_eq {L j : ℕ} (_hL : 1 ≤ L) (hj : j < 6 * L) : mod2 L j = j % (2 * L) := by
  unfold mod2
  by_cases h1 : 2 * L ≤ j
  · rw [ite_eq_left h1]
    by_cases h2 : 2 * L ≤ j - 2 * L
    · rw [ite_eq_left h2, Nat.mod_eq_sub_mod h1, Nat.mod_eq_sub_mod h2, Nat.mod_eq_of_lt (by omega)]
    · rw [ite_eq_right h2, Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
  · rw [ite_eq_right h1, ite_eq_right h1, Nat.mod_eq_of_lt (by omega)]

/-- The vertex index of `Q` at the walk vertex `6 + i` (`i ≤ 2L`) of the chain model. -/
def cVtxV (n cs L S i : ℕ) : ℕ :=
  (cs + sideE L (mod2 L (S + i))) % n

theorem cVtx_ch {C : Chain} {i : ℕ} (hi : i ≤ 2 * C.m) :
    cVtx C (i + 6) = cVtxV C.P.n C.s C.m (sSV C.sideBeta C.topIdx C.m) i := by
  unfold cVtx cVtxV Chain.sideIdx
  have hT := C.topIdx_le
  have hm := C.one_le
  have hS : C.sideS C.sideBeta = sSV C.sideBeta C.topIdx C.m := by
    unfold Chain.sideS sSV; rfl
  rw [show i + 6 - 6 = i by omega, hS, mod2_eq hm (by unfold sSV; split_ifs <;> omega)]

/-- **The boundary symbolic point of a chain-model position**, in closed form (`v` the top vertex
of `Q`, `S` the tour start). -/
noncomputable def hitSymV (n cs L S v e h : ℕ) : SymPt := by
  classical
  exact if e < 6 ∨ 2 * L + 6 ≤ e then .vtx v
    else if h = 0 ∨ h - 1 = cVtxV n cs L S (e - 6) then .vtx (cVtxV n cs L S (e - 6))
    else .onEdge (ShootCut.edgeOf n (.vtx (cVtxV n cs L S (e - 6)))
      (.vtx (cVtxV n cs L S (e - 6 + 1)))) (h - 1)

theorem hitSym_ch {C : Chain} {v : ℕ} (hv : v = (C.s + C.topIdx) % C.P.n) {e h : ℕ}
    (_he : e < 2 * C.m + 7) :
    hitSym C e h = hitSymV C.P.n C.s C.m (sSV C.sideBeta C.topIdx C.m) v e h := by
  unfold hitSym hitSymV
  by_cases h6 : e < 6 ∨ 2 * C.m + 6 ≤ e
  · rw [ite_eq_left h6, ite_eq_left h6, hv]
  · rw [ite_eq_right h6, ite_eq_right h6]
    have e1 : cVtx C e = cVtxV C.P.n C.s C.m (sSV C.sideBeta C.topIdx C.m) (e - 6) := by
      rw [← cVtx_ch (by omega), show e - 6 + 6 = e by omega]
    have e2 : cVtx C (e + 1) = cVtxV C.P.n C.s C.m (sSV C.sideBeta C.topIdx C.m) (e - 6 + 1) := by
      rw [← cVtx_ch (by omega), show e - 6 + 1 + 6 = e + 1 by omega]
    rw [e1, e2]

/-! ## First hits on a union -/

theorem firstHit_union_l {A B : Set Point} {z : Point} {σ t : ℝ} (hA : FirstHit A z σ t)
    (hB : ∀ t', 0 < t' → t' < t → rayPt z σ t' ∉ B) : FirstHit (A ∪ B) z σ t :=
  ⟨hA.1, Or.inl hA.2.1, fun t' h0 h1 hm => hm.elim (hA.2.2 t' h0 h1) (hB t' h0 h1)⟩

theorem firstHit_union_r {A B : Set Point} {z : Point} {σ t : ℝ} (hB : FirstHit B z σ t)
    (hA : ∀ t', 0 < t' → t' < t → rayPt z σ t' ∉ A) : FirstHit (A ∪ B) z σ t := by
  rw [Set.union_comm]; exact firstHit_union_l hB hA

theorem firstHit_noHit {A B : Set Point} {z : Point} {σ t : ℝ} (hA : FirstHit A z σ t)
    (hB : NoHit B z σ) : FirstHit (A ∪ B) z σ t :=
  firstHit_union_l hA fun t' h0 _ => hB t' h0

theorem noHit_firstHit {A B : Set Point} {z : Point} {σ t : ℝ} (hA : NoHit A z σ)
    (hB : FirstHit B z σ t) : FirstHit (A ∪ B) z σ t :=
  firstHit_union_r hB fun t' h0 _ => hA t' h0

theorem noHit_union {A B : Set Point} {z : Point} {σ : ℝ} (hA : NoHit A z σ) (hB : NoHit B z σ) :
    NoHit (A ∪ B) z σ := fun t h0 hm => hm.elim (hA t h0) (hB t h0)

/-- Two first hits: the nearer one. -/
theorem firstHit_min {A B : Set Point} {z : Point} {σ t₁ t₂ : ℝ} (hA : FirstHit A z σ t₁)
    (hB : FirstHit B z σ t₂) (h : t₁ ≤ t₂) : FirstHit (A ∪ B) z σ t₁ :=
  firstHit_union_l hA fun t' h0 h1 => hB.2.2 t' h0 (lt_of_lt_of_le h1 h)

end

end IOrc

end Chazelle.Core
