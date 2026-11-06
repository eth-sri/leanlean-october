module

public import Chazelle.Core.RestoreTArcs
public import Chazelle.Core.SweepPrimArr

/-!
# WP-E, the candidate test on the RAM: the positions of the origin (the holes)

The shot wrapper must not shoot at a piece containing the origin `z`, so the test removes the
walk edges through every position of `z` ("holes": open key intervals between walk vertices).
This file lists the positions:

* a point inside an open edge of the chain of a chain model is at the tour edge `i` and at its
  twin `tourTwin C i` (`chain_open_positions`);
* a chain vertex `k` is at the tour vertices `candIdx k`, `candIdx (2m - k)` and, for the top,
  `2m` (`SweepPrim.vertex_positions`, `SweepPrim.cand_complete`);
* a point of the interior model is at a single position (`FactsInterior.pos_unique`);

and the hole vocabulary: the edge hole `eHole` of a walk edge and the vertex hole `vHole` of a
walk vertex, which contain the keys of the positions.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Set
open Chazelle.Chain (sideE sidePt sideInArc)
open Chazelle.Geometry (lerp)
open SweepPrim

/-! ## Tour indices -/

theorem tour_mod {m S a : ℕ} (hS : S ≤ 2 * m) (ha : a < 2 * m) :
    (S + a) % (2 * m) = if S + a < 2 * m then S + a else S + a - 2 * m := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

/-- The tour position determines the tour step. -/
theorem tour_inj {m S a b : ℕ} (hS : S ≤ 2 * m) (ha : a < 2 * m) (hb : b < 2 * m)
    (h : (S + a) % (2 * m) = (S + b) % (2 * m)) : a = b := by
  rw [tour_mod hS ha, tour_mod hS hb] at h
  split_ifs at h <;> omega

/-- The tour positions of the chain edge `k`: `k` going up and `2m - 1 - k` going down. -/
theorem cover_pos {m j k : ℕ} (hj : j < 2 * m) (hk : k < m)
    (h : (sideE m j = k ∧ sideE m (j + 1) = k + 1) ∨ (sideE m j = k + 1 ∧ sideE m (j + 1) = k)) :
    j = k ∨ j = 2 * m - 1 - k := by
  unfold sideE at h; split_ifs at h <;> omega

/-! ## Positions in a chain model -/

variable {C : Chain}

/-- **The positions of a point inside an open chain edge** are the tour edge and its twin. -/
theorem chain_open_positions (hP : C.P.Simple) {i : ℕ} (hi : i < 2 * C.m) {t : ℝ} (ht : 0 < t)
    (ht1 : t < 1) {p' : ℕ} {t' : ℝ} (hp' : p' < (chainModel C).W.n) (ht' : 0 ≤ t')
    (ht1' : t' < 1)
    (heq : sidePt (chainModel C).W p' t' = sidePt (chainModel C).W (i + 6) t) :
    0 < t' ∧ (p' = i + 6 ∨ p' = tourTwin C i + 6) := by
  have hW : (chainModel C).W = C.sideWalk C.sideBeta := rfl
  rw [hW] at heq hp'
  have hm := C.one_le
  have hS := C.sideS_lt C.sideBeta
  obtain ⟨k, hk, s, hs, hz, hcov⟩ := C.sideTour_open C.sideBeta hi ⟨ht, ht1⟩
  have hzmem : sidePt (C.sideWalk C.sideBeta) (i + 6) t ∈ C.set :=
    C.sideWalk_tour_pt_mem C.sideBeta hi.le (fun h => absurd h (by omega)) ht.le ht1
  rcases C.sideWalk_pos_cases C.sideBeta hp' ht' with hbox | ⟨i', hi', rfl, hit'⟩
  · exact absurd (heq ▸ hzmem) (C.sideWalk_box_pt C.sideBeta hbox ht' ht1').1
  -- a tour position
  rcases ht'.lt_or_eq with ht'0 | ht'0
  swap
  · exfalso
    subst ht'0
    rw [Chazelle.Chain.sidePt_zero, C.sideWalk_vtx_tour _ hi', hz] at heq
    exact C.sideOpen_ne_vertex hP hs heq.symm
  have hi'2 : i' < 2 * C.m := by
    rcases hi'.lt_or_eq with h | h
    · exact h
    · exact absurd (hit' h) ht'0.ne'
  obtain ⟨k', hk', s', hs', hz', hcov'⟩ := C.sideTour_open C.sideBeta hi'2 ⟨ht'0, ht1'⟩
  -- the same chain edge
  have hkk : k' = k := by
    by_contra hne
    have hlk : C.edgeIdx k' ≠ C.edgeIdx k := fun h =>
      hne (C.sideEdgeIdx_inj (by omega) (by omega) h)
    have e1 : ∀ q : ℕ, C.vertex (q + 1) = C.P.vtx ((C.edgeIdx q + 1) % C.P.n) := fun q => by
      unfold Chain.vertex; rw [C.edgeIdx_succ]
    have h2 : lerp (C.vertex k') (C.vertex (k' + 1)) s' = lerp (C.vertex k) (C.vertex (k + 1)) s := by
      rw [← hz', heq, hz]
    have hmem : lerp (C.vertex k) (C.vertex (k + 1)) s ∈ C.P.edge (C.edgeIdx k) := by
      rw [e1]; exact Geometry.lerp_mem_segment _ _ hs.1.le hs.2.le
    have := Jordan.simple_openEdge_not_mem_other hP (C.edgeIdx_lt k') hs' (C.edgeIdx_lt k)
      (Ne.symm hlk)
    apply this
    rwa [show C.P.vtx (C.edgeIdx k') = C.vertex k' from rfl, ← e1 k', h2]
  subst hkk
  -- the tour positions of the chain edge
  rw [C.sideIdx_eq, C.sideIdx_succ] at hcov hcov'
  have hj := Nat.mod_lt (C.sideS C.sideBeta + i) (show 0 < 2 * C.m by omega)
  have hj' := Nat.mod_lt (C.sideS C.sideBeta + i') (show 0 < 2 * C.m by omega)
  have c1 := cover_pos hj hk' hcov
  have c2 := cover_pos hj' hk' hcov'
  refine ⟨ht'0, ?_⟩
  by_cases hsame : (C.sideS C.sideBeta + i') % (2 * C.m) = (C.sideS C.sideBeta + i) % (2 * C.m)
  · left; rw [tour_inj hS hi'2 hi hsame]
  · right
    obtain ⟨h1, h2⟩ := candIdx_mod (m := C.m) (j := 2 * C.m - 1 - (C.sideS C.sideBeta + i) %
      (2 * C.m)) hS (by omega)
    have htw : tourTwin C i = candIdx C.m (C.sideS C.sideBeta)
        (2 * C.m - 1 - (C.sideS C.sideBeta + i) % (2 * C.m)) := rfl
    rw [← htw] at h1 h2
    have : (C.sideS C.sideBeta + i') % (2 * C.m) = (C.sideS C.sideBeta + tourTwin C i) %
        (2 * C.m) := by rw [h1]; omega
    rw [tour_inj hS hi'2 h2 this]

/-- **The positions of a chain vertex** are the candidates of its index (and the last tour vertex
for the top). -/
theorem chain_vertex_positions (hP : C.P.Simple) {k : ℕ} (hk : k ≤ C.m) {p' : ℕ} {t' : ℝ}
    (hp' : p' < (chainModel C).W.n) (ht' : 0 ≤ t') (ht1' : t' < 1)
    (heq : sidePt (chainModel C).W p' t' = C.vertex k) :
    t' = 0 ∧ (p' = candIdx C.m (C.sideS C.sideBeta) k + 6 ∨
      p' = candIdx C.m (C.sideS C.sideBeta) (2 * C.m - k) + 6 ∨
      (p' = 2 * C.m + 6 ∧ k = C.topIdx)) := by
  obtain ⟨h0, i, hi, rfl, hik⟩ := vertex_positions C hP hk hp' ht' ht1' heq
  refine ⟨h0, ?_⟩
  rcases cand_complete C C.sideBeta hi hik with h | h | h
  · left; rw [h]
  · right; left; rw [h]
  · right; right; refine ⟨by rw [h], ?_⟩
    rw [← hik, h, C.sideIdx_two_m]

/-! ## Holes -/

/-- The walk vertex before `q`. -/
def prevV (n q : ℕ) : ℕ := (q + n - 1) % n

/-- The hole of the walk edge `p`: the open key interval `(p, p + 1)`. -/
def eHole (n p : ℕ) : WPos × WPos := (⟨p, 0⟩, ⟨(p + 1) % n, 0⟩)

/-- The hole of the walk vertex `q`: the open key interval `(q - 1, q + 1)`. -/
def vHole (n q : ℕ) : WPos × WPos := (⟨prevV n q, 0⟩, ⟨(q + 1) % n, 0⟩)

/-- The key of a hole vertex. -/
theorem key_hole (M : Model) (Q : Polygon) (v : ℕ) : M.key Q ⟨v, 0⟩ = v := key_vtx' M Q v

/-- **An edge hole contains the keys of the open edge.** -/
theorem eHole_mem {n p : ℕ} (hp : p < n) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    sideInArc (p : ℝ) (((p + 1) % n : ℕ) : ℝ) ((p : ℝ) + t) := by
  unfold sideInArc
  rcases Nat.lt_or_ge (p + 1) n with h | h
  · rw [Nat.mod_eq_of_lt h]
    push_cast
    rw [ite_eq_left (by linarith)]; constructor <;> linarith
  · rw [show p + 1 = n by omega, Nat.mod_self]
    push_cast
    rw [ite_eq_right (by have : (0 : ℝ) ≤ p := Nat.cast_nonneg _; linarith)]
    left; linarith

/-- **A vertex hole contains the key of the vertex.** -/
theorem vHole_mem {n q : ℕ} (hn : 3 ≤ n) (hq : q < n) :
    sideInArc ((prevV n q : ℕ) : ℝ) (((q + 1) % n : ℕ) : ℝ) ((q : ℝ) + 0) := by
  rw [add_zero]
  unfold sideInArc prevV
  rcases Nat.eq_zero_or_pos q with h0 | h0
  · subst h0
    rw [show 0 + n - 1 = n - 1 by omega, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    push_cast
    rw [ite_eq_right (by norm_num; omega)]
    right; norm_num
  · rw [show q + n - 1 = (q - 1) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rcases Nat.lt_or_ge (q + 1) n with h | h
    · rw [Nat.mod_eq_of_lt h]
      rw [ite_eq_left (by exact_mod_cast (show q - 1 < q + 1 by omega))]
      constructor <;> exact_mod_cast (by omega)
    · rw [show q + 1 = n by omega, Nat.mod_self]
      rw [ite_eq_right (by push_cast; norm_num)]
      left; exact_mod_cast (show q - 1 < q by omega)

/-- A key `0` inside an interval with ends below `n` means the key `n` is inside it too. -/
theorem sideInArc_zero_n {a b : ℝ} {n : ℕ} (ha0 : 0 ≤ a) (ha : a < n) (h : sideInArc a b ((0 : ℕ) + 0)) :
    sideInArc a b (n : ℝ) := by
  unfold sideInArc at h ⊢
  push_cast at h
  split_ifs at h ⊢ with h1
  · linarith [h.1]
  · left; exact ha

/-! ## Covering the positions of the origin -/

/-- **The holes cover the origin**: every position of `z` has its key in an open hole. -/
def Cover (M : Model) (Q : Polygon) (hs : List (WPos × WPos)) (z : Point) : Prop :=
  ∀ p : ℕ, ∀ t : ℝ, p < M.W.n → 0 ≤ t → t < 1 → sidePt M.W p t = z →
    ∃ g ∈ hs, sideInArc (M.key Q g.1) (M.key Q g.2) ((p : ℝ) + t)

/-- **Covering the origin avoids it** (`ShotList.Avoid`), for holes between walk vertices. -/
theorem avoid_of_cover {M : Model} {Q : Polygon} {hs : List (WPos × WPos)} {z : Point}
    (hc : Cover M Q hs z) (hv : ∀ g ∈ hs, g.1.hgt = 0 ∧ g.1.edge < M.W.n)
    (m : ℕ → ℕ) (A K : ℕ) : ShotList.Avoid M Q m A K hs z := by
  intro p t hp ht0 ht1 hz j hj _
  rcases ht1.lt_or_eq with ht1 | ht1
  · exact hc p t hp ht0 ht1 hz
  · subst ht1
    have hn : 0 < M.W.n := by omega
    have hz' : sidePt M.W ((p + 1) % M.W.n) 0 = z := by
      rw [Chazelle.Chain.sidePt_zero, ← hz]; simp [Model.wb, Geometry.lerp]
    obtain ⟨g, hg, hin⟩ := hc _ 0 (Nat.mod_lt _ hn) le_rfl one_pos hz'
    refine ⟨g, hg, ?_⟩
    rcases Nat.lt_or_ge (p + 1) M.W.n with h | h
    · rw [Nat.mod_eq_of_lt h] at hin; push_cast at hin ⊢; rwa [add_zero] at hin
    · rw [show p + 1 = M.W.n by omega, Nat.mod_self] at hin
      obtain ⟨g1, g1e⟩ := hv g hg
      have hk : M.key Q g.1 = g.1.edge := by
        obtain ⟨⟨e, h⟩, _⟩ := g; simp only at g1 ⊢; subst g1; exact key_vtx' M Q e
      have e1 : ((p : ℝ) + 1) = ((M.W.n : ℕ) : ℝ) := by exact_mod_cast (show p + 1 = M.W.n by omega)
      rw [e1]
      exact sideInArc_zero_n (by rw [hk]; exact Nat.cast_nonneg _)
        (by rw [hk]; exact_mod_cast g1e) hin

/-- **The chain vertex holes.** -/
theorem cover_chain_vertex (hP : C.P.Simple) {k : ℕ} (hk : k ≤ C.m) {hs : List (WPos × WPos)}
    (h1 : vHole (chainModel C).W.n (candIdx C.m (C.sideS C.sideBeta) k + 6) ∈ hs)
    (h2 : vHole (chainModel C).W.n (candIdx C.m (C.sideS C.sideBeta) (2 * C.m - k) + 6) ∈ hs)
    (h3 : k = C.topIdx → vHole (chainModel C).W.n (2 * C.m + 6) ∈ hs) (Q : Polygon) :
    Cover (chainModel C) Q hs (C.vertex k) := by
  intro p t hp ht0 ht1 hz
  have hn : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _
  obtain ⟨rfl, hpc⟩ := chain_vertex_positions hP hk hp ht0 ht1 hz
  have mem : ∀ q, q < (chainModel C).W.n → vHole (chainModel C).W.n q ∈ hs → p = q →
      ∃ g ∈ hs, sideInArc ((chainModel C).key Q g.1) ((chainModel C).key Q g.2)
        ((p : ℝ) + 0) := fun q hq hm hpq => by
    refine ⟨_, hm, ?_⟩
    simp only [vHole, key_hole]
    subst hpq
    exact vHole_mem (by omega) hq
  rcases hpc with h | h | ⟨h, hkt⟩
  · exact mem _ (by omega) h1 h
  · exact mem _ (by omega) h2 h
  · exact mem _ (by omega) (h3 hkt) h

/-- **The chain edge holes.** -/
theorem cover_chain_edge (hP : C.P.Simple) {i : ℕ} (hi : i < 2 * C.m) {τ : ℝ} (hτ : 0 < τ)
    (hτ1 : τ < 1) {hs : List (WPos × WPos)}
    (h1 : eHole (chainModel C).W.n (i + 6) ∈ hs)
    (h2 : eHole (chainModel C).W.n (tourTwin C i + 6) ∈ hs) (Q : Polygon) :
    Cover (chainModel C) Q hs (sidePt (chainModel C).W (i + 6) τ) := by
  intro p t hp ht0 ht1 hz
  obtain ⟨htp, hpc⟩ := chain_open_positions hP hi hτ hτ1 hp ht0 ht1 hz
  have mem : ∀ q, vHole (chainModel C).W.n q = vHole (chainModel C).W.n q →
      eHole (chainModel C).W.n q ∈ hs → p = q →
      ∃ g ∈ hs, sideInArc ((chainModel C).key Q g.1) ((chainModel C).key Q g.2)
        ((p : ℝ) + t) := fun q _ hm hpq => by
    refine ⟨_, hm, ?_⟩
    simp only [eHole, key_hole]
    subst hpq
    exact eHole_mem hp htp ht1
  rcases hpc with h | h
  · exact mem _ rfl h1 h
  · exact mem _ rfl h2 h

/-- **The interior holes**: the origin has a single position. -/
theorem cover_unique {M : Model} (hW : M.W.Simple) {e : ℕ} (he : e < M.W.n) {τ : ℝ} (hτ0 : 0 ≤ τ)
    (hτ1 : τ < 1) {hs : List (WPos × WPos)} (h3 : 3 ≤ M.W.n)
    (hv : τ = 0 → vHole M.W.n e ∈ hs) (he' : 0 < τ → eHole M.W.n e ∈ hs) (Q : Polygon) :
    Cover M Q hs (sidePt M.W e τ) := by
  intro p t hp ht0 ht1 hz
  obtain ⟨rfl, rfl⟩ := FactsInterior.pos_unique hW hp he ht0 ht1 hτ0 hτ1 hz
  rcases ht0.lt_or_eq with h | h
  · refine ⟨_, he' h, ?_⟩
    simp only [eHole, key_hole]
    exact eHole_mem hp h ht1
  · subst h
    refine ⟨_, hv rfl, ?_⟩
    simp only [vHole, key_hole]
    exact vHole_mem h3 hp

end

end Restore

end Chazelle.Core
