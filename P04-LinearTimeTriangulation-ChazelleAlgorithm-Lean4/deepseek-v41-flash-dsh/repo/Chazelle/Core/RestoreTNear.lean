module

public import Chazelle.Golf

public import Chazelle.Core.RestoreTHoleMath
public import Chazelle.Core.ShotListMath

/-!
# WP-E, the candidate test: the holes are near the candidate

The shot of the candidate test cuts the arcs of the region by the holes of the candidate (the walk
edges through the candidate point, as closed key intervals of walk vertices).  For the exit point
of the ray to survive the cut, every walk point with a key in a hole must lie on a walk edge
through the candidate (`Near`): then `RestoreHoles.no_common_edge` rules it out.

* `edge_keys`: a position whose key lies in the closed key interval `[e, e + 1]` of the walk edge
  `e` is a point of that edge.
* `vtx_keys_split`: the key interval of a vertex hole is the union of those of its two edges.
* `near_eHole`, `near_vHole`: edge holes and vertex holes are near the points of their edges.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Chazelle.Chain (sidePt sideInArc sidePt_zero)
open ShotList

/-- **The holes are near `z`**: every walk point with a key in a closed hole lies on a walk edge
through `z`. -/
def Near (M : Model) (Q : Polygon) (hs : List (WPos × WPos)) (z : Point) : Prop :=
  ∀ g ∈ hs, ∀ p : ℕ, ∀ τ : ℝ, p < M.W.n → 0 ≤ τ → τ ≤ 1 →
    CIn (M.key Q g.1) (M.key Q g.2) ((p : ℝ) + τ) →
    ∃ p', p' < M.W.n ∧ (∃ t₁ : ℝ, 0 ≤ t₁ ∧ t₁ ≤ 1 ∧ sidePt M.W p' t₁ = z) ∧
      ∃ t₂ : ℝ, 0 ≤ t₂ ∧ t₂ ≤ 1 ∧ sidePt M.W p' t₂ = sidePt M.W p τ

theorem sidePt_one' (W : Polygon) (p : ℕ) : sidePt W p 1 = W.vtx ((p + 1) % W.n) := by
  unfold sidePt; simp [Geometry.lerp]

/-- A key equal to a natural `e` at a position `(p, τ)`: the position is `(e, 0)` or `(e - 1, 1)`. -/
theorem key_eq_nat {p e : ℕ} {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (h : (p : ℝ) + τ = e) :
    (p = e ∧ τ = 0) ∨ (p + 1 = e ∧ τ = 1) := by
  rcases h1.lt_or_eq with h1 | h1
  · left
    have a1 : (p : ℝ) ≤ e := ⟡
    have a2 : (e : ℝ) < p + 1 := ⟡
    have b1 : p ≤ e := by exact_mod_cast a1
    have b2 : e < p + 1 := by exact_mod_cast a2
    have hp : p = e := ⋄
    subst hp
    exact ⟨rfl, ⟡⟩
  · right
    subst h1
    have : ((p + 1 : ℕ) : ℝ) = e := by push_cast; linarith
    exact ⟨by exact_mod_cast this, rfl⟩

/-- A key strictly between `e` and `e + 1` at a position `(p, τ)`: the position is on edge `e`. -/
theorem key_between {p e : ℕ} {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (ha : (e : ℝ) < p + τ)
    (hb : (p : ℝ) + τ < e + 1) : p = e := by
  have a1 : (p : ℝ) < e + 1 := ⟡
  have a2 : (e : ℝ) < p + 1 := ⟡
  have b1 : p < e + 1 := by exact_mod_cast a1
  have b2 : e < p + 1 := by exact_mod_cast a2
  omega

/-- **Positions with keys in the closed key interval of a walk edge** are points of the edge. -/
theorem edge_keys (W : Polygon) {e : ℕ} (he : e < W.n) {p : ℕ} (hp : p < W.n) {τ : ℝ}
    (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (hk : CIn (e : ℝ) (((e + 1) % W.n : ℕ) : ℝ) ((p : ℝ) + τ)) :
    ∃ t₂ : ℝ, 0 ≤ t₂ ∧ t₂ ≤ 1 ∧ sidePt W e t₂ = sidePt W p τ := by
  -- the start vertex of the edge
  have at_e : (p : ℝ) + τ = e → ∃ t₂ : ℝ, 0 ≤ t₂ ∧ t₂ ≤ 1 ∧ sidePt W e t₂ = sidePt W p τ := by
    intro h
    rcases key_eq_nat h0 h1 h with ⟨rfl, rfl⟩ | ⟨hpe, rfl⟩
    · exact ⟨0, le_rfl, zero_le_one, rfl⟩
    · refine ⟨0, le_rfl, zero_le_one, ?_⟩
      rw [sidePt_zero, sidePt_one', ← hpe, Nat.mod_eq_of_lt (⋄)]
  -- the end vertex of the edge
  have at_f : (p : ℝ) + τ = (((e + 1) % W.n : ℕ) : ℝ) →
      ∃ t₂ : ℝ, 0 ≤ t₂ ∧ t₂ ≤ 1 ∧ sidePt W e t₂ = sidePt W p τ := by
    intro h
    refine ⟨1, zero_le_one, le_rfl, ?_⟩
    Ξ sidePt_one'
    rcases key_eq_nat h0 h1 h with ⟨hpe, rfl⟩ | ⟨hpe, rfl⟩
    · Ξ sidePt_zero, hpe
    · -- `p + 1 = (e + 1) % n`: then `p = e` (the edge itself, at its end)
      Ξ sidePt_one', hpe, Nat.mod_mod_of_dvd _ (dvd_refl _)
  rcases hk with hin | h | h
  · unfold sideInArc at hin
    rcases Nat.lt_or_ge (e + 1) W.n with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hin
      push_cast at hin
      rw [ite_eq_left (⟡)] at hin
      have := key_between h0 h1 hin.1 hin.2
      subst this
      exact ⟨τ, h0, h1, rfl⟩
    · have hn : e + 1 = W.n := ⋄
      rw [hn, Nat.mod_self] at hin
      push_cast at hin
      rw [ite_eq_right (by have : (0 : ℝ) ≤ e := Nat.cast_nonneg _; linarith)] at hin
      rcases hin with hin | hin
      · have hpe : p = e := by
          have a1 : (e : ℝ) < p + 1 := ⟡
          have b1 : e < p + 1 := by exact_mod_cast a1
          omega
        subst hpe
        exact ⟨τ, h0, h1, rfl⟩
      · have : (0 : ℝ) ≤ p := Nat.cast_nonneg _
        linarith
  · exact at_e h
  · exact at_f h

theorem prevV_succ {n q : ℕ} (hn : 2 ≤ n) (hq : q < n) : (prevV n q + 1) % n = q := by
  unfold prevV
  rcases Nat.eq_zero_or_pos q with rfl | h0
  · have : (0 + n - 1) % n = n - 1 := by
      rw [show 0 + n - 1 = n - 1 by omega]; exact Nat.mod_eq_of_lt (by omega)
    rw [this, show n - 1 + 1 = n by omega, Nat.mod_self]
  · have : (q + n - 1) % n = q - 1 := by
      rw [show q + n - 1 = (q - 1) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [this, show q - 1 + 1 = q by omega, Nat.mod_eq_of_lt hq]

/-- **The key interval of a vertex hole** is the union of those of its two walk edges. -/
theorem vtx_keys_split {n q : ℕ} (hn : 3 ≤ n) (hq : q < n) {k : ℝ} (hk0 : 0 ≤ k)
    (_hkn : k ≤ n) (h : CIn ((prevV n q : ℕ) : ℝ) (((q + 1) % n : ℕ) : ℝ) k) :
    CIn ((prevV n q : ℕ) : ℝ) (((prevV n q + 1) % n : ℕ) : ℝ) k ∨
      CIn (q : ℝ) (((q + 1) % n : ℕ) : ℝ) k := by
  have hpq : (prevV n q + 1) % n = q := prevV_succ (by omega) hq
  rw [hpq]
  unfold CIn sideInArc at h ⊢
  unfold prevV at h ⊢
  rcases Nat.eq_zero_or_pos q with rfl | h0
  · -- q = 0: the interval [n - 1, 1] wraps
    rw [show 0 + n - 1 = n - 1 by omega, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega : 0 + 1 < n)] at h ⊢
    have e1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [e1] at h ⊢
    push_cast at h ⊢
    have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
    rw [ite_eq_right (by linarith)] at h
    rw [ite_eq_right (by linarith), ite_eq_left (by linarith)]
    rcases h with (h | h) | h | h
    · left; left; left; exact h
    · rcases lt_or_ge k 0 with h' | h'
      · left; left; right; exact h'
      · rcases h'.lt_or_eq with h' | h'
        · right; left; exact ⟨h', h⟩
        · right; right; left; exact h'.symm
    · left; right; left; exact h
    · right; right; right; exact h
  · rw [show q + n - 1 = (q - 1) + n by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega : q - 1 < n)] at h ⊢
    have e1 : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    rw [e1] at h ⊢
    rcases Nat.lt_or_ge (q + 1) n with hlt | hge
    · -- no wrap
      rw [Nat.mod_eq_of_lt hlt] at h ⊢
      push_cast at h ⊢
      rw [ite_eq_left (by linarith)] at h
      rw [ite_eq_left (by linarith), ite_eq_left (by linarith)]
      rcases h with ⟨ha, hb⟩ | h | h
      · rcases lt_trichotomy k q with h' | h' | h'
        · left; left; exact ⟨ha, h'⟩
        · left; right; right; exact h'
        · right; left; exact ⟨h', hb⟩
      · left; right; left; exact h
      · right; right; right; exact h
    · -- q = n - 1: the interval [n - 2, 0] wraps
      have hq1 : q + 1 = n := by omega
      rw [hq1, Nat.mod_self] at h ⊢
      push_cast at h ⊢
      have hq' : (q : ℝ) + 1 = n := by exact_mod_cast hq1
      rw [ite_eq_right (by linarith)] at h
      rw [ite_eq_left (by linarith), ite_eq_right (by linarith)]
      rcases h with (h | h) | h | h
      · rcases lt_trichotomy k q with h' | h' | h'
        · left; left; exact ⟨h, h'⟩
        · left; right; right; exact h'
        · right; left; left; exact h'
      · linarith
      · left; right; left; exact h
      · right; right; right; exact h

/-- **An edge hole is near the points of its edge.** -/
theorem near_eHole (M : Model) (Q : Polygon) {e : ℕ} (he : e < M.W.n) {z : Point}
    (hz : ∃ t₁ : ℝ, 0 ≤ t₁ ∧ t₁ ≤ 1 ∧ sidePt M.W e t₁ = z) {p : ℕ} {τ : ℝ} (hp : p < M.W.n)
    (h0 : 0 ≤ τ) (h1 : τ ≤ 1)
    (hk : CIn (M.key Q (eHole M.W.n e).1) (M.key Q (eHole M.W.n e).2) ((p : ℝ) + τ)) :
    ∃ p', p' < M.W.n ∧ (∃ t₁ : ℝ, 0 ≤ t₁ ∧ t₁ ≤ 1 ∧ sidePt M.W p' t₁ = z) ∧
      ∃ t₂ : ℝ, 0 ≤ t₂ ∧ t₂ ≤ 1 ∧ sidePt M.W p' t₂ = sidePt M.W p τ := by
  simp only [eHole, key_hole] at hk
  exact ⟨e, he, hz, edge_keys M.W he hp h0 h1 hk⟩

/-- **A vertex hole is near its vertex.** -/
theorem near_vHole (M : Model) (Q : Polygon) (hn : 3 ≤ M.W.n) {q : ℕ} (hq : q < M.W.n)
    {z : Point} (hz : M.W.vtx q = z) {p : ℕ} {τ : ℝ} (hp : p < M.W.n) (h0 : 0 ≤ τ) (h1 : τ ≤ 1)
    (hk : CIn (M.key Q (vHole M.W.n q).1) (M.key Q (vHole M.W.n q).2) ((p : ℝ) + τ)) :
    ∃ p', p' < M.W.n ∧ (∃ t₁ : ℝ, 0 ≤ t₁ ∧ t₁ ≤ 1 ∧ sidePt M.W p' t₁ = z) ∧
      ∃ t₂ : ℝ, 0 ≤ t₂ ∧ t₂ ≤ 1 ∧ sidePt M.W p' t₂ = sidePt M.W p τ := by
  simp only [vHole, key_hole] at hk
  have hk0 : (0 : ℝ) ≤ p + τ := by have : (0 : ℝ) ≤ p := Nat.cast_nonneg _; linarith
  have hkn : (p : ℝ) + τ ≤ M.W.n := by
    have : ((p + 1 : ℕ) : ℝ) ≤ M.W.n := by exact_mod_cast hp
    push_cast at this; linarith
  have hpv : prevV M.W.n q < M.W.n := by unfold prevV; exact Nat.mod_lt _ (⋄)
  have hpq : (prevV M.W.n q + 1) % M.W.n = q := prevV_succ (⋄) hq
  rcases vtx_keys_split hn hq hk0 hkn hk with h | h
  · refine ⟨prevV M.W.n q, hpv, ⟨1, zero_le_one, le_rfl, ?_⟩, edge_keys M.W hpv hp h0 h1 h⟩
    Ξ sidePt_one', hpq, hz
  · exact ⟨q, hq, ⟨0, le_rfl, zero_le_one, Ρ sidePt_zero, hz⟩, edge_keys M.W hq hp h0 h1 h⟩

end

end Restore

end Chazelle.Core
