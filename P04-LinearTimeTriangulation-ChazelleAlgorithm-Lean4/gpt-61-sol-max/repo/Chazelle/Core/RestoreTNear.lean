module

public meta import Chazelle.Arithmetic

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
  grind [sidePt, Geometry.lerp]

section
variable {p e : ℕ} {τ : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1)
include h0 h1
/-- A key equal to a natural `e` at a position `(p, τ)`: the position is `(e, 0)` or `(e - 1, 1)`. -/
theorem key_eq_nat (h : (p : ℝ) + τ = e) :
    (p = e ∧ τ = 0) ∨ (p + 1 = e ∧ τ = 1) := by
  rcases h1.lt_or_eq with h1 | h1
  · left
    have a1 : (p : ℝ) ≤ e := by linarith
    have a2 : (e : ℝ) < p + 1 := by linarith
    have b1 : p ≤ e := by simp_all
    have b2 : e < p + 1 := by exact_mod_cast a2
    ram_grind
  · right
    subst h1
    have : ((p + 1 : ℕ) : ℝ) = e := by simp_all
    exact ⟨by exact_mod_cast this, rfl⟩

/-- A key strictly between `e` and `e + 1` at a position `(p, τ)`: the position is on edge `e`. -/
theorem key_between (ha : (e : ℝ) < p + τ)
    (hb : (p : ℝ) + τ < e + 1) : p = e := by
  have a1 : (p : ℝ) < e + 1 := by linarith
  have a2 : (e : ℝ) < p + 1 := by linarith
  have b1 : p < e + 1 := by exact_mod_cast a1
  have b2 : e < p + 1 := by exact_mod_cast a2
  omega


end

/-- **Positions with keys in the closed key interval of a walk edge** are points of the edge. -/
theorem edge_keys (W : Polygon) {e : ℕ} (he : e < W.n) {p : ℕ} (hp : p < W.n) {τ : ℝ}
    (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (hk : CIn (e : ℝ) (((e + 1) % W.n : ℕ) : ℝ) ((p : ℝ) + τ)) :
    ∃ t₂ : ℝ, 0 ≤ t₂ ∧ t₂ ≤ 1 ∧ sidePt W e t₂ = sidePt W p τ := by
  -- the start vertex of the edge
  have at_e : (p : ℝ) + τ = e → ∃ t₂ : ℝ, 0 ≤ t₂ ∧ t₂ ≤ 1 ∧ sidePt W e t₂ = sidePt W p τ := by
    intro h
    rcases key_eq_nat h0 h1 h with ⟨rfl, rfl⟩ | ⟨hpe, rfl⟩
    · ram_grind
    · refine ⟨0, le_rfl, zero_le_one, ?_⟩
      rw [sidePt_zero, sidePt_one', ← hpe, Nat.mod_eq_of_lt (by omega)]
  -- the end vertex of the edge
  have at_f : (p : ℝ) + τ = (((e + 1) % W.n : ℕ) : ℝ) →
      ∃ t₂ : ℝ, 0 ≤ t₂ ∧ t₂ ≤ 1 ∧ sidePt W e t₂ = sidePt W p τ := by
    intro h
    refine ⟨1, zero_le_one, le_rfl, ?_⟩
    rw [sidePt_one']
    rcases key_eq_nat h0 h1 h with ⟨hpe, rfl⟩ | ⟨hpe, rfl⟩
    · grind [sidePt_zero]
    simp_all [sidePt_one'] 
  rcases hk with hin | h | h
  · unfold sideInArc at hin
    rcases Nat.lt_or_ge (e + 1) W.n with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hin
      push_cast at hin
      rw [ite_eq_left (by linarith)] at hin
      have := key_between h0 h1 hin.1 hin.2
      ram_grind
    · have hn : e + 1 = W.n := by omega
      rw [hn, Nat.mod_self] at hin
      push_cast at hin
      rw [ite_eq_right (by linarith)] at hin
      rcases hin with hin | hin
      · have hpe : p = e := by
          have a1 : (e : ℝ) < p + 1 := by linarith
          have b1 : e < p + 1 := by exact_mod_cast a1
          omega
        ram_grind
      linarith
  · exact at_e h
  simp_all

theorem prevV_succ {n q : ℕ} (hn : 2 ≤ n) (hq : q < n) : (prevV n q + 1) % n = q := by
  unfold prevV
  rcases Nat.eq_zero_or_pos q with rfl | h0
  · simp_all +arith
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
    ram_grind
  · ram_grind

section
variable (M : Model) (Q : Polygon)
/-- **An edge hole is near the points of its edge.** -/
theorem near_eHole {e : ℕ} (he : e < M.W.n) {z : Point}
    (hz : ∃ t₁ : ℝ, 0 ≤ t₁ ∧ t₁ ≤ 1 ∧ sidePt M.W e t₁ = z) {p : ℕ} {τ : ℝ} (hp : p < M.W.n)
    (h0 : 0 ≤ τ) (h1 : τ ≤ 1)
    (hk : CIn (M.key Q (eHole M.W.n e).1) (M.key Q (eHole M.W.n e).2) ((p : ℝ) + τ)) :
    ∃ p', p' < M.W.n ∧ (∃ t₁ : ℝ, 0 ≤ t₁ ∧ t₁ ≤ 1 ∧ sidePt M.W p' t₁ = z) ∧
      ∃ t₂ : ℝ, 0 ≤ t₂ ∧ t₂ ≤ 1 ∧ sidePt M.W p' t₂ = sidePt M.W p τ := by
  simp only [eHole, key_hole] at hk
  exact ⟨e, he, hz, edge_keys M.W he hp h0 h1 hk⟩

/-- **A vertex hole is near its vertex.** -/
theorem near_vHole (hn : 3 ≤ M.W.n) {q : ℕ} (hq : q < M.W.n)
    {z : Point} (hz : M.W.vtx q = z) {p : ℕ} {τ : ℝ} (hp : p < M.W.n) (h0 : 0 ≤ τ) (h1 : τ ≤ 1)
    (hk : CIn (M.key Q (vHole M.W.n q).1) (M.key Q (vHole M.W.n q).2) ((p : ℝ) + τ)) :
    ∃ p', p' < M.W.n ∧ (∃ t₁ : ℝ, 0 ≤ t₁ ∧ t₁ ≤ 1 ∧ sidePt M.W p' t₁ = z) ∧
      ∃ t₂ : ℝ, 0 ≤ t₂ ∧ t₂ ≤ 1 ∧ sidePt M.W p' t₂ = sidePt M.W p τ := by
  simp only [vHole, key_hole] at hk
  have hk0 : (0 : ℝ) ≤ p + τ := by linarith
  have hkn : (p : ℝ) + τ ≤ M.W.n := by
    have : ((p + 1 : ℕ) : ℝ) ≤ M.W.n := by exact_mod_cast hp
    grind
  have hpv : prevV M.W.n q < M.W.n := by unfold prevV; exact Nat.mod_lt _ (by omega)
  have hpq : (prevV M.W.n q + 1) % M.W.n = q := prevV_succ (by omega) hq
  rcases vtx_keys_split hn hq hk0 hkn hk with h | h
  · refine ⟨prevV M.W.n q, hpv, ⟨1, zero_le_one, le_rfl, ?_⟩, edge_keys M.W hpv hp h0 h1 h⟩
    grind [sidePt_one']
  · exact ⟨q, hq, ⟨0, le_rfl, zero_le_one, by grind [sidePt_zero]⟩, edge_keys M.W hq hp h0 h1 h⟩


end

end

end Restore

end Chazelle.Core
