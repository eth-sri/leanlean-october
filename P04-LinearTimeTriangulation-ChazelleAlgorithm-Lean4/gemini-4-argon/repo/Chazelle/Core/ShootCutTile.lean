module

public import Chazelle.Core.ShootCutPiece

/-!
# WP-G, part 4: tiling a subarc by pieces

The ray-shooter decomposes its subarc into the pieces of the arc-cutter and combines their first
hits; this needs the point set of the subarc to be the union of the point sets of the pieces.
Keys live on the cycle `[0, n)` (`n` walk edges); an **unwrapped** key interval `[A, B]` (reals,
`B - A ≤ n`) describes the walk points with a key congruent to a point of `[A, B]` modulo `n`
(`wset`).

* `arcSet_eq_wset`: the point set of the closed cyclic key interval from `a` to `b` is
  `wset a b` (if `a < b`) or `wset a (b + n)` (if `b ≤ a`, including the whole walk for `a = b`);
* `wset_union`: consecutive unwrapped intervals add up;
* `wset_shift`: shifting by a multiple of `n` changes nothing;
* `arcSet_step`: a piece from key `k` (unwrapped to `K ≡ k`) to key `k'` covers `wset K K'` for
  the unwrapped end `K' = K + len k k'`;
* `unwrap_final`: an unwrapped end congruent to `b`, after `a` and not beyond `B`, is `B`.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (sideInArc)
open Chazelle.Geometry (lerp)

namespace ShootCut

variable (M : Model)

/-- The walk points with a key congruent modulo `n` to a point of `[A, B]`. -/
def wset (A B : ℝ) : Set Point :=
  {x | ∃ p : ℕ, ∃ t : ℝ, p < M.W.n ∧ 0 ≤ t ∧ t ≤ 1 ∧
    (∃ X : ℝ, A ≤ X ∧ X ≤ B ∧ ∃ j : ℤ, (p : ℝ) + t = X + j * M.W.n) ∧
      x = lerp (M.wa p) (M.wb p) t}

theorem wset_union {A B C : ℝ} (hAB : A ≤ B) (hBC : B ≤ C) :
    wset M A B ∪ wset M B C = wset M A C := by
  ext x
  constructor
  · rintro (⟨p, t, hp, h0, h1, ⟨X, hX1, hX2, j, hj⟩, rfl⟩ | ⟨p, t, hp, h0, h1, ⟨X, hX1, hX2, j, hj⟩, rfl⟩)
    · exact ⟨p, t, hp, h0, h1, ⟨X, hX1, by linarith, j, hj⟩, rfl⟩
    · exact ⟨p, t, hp, h0, h1, ⟨X, by linarith, hX2, j, hj⟩, rfl⟩
  · rintro ⟨p, t, hp, h0, h1, ⟨X, hX1, hX2, j, hj⟩, rfl⟩
    by_cases hXB : X ≤ B
    · exact Or.inl ⟨p, t, hp, h0, h1, ⟨X, hX1, hXB, j, hj⟩, rfl⟩
    · exact Or.inr ⟨p, t, hp, h0, h1, ⟨X, by linarith, hX2, j, hj⟩, rfl⟩

theorem wset_shift (A B : ℝ) (i : ℤ) :
    wset M (A + i * M.W.n) (B + i * M.W.n) = wset M A B := by
  ext x
  constructor
  · rintro ⟨p, t, hp, h0, h1, ⟨X, hX1, hX2, j, hj⟩, rfl⟩
    refine ⟨p, t, hp, h0, h1, ⟨X - i * M.W.n, by linarith, by linarith, j + i, ?_⟩, rfl⟩
    push_cast; linarith
  · rintro ⟨p, t, hp, h0, h1, ⟨X, hX1, hX2, j, hj⟩, rfl⟩
    refine ⟨p, t, hp, h0, h1, ⟨X + i * M.W.n, by linarith, by linarith, j - i, ?_⟩, rfl⟩
    push_cast; linarith

/-- The last walk edge ends where the first begins. -/
theorem wb_last (hn : 0 < M.W.n) : M.wb (M.W.n - 1) = M.wa 0 := by
  unfold Model.wb Model.wa
  rw [Nat.sub_add_cancel hn, Nat.mod_self]

/-- The integer `j` of a key `y ∈ [0, n]` congruent to `X ∈ [0, 2n)`. -/
theorem int_range {n y X : ℝ} {j : ℤ} (hn : 0 < n) (hy0 : 0 ≤ y) (hy1 : y ≤ n)
    (hX0 : 0 ≤ X) (hX1 : X < 2 * n) (hj : y = X + j * n) :
    j = -1 ∨ j = 0 ∨ j = 1 := by
  have h1' : (j : ℝ) > -2 := by
    by_contra h; push Not at h; nlinarith
  have h2' : (j : ℝ) ≤ 1 := by
    by_contra h; push Not at h; nlinarith
  have h3 : j > -2 := by exact_mod_cast h1'
  have h4 : j ≤ 1 := by exact_mod_cast h2'
  omega

/-- **The point set of a closed cyclic key interval** as an unwrapped interval. -/
theorem arcSet_eq_wset {a b : ℝ} (ha : 0 ≤ a) (han : a < M.W.n) (hb : 0 ≤ b) (hbn : b < M.W.n) :
    M.arcSet a b = wset M a (if a < b then b else b + M.W.n) := by
  have hn : (0 : ℝ) < M.W.n := by linarith
  have hn' : 0 < M.W.n := by exact_mod_cast hn
  ext x
  constructor
  · rintro ⟨p, t, hp, h0, h1, hc, rfl⟩
    have hpn : (p : ℝ) + 1 ≤ M.W.n := by exact_mod_cast hp
    refine ⟨p, t, hp, h0, h1, ?_, rfl⟩
    split_ifs with hab
    · refine ⟨p + t, ?_, ?_, 0, by simp⟩
      · rcases hc with hc | hc | hc
        · unfold sideInArc at hc; rw [ite_eq_left hab] at hc; exact hc.1.le
        · exact hc.ge
        · linarith
      · rcases hc with hc | hc | hc
        · unfold sideInArc at hc; rw [ite_eq_left hab] at hc; exact hc.2.le
        · linarith
        · exact hc.le
    · have hy : a ≤ (p : ℝ) + t ∨ (p : ℝ) + t ≤ b := by
        rcases hc with hc | hc | hc
        · unfold sideInArc at hc; rw [ite_eq_right hab] at hc
          rcases hc with hc | hc
          · exact Or.inl hc.le
          · exact Or.inr hc.le
        · exact Or.inl hc.ge
        · exact Or.inr hc.le
      rcases hy with hy | hy
      · exact ⟨p + t, hy, by linarith, 0, by simp⟩
      · exact ⟨p + t + M.W.n, by linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)], by linarith, -1,
          by push_cast; ring⟩
  · rintro ⟨p, t, hp, h0, h1, ⟨X, hX1, hX2, j, hj⟩, rfl⟩
    have hpn : (p : ℝ) + 1 ≤ M.W.n := by exact_mod_cast hp
    have hy0 : 0 ≤ (p : ℝ) + t := by positivity
    have hy1 : (p : ℝ) + t ≤ M.W.n := by linarith
    -- the alias of the key `n`: the walk vertex `0`
    have halias : (p : ℝ) + t = M.W.n → lerp (M.wa p) (M.wb p) t = lerp (M.wa 0) (M.wb 0) 0 := by
      intro he
      have ht1 : t = 1 := by
        by_contra hne
        have := lt_of_le_of_ne h1 hne
        linarith
      have hp1 : p = M.W.n - 1 := by
        have : (p : ℝ) = M.W.n - 1 := by linarith
        have : ((p + 1 : ℕ) : ℝ) = M.W.n := by push_cast; linarith
        have := (Nat.cast_inj (R := ℝ)).1 this
        omega
      rw [ht1, hp1, wb_last M hn']
      simp [lerp]
    have hX3 : X < 2 * M.W.n := by split_ifs at hX2 <;> linarith
    rcases int_range hn hy0 hy1 (by linarith) hX3 hj with rfl | rfl | rfl
    · -- `j = -1`: `y = X - n`
      push_cast at hj
      split_ifs at hX2 with hab
      · exfalso; linarith
      · refine ⟨p, t, hp, h0, h1, ?_, rfl⟩
        rcases (show (p : ℝ) + t < b ∨ (p : ℝ) + t = b by
          rcases lt_or_eq_of_le (show (p : ℝ) + t ≤ b by linarith) with h | h
          · exact Or.inl h
          · exact Or.inr h) with h | h
        · left; unfold sideInArc; rw [ite_eq_right hab]; exact Or.inr h
        · right; right; exact h
    · -- `j = 0`: `y = X`
      simp only [Int.cast_zero, zero_mul, add_zero] at hj
      refine ⟨p, t, hp, h0, h1, ?_, rfl⟩
      split_ifs at hX2 with hab
      · rcases lt_or_eq_of_le (show a ≤ (p : ℝ) + t by linarith) with h | h
        · rcases lt_or_eq_of_le (show (p : ℝ) + t ≤ b by linarith) with h' | h'
          · left; unfold sideInArc; rw [ite_eq_left hab]; exact ⟨h, h'⟩
          · right; right; exact h'
        · right; left; exact h.symm
      · rcases lt_or_eq_of_le (show a ≤ (p : ℝ) + t by linarith) with h | h
        · left; unfold sideInArc; rw [ite_eq_right hab]; exact Or.inl h
        · right; left; exact h.symm
    · -- `j = 1`: `y = X + n`, so `X = 0 = a` and `y = n`: the alias
      push_cast at hj
      have ha0 : a = 0 := by linarith
      rw [halias (by linarith)]
      refine ⟨0, 0, hn', le_rfl, zero_le_one, Or.inr (Or.inl (by simp [ha0])), rfl⟩

/-- The unwrapped length of the piece from key `k` to key `k'`. -/
noncomputable def len (n k k' : ℝ) : ℝ := if k < k' then k' - k else k' - k + n

/-- **One piece** (keys `k`, `k'` on the cycle, `k` unwrapped to `K = k + i n`). -/
theorem arcSet_step {k k' : ℝ} (hk : 0 ≤ k) (hkn : k < M.W.n) (hk' : 0 ≤ k') (hk'n : k' < M.W.n)
    (i : ℤ) :
    M.arcSet k k' = wset M (k + i * M.W.n) (k + i * M.W.n + len M.W.n k k') := by
  rw [arcSet_eq_wset M hk hkn hk' hk'n, show k + i * M.W.n + len M.W.n k k' =
    (if k < k' then k' else k' + M.W.n) + i * M.W.n by unfold len; split_ifs <;> ring,
    wset_shift]

theorem len_pos (n k k' : ℝ) (hk : k < n) (hk' : 0 ≤ k') : 0 < len n k k' := by
  unfold len; split_ifs <;> linarith

theorem len_le (n k k' : ℝ) (hk : 0 ≤ k) (hk' : k' < n) : len n k k' ≤ n := by
  unfold len; split_ifs <;> linarith

/-! ## Lists of pieces -/

end ShootCut

end

end Chazelle.Core
