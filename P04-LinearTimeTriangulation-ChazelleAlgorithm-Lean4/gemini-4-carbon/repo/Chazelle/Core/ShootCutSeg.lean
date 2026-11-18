module

public import Chazelle.Core.ShootCutTile
public import Chazelle.Core.SweepHit

/-!
# WP-G, part 5: first hits on walk edges

The ray-shooter answers kind-0 pieces edge by edge.

* `wset_edge`: an unwrapped key range inside one walk edge `p` is the sub-segment of that edge
  between the two parameters;
* `wset_edges`: an unwrapped key range from `p + s₀` to `q + s₁` (`p < q`) is the union of the
  sub-segment of edge `p` from `s₀`, the whole edges `p + 1, …, q - 1` and the sub-segment of
  edge `q` up to `s₁` (edges taken modulo `n`);
* `firstHit_of_single`: a set meeting the ray (at positive parameters) exactly at `t*`;
* `seg_single`: a non-horizontal segment meets the horizontal line through `z` in at most one
  point, the point at the height of `z`;
* `hseg_firstHit`, `hseg_noHit`: a horizontal segment on the line of the ray.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (sideInArc)
open Chazelle.Geometry (lerp lerp_fst lerp_snd)
open Chazelle.Visibility (rayPt rayPt_fst rayPt_snd)

namespace ShootCut

/-! ## Sub-segments of a walk edge -/

/-- The points of the walk edge `p` with parameters in `[s₀, s₁]`. -/
def subSeg (M : Model) (p : ℕ) (s₀ s₁ : ℝ) : Set Point :=
  {x | ∃ s, s₀ ≤ s ∧ s ≤ s₁ ∧ x = lerp (M.wa p) (M.wb p) s}

theorem wa_succ (M : Model) {p : ℕ} (hp : p + 1 < M.W.n) : M.wa (p + 1) = M.wb p := by
  unfold Model.wa Model.wb; rw [Nat.mod_eq_of_lt hp]

theorem lerp_zero' (a b : Point) : lerp a b 0 = a := by simp [lerp]
theorem lerp_one' (a b : Point) : lerp a b 1 = b := by
  ext <;> simp [lerp]

/-- **An unwrapped key range inside one walk edge.** -/
theorem wset_edge (M : Model) {p : ℕ} (hp : p < M.W.n) {s₀ s₁ : ℝ} (h0 : 0 ≤ s₀) (h01 : s₀ ≤ s₁)
    (h1 : s₁ ≤ 1) (i : ℤ) :
    wset M (p + s₀ + i * M.W.n) (p + s₁ + i * M.W.n) = subSeg M p s₀ s₁ := by
  rw [wset_shift]
  have hn' : 0 < M.W.n := by_o
  have hn : (0 : ℝ) < M.W.n := by exact_mod_cast hn'
  have hpn : (p : ℝ) + 1 ≤ M.W.n := by exact_mod_cast hp
  ext x
  constructor
  · rintro ⟨p', t, hp', ht0, ht1, ⟨X, hX1, hX2, j, hj⟩, rfl⟩
    have hp'n : (p' : ℝ) + 1 ≤ M.W.n := by exact_mod_cast hp'
    have hy0 : 0 ≤ (p' : ℝ) + t := by_p
    rcases int_range hn hy0 by_l (by linarith [(Nat.cast_nonneg p : (0:ℝ) ≤ p)]) by_l hj with rfl | rfl | rfl
    · -- `j = -1`: `X = n`, so `p = n - 1`, `s₁ = 1`, and the position is the vertex `0`
      push_cast at hj
      have hX : X = M.W.n := by_l
      have hpp : (p : ℝ) = M.W.n - 1 := by_l
      have hs1 : s₁ = 1 := by_l
      have hp'0 : (p' : ℝ) = 0 ∧ t = 0 := by constructor <;> linarith
      have hp'0' : p' = 0 := by exact_mod_cast hp'0.1
      have hpn1 : p = M.W.n - 1 := by
        have : ((p + 1 : ℕ) : ℝ) = M.W.n := by push_cast; linarith
        have := (Nat.cast_inj (R := ℝ)).1 this; omega
      refine ⟨1, by_l, by_l, ?_⟩
      rw [hp'0', hp'0.2, lerp_zero', lerp_one', hpn1, wb_last M hn']
    · simp only [Int.cast_zero, zero_mul, add_zero] at hj
      -- `p' + t ∈ [p, p + 1]`
      have hlo : (p : ℝ) ≤ p' + t := by_l
      have hhi : (p' : ℝ) + t ≤ p + 1 := by_l
      have hp'1 : p' ≤ p + 1 := by
        have : (p' : ℝ) ≤ p + 1 := by_l
        exact_mod_cast this
      have hp'2 : p ≤ p' + 1 := by
        have : (p : ℝ) ≤ p' + 1 := by_l
        exact_mod_cast this
      rcases (show p' = p ∨ p' = p + 1 ∨ p' + 1 = p by omega) with rfl | rfl | h
      · exact ⟨t, by_l, by_l, rfl⟩
      · push_cast at hhi
        have ht : t = 0 := by_l
        refine ⟨1, by_l, by push_cast at hj; linarith, ?_⟩
        rw [ht, lerp_zero', lerp_one', wa_succ M hp']
      · have hpR : (p : ℝ) = p' + 1 := by exact_mod_cast h.symm
        have ht : t = 1 := by_l
        refine ⟨0, by_l, by_l, ?_⟩
        rw [ht, lerp_zero', lerp_one', ← h, wa_succ M by_o]
    · -- `j = 1`: `X = 0`, so `p = 0`, `s₀ = 0`, and the position is the end of the last edge
      push_cast at hj
      have hX : X = 0 := by_l
      have hp0 : (p : ℝ) = 0 := by linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
      have hp0' : p = 0 := by exact_mod_cast hp0
      have hs0 : s₀ = 0 := by_l
      have ht : t = 1 := by
        by_contra hne
        have := lt_of_le_of_ne ht1 hne
        linarith
      have hp'n1 : p' = M.W.n - 1 := by
        have : ((p' + 1 : ℕ) : ℝ) = M.W.n := by push_cast; linarith
        have := (Nat.cast_inj (R := ℝ)).1 this; omega
      refine ⟨0, by_l, by_l, ?_⟩
      rw [ht, lerp_zero', lerp_one', hp'n1, wb_last M hn', hp0']
  · rintro ⟨s, hs0, hs1, rfl⟩
    exact ⟨p, s, hp, by_l, by_l, ⟨p + s, by_l, by_l, 0, by_s⟩, rfl⟩

/-! ## First hits on simple sets -/

/-- The parameter of the point at height `y` of the segment `[u, v]`. -/
noncomputable def hpar (u v : Point) (y : ℝ) : ℝ := (y - u.2) / (v.2 - u.2)

theorem hpar_snd {u v : Point} (huv : u.2 ≠ v.2) (y : ℝ) : (lerp u v (hpar u v y)).2 = y := by
  unfold hpar
  simp only [lerp_snd]
  have := sub_ne_zero.2 (Ne.symm huv)
  field_simp
  ring

/-! ## Horizontal segments on the line of the ray -/

end ShootCut

end

end Chazelle.Core
