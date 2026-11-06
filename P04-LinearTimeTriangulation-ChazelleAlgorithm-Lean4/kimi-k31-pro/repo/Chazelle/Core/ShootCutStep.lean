module

public import Chazelle.Core.ShootCutValid
public import Chazelle.Core.ShootCutWt
public import Chazelle.Core.ShootCutDyadic
public import Chazelle.SimpTactics
public import Chazelle.MiscTactics

/-!
# WP-G, part 13: the pieces of one step of the core

* `single_ok`: a single walk edge `[c, c + 1]` of the double boundary is a valid kind-0 piece;
* `stretch_up`, `stretch_down`: along a run stretch the walk visits consecutive vertices of `Q`;
* `blockUp_ok`, `blockDn_ok`: an aligned block of the dyadic cover of a stretch is a valid piece
  (kind `1` with its grade-table entry when `g ≥ 1`, kind `0` when `g = 0`).
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (sideE sideInArc)

namespace ShootCut

variable {P : Polygon} {C : Chain} {m : ℕ → ℕ} {h γ : ℕ}

theorem proper_vtx' (P : Polygon) (C : Chain) (p : ℕ) :
    ProperPos (chainModel C) (Qof P) P.n ⟨p, 0⟩ := proper_vtx _ _ _ _

/-- **A single edge** between two walk vertices is a valid kind-0 piece. -/
theorem single_ok (e x0 dir pw : ℕ) {c : ℕ} (hc : c + 1 < 2 * C.m + 7) :
    PcOK P C m h γ ⟨⟨c, 0⟩, ⟨c + 1, 0⟩, 0, e, x0, dir, pw⟩ := by
  refine ⟨proper_vtx' P C _, proper_vtx' P C _, by sio, by sio, Or.inl rfl,
    fun _ => ?_, fun h1 => by simp at h1⟩
  simp only [key_hgt0]
  exact wt_within (chainModel C) (e := c) (by pcl) le_rfl (by pcl)

/-- **The grade of a block of weight at most `γ ≤ cap`** is processed and its granularity is
at most `cutGran γ`. -/
theorem block_grade {g Λ : ℕ} (hg : 1 ≤ g) (hγ : 2 ^ g ≤ γ) (hcap : γ ≤ 2 ^ (Λ - 1)) :
    g < Λ ∧ gradeGran g ≤ cutGran γ := by
  have h1 : g ≤ Λ - 1 := by
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 (hγ.trans hcap)
    exact this
  have h2 : 2 ≤ 2 ^ g := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ g := Nat.pow_le_pow_right (by norm_num) hg
  refine ⟨by
    rcases Nat.eq_zero_or_pos Λ with h0 | h0
    · subst h0; sio at hcap
    · omega, ?_⟩
  unfold cutGran
  apply gradeGran_mono
  have : 2 ^ g ≤ 2 ^ Nat.clog 2 γ := hγ.trans (Nat.le_pow_clog (by norm_num) γ)
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 this

/-- **A block of an upward stretch** `[q, q + L]` (walk vertices `c + d ↦ Q.vtx (q + d)`). -/
theorem blockUp_ok {c q L g b e : ℕ} (hwalk : ∀ d, d ≤ L →
      (chainModel C).W.vtx (c + d) = (Qof P).vtx (q + d))
    (h6 : 6 ≤ c) (hcL : c + L ≤ 2 * C.m + 6) (hqL : q + L < P.n) (hLγ : L ≤ γ)
    (hcap : γ ≤ 2 ^ (m h - 1)) (hlo : q ≤ b * 2 ^ g) (hhi : (b + 1) * 2 ^ g ≤ q + L)
    (he : 1 ≤ g → e = entryAddr m h g b) :
    PcOK P C m h γ ⟨⟨c + (b * 2 ^ g - q), 0⟩, ⟨c + (b * 2 ^ g - q) + 2 ^ g, 0⟩,
      if 0 < g then 1 else 0, e, b * 2 ^ g, 1, 2 ^ g⟩ := by
  have hp := Nat.two_pow_pos g
  have e1 : (b + 1) * 2 ^ g = b * 2 ^ g + 2 ^ g := by ring
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · simp only [pow_zero, lt_irrefl, ite_false]
    exact single_ok e (b * 1) 1 1 (by sio at e1 hhi)
  · simp only [hg, ite_true]
    have hγ : 2 ^ g ≤ γ := by omega
    obtain ⟨hΛ, hgran⟩ := block_grade hg hγ hcap
    refine ⟨proper_vtx' P C _, proper_vtx' P C _, by sio, by sio, Or.inr rfl,
      fun h1 => by simp at h1, fun _ => ⟨g, b, hg, hΛ, ?_, he hg, rfl, rfl, by omega, hgran,
        rfl, rfl, by sio, rfl, by sio, Or.inl rfl, fun d hd => ?_⟩⟩
    · unfold gradeCount
      have : b * 2 ^ g + 2 ^ g ≤ P.n - 1 := by omega
      have : b * 2 ^ g ≤ P.n - 2 := by omega
      have := (Nat.le_div_iff_mul_le hp).2 this
      omega
    · simp only [↓reduceIte]
      rw [Nat.add_assoc, hwalk _ (by omega)]
      congr 1; omega

/-- **A block of a downward stretch** from the top `q` (walk vertices `c + d ↦ Q.vtx (q - d)`). -/
theorem blockDn_ok {c q L g b e : ℕ} (hwalk : ∀ d, d ≤ L →
      (chainModel C).W.vtx (c + d) = (Qof P).vtx (q - d))
    (h6 : 6 ≤ c) (hcL : c + L ≤ 2 * C.m + 6) (hq : q < P.n) (hLq : L ≤ q) (hLγ : L ≤ γ)
    (hcap : γ ≤ 2 ^ (m h - 1)) (hlo : q - L ≤ b * 2 ^ g) (hhi : (b + 1) * 2 ^ g ≤ q)
    (he : 1 ≤ g → e = entryAddr m h g b) :
    PcOK P C m h γ ⟨⟨c + (q - (b + 1) * 2 ^ g), 0⟩, ⟨c + (q - (b + 1) * 2 ^ g) + 2 ^ g, 0⟩,
      if 0 < g then 1 else 0, e, b * 2 ^ g, 0, 2 ^ g⟩ := by
  have hp := Nat.two_pow_pos g
  have e1 : (b + 1) * 2 ^ g = b * 2 ^ g + 2 ^ g := by ring
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · simp only [pow_zero, lt_irrefl, ite_false]
    exact single_ok e (b * 1) 0 1 (by sio at e1 hhi)
  · simp only [hg, ite_true]
    have hγ : 2 ^ g ≤ γ := by omega
    obtain ⟨hΛ, hgran⟩ := block_grade hg hγ hcap
    refine ⟨proper_vtx' P C _, proper_vtx' P C _, by sio, by sio, Or.inr rfl,
      fun h1 => by simp at h1, fun _ => ⟨g, b, hg, hΛ, ?_, he hg, rfl, rfl, by omega, hgran,
        rfl, rfl, by sio, rfl, by sio, Or.inr rfl, fun d hd => ?_⟩⟩
    · unfold gradeCount
      have : b * 2 ^ g ≤ P.n - 2 := by omega
      have := (Nat.le_div_iff_mul_le hp).2 this
      omega
    · simp only [show (0 : ℕ) ≠ 1 by decide, ↓reduceIte]
      rw [Nat.add_assoc, hwalk _ (by omega)]
      congr 1; omega

end ShootCut

end

end Chazelle.Core
