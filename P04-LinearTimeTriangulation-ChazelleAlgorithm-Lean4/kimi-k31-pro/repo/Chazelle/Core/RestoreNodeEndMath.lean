module

public import Chazelle.Core.RestoreNodeArr

/-!
# WP-E, the search: the position of a node chord end in the host walk

For the end `(p, h)` of a node chord in the piece chain's walk (parameter `t`), at offset
`d = p - g'` of the stretch: it is strictly inside the stretch iff its rotated key
`off nα g' (p + t)` is in `(0, L)` (`inE_iff`); its host position `((g + d) mod n, h)` has the same
point and parameter (`endM_param`, `endM_pos`), hence host offset `d + t`.
-/

namespace Chazelle.Core

namespace Restore

@[expose] public section

open Chazelle.Chain (sidePt SideAttach sideInArc)
open WalkEmbed (off off_nonneg off_key off_key' dOf dOf_lt add_dOf)

variable {M : Model} {Cα : Chain} {g g' L : ℕ}

/-- **An end is strictly inside the stretch** iff its rotated key is in `(0, L)`. -/
theorem inE_iff (hS : Stretch M Cα g g' L) {p : ℕ} (hp : p < (chainModel Cα).W.n) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) :
    (g' ≤ p ∧ p < g' + L ∧ (g' < p ∨ 0 < t)) ↔
      (0 < off (chainModel Cα).W.n g' (p + t) ∧ off (chainModel Cα).W.n g' (p + t) < L) := by
  have hnα := Stretch.nα Cα
  have hg' : g' < (chainModel Cα).W.n := by rw [hnα]; have := hS.hgL; omega
  rw [off_key' hg' hp ht0 ht1]
  unfold dOf
  have hgL := hS.hgL
  by_cases hge : g' ≤ p
  · have e : (p + (chainModel Cα).W.n - g') % (chainModel Cα).W.n = p - g' := by
      rw [show p + (chainModel Cα).W.n - g' = (p - g') + (chainModel Cα).W.n by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [e]
    have hc : ((p - g' : ℕ) : ℝ) = (p : ℝ) - g' := by push_cast [Nat.cast_sub hge]; ring
    constructor
    · rintro ⟨-, h2, h3⟩
      refine ⟨?_, ?_⟩
      · rcases h3 with h3 | h3
        · have : (1 : ℝ) ≤ ((p - g' : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ p - g' by omega)
          linarith
        · have : (0 : ℝ) ≤ ((p - g' : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith
      · have : ((p - g' : ℕ) : ℝ) + 1 ≤ L := by exact_mod_cast (show p - g' + 1 ≤ L by omega)
        linarith
    · rintro ⟨h1, h2⟩
      refine ⟨hge, ?_, ?_⟩
      · by_contra hc'
        have : (L : ℝ) ≤ ((p - g' : ℕ) : ℝ) := by exact_mod_cast (show L ≤ p - g' by omega)
        linarith
      · by_cases hpg : g' < p
        · exact Or.inl hpg
        · right
          have : p - g' = 0 := by omega
          rw [this] at h1; simpa using h1
  · push Not at hge
    have e : (p + (chainModel Cα).W.n - g') % (chainModel Cα).W.n =
        p + (chainModel Cα).W.n - g' := Nat.mod_eq_of_lt (by omega)
    rw [e]
    constructor
    · rintro ⟨h1, -⟩; omega
    · rintro ⟨-, h2⟩
      exfalso
      have : (L : ℝ) ≤ ((p + (chainModel Cα).W.n - g' : ℕ) : ℝ) := by
        exact_mod_cast (show L ≤ p + (chainModel Cα).W.n - g' by rw [hnα]; omega)
      linarith

/-- The parameter of a vertex position is `0`. -/
theorem key_vtx (M : Model) (Q : Polygon) (p : ℕ) : M.key Q ⟨p, 0⟩ = p := by
  show (p : ℝ) + M.param Q ⟨p, 0⟩ = p
  rw [show M.param Q ⟨p, 0⟩ = 0 from rfl, add_zero]

/-- The comparison of `(p, 0)` and `(p, h)` tells whether the parameter is positive. -/
theorem key_pz (M : Model) (Q : Polygon) (p h : ℕ) :
    M.key Q ⟨p, 0⟩ < M.key Q ⟨p, h⟩ ↔ 0 < M.param Q ⟨p, h⟩ := by
  rw [key_vtx]
  show (p : ℝ) < p + M.param Q ⟨p, h⟩ ↔ _
  constructor <;> intro h <;> linarith

/-- **The host position of an end** has the parameter of the end. -/
theorem endM_param (hS : Stretch M Cα g g' L) {Q : Polygon} {d : ℕ} (hd : d < L) (h : ℕ) :
    M.param Q ⟨(g + d) % M.W.n, h⟩ = (chainModel Cα).param Q ⟨g' + d, h⟩ := by
  rw [param_agree hS.hA hd h, hS.mod' hd.le]

theorem endM_pos (hS : Stretch M Cα g g' L) {Q : Polygon} {d : ℕ} (hd : d < L) (h : ℕ) :
    M.pos Q ⟨(g + d) % M.W.n, h⟩ = (chainModel Cα).pos Q ⟨g' + d, h⟩ := by
  rw [pos_agree hS.hA hd h, hS.mod' hd.le]

/-- **The host offset of an end** is its rotated key. -/
theorem endM_off (hS : Stretch M Cα g g' L) {d : ℕ} (hd : d < L) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) : off M.W.n g (((g + d) % M.W.n : ℕ) + t) = d + t :=
  off_key hS.hg (by have := hS.hLn; omega) ht0 ht1

theorem endα_off (hS : Stretch M Cα g g' L) {d : ℕ} (hd : d < L) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t < 1) : off (chainModel Cα).W.n g' (((g' + d : ℕ) : ℝ) + t) = d + t := by
  have h := off_key (n := (chainModel Cα).W.n) (g := g') (d := d)
    (by rw [Stretch.nα]; have := hS.hgL; omega) (by rw [Stretch.nα]; have := hS.hgL; omega) ht0 ht1
  rwa [hS.mod' hd.le] at h

end

end Restore

end Chazelle.Core
