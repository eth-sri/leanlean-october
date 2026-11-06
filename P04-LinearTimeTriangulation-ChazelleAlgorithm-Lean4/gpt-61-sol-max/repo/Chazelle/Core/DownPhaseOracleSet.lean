module

public meta import Chazelle.Arithmetic

public import Chazelle.Core.DownPhaseOracleChain
public import Chazelle.Core.ShootCutTile

/-!
# WP-M (E7-B, part 2): point sets and weights along agreeing stretches (O3)

The interior oracles translate a subarc of the interior walk of `Q` into one or two arcs of the
walk of the chain model of a chain of `Q` (`DownPhaseOracleChain`).  The two walks agree along
stretches (`WalkEmbed.Agree`); this file shows that point sets and weights of arcs inside such a
stretch correspond.

* `oset W g x y`: the points of the walk `W` at offsets in `[x, y]` from its vertex `g`;
  `oset_union`, `oset_shift`, and `oset_congr` (agreeing stretches have the same `oset`);
* `wset_eq_oset`, `arcSet_eq_oset`: the point set of a closed cyclic key interval is an `oset`;
* `len_key`: the unwrapped length of the key interval from `u + t₁` to `(u + e) mod n + t₂`;
* `param_agree`, `pos_agree`: positions at the same offset of agreeing stretches have the same
  parameter and point;
* `arcWt_off`: the weight of a key interval inside the counted edges, by offsets.
-/

namespace Chazelle.Core

namespace IOrc

@[expose] public section

open Set
open Chazelle.Chain (sideInArc)
open Chazelle.Geometry (lerp lerp_zero lerp_one)

/-! ## Point sets by offsets -/

/-- The points of the walk `W` at offsets in `[x, y]` from its vertex `g`. -/
def oset (W : Polygon) (g : ℕ) (x y : ℝ) : Set Point :=
  {z | ∃ d : ℕ, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x ≤ d + t ∧ (d : ℝ) + t ≤ y ∧
    z = lerp (W.vtx ((g + d) % W.n)) (W.vtx ((g + d + 1) % W.n)) t}

section
variable (W : Polygon) (g : ℕ)
theorem oset_union {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) :
    oset W g x y ∪ oset W g y z = oset W g x z := by
  ext p; constructor
  · rintro (⟨d, t, h0, h1, h2, h3, rfl⟩ | ⟨d, t, h0, h1, h2, h3, rfl⟩)
    · exact ⟨d, t, h0, h1, h2, by linarith, rfl⟩
    · exact ⟨d, t, h0, h1, by linarith, h3, rfl⟩
  · rintro ⟨d, t, h0, h1, h2, h3, rfl⟩
    by_cases h : (d : ℝ) + t ≤ y
    · exact Or.inl ⟨d, t, h0, h1, h2, h, rfl⟩
    · exact Or.inr ⟨d, t, h0, h1, by linarith, h3, rfl⟩

theorem oset_mono {x y x' y' : ℝ} (hx : x' ≤ x) (hy : y ≤ y') :
    oset W g x y ⊆ oset W g x' y' := by
  rintro _ ⟨d, t, h0, h1, h2, h3, rfl⟩
  exact ⟨d, t, h0, h1, by linarith, by linarith, rfl⟩


end

/-- **Agreeing stretches have the same point sets.** -/
theorem oset_congr {W W' : Polygon} {g g' L : ℕ} (hA : WalkEmbed.Agree W W' g g' L) {x y : ℝ}
    (hy : y ≤ L) : oset W g x y = oset W' g' x y := by
  have key : ∀ {V V' : Polygon} {h h' : ℕ}, WalkEmbed.Agree V V' h h' L →
      oset V h x y ⊆ oset V' h' x y := by
    intro V V' h h' hA' p hp
    obtain ⟨d, t, h0, h1, h2, h3, rfl⟩ := hp
    have hd : d ≤ L := by
      have : (d : ℝ) ≤ L := by linarith
      simp_all
    rcases h0.lt_or_eq with ht | rfl
    · have hd' : d + 1 ≤ L := by
        ram_grind
      refine ⟨d, t, h0, h1, h2, h3, ?_⟩
      rw [hA' d hd, show h + d + 1 = h + (d + 1) by ring, show h' + d + 1 = h' + (d + 1) by ring,
        hA' (d + 1) hd']
    · refine ⟨d, 0, le_rfl, zero_le_one, h2, h3, ?_⟩
      simp only [lerp_zero]
      exact hA' d hd
  exact Subset.antisymm (key hA) (key fun d hd => (hA d hd).symm)

/-- Shifting the base vertex by `k` steps. -/
theorem oset_shift (W : Polygon) (g k : ℕ) {x y : ℝ} (hx : 0 ≤ x) :
    oset W g (k + x) (k + y) = oset W (g + k) x y := by
  ext p; constructor
  · rintro ⟨d, t, h0, h1, h2, h3, rfl⟩
    by_cases hdk : k ≤ d
    · have e : ((d - k : ℕ) : ℝ) = d - k := Nat.cast_sub hdk
      refine ⟨d - k, t, h0, h1, by linarith, by linarith, ?_⟩
      simp_all
    · have hdk' : (d : ℝ) + 1 ≤ k := by exact_mod_cast (by omega : d + 1 ≤ k)
      have ht : t = 1 := by linarith
      have hx0 : x = 0 := by linarith
      have hdk1 : d + 1 = k := by
        have : (k : ℝ) ≤ d + 1 := by linarith
        have : k ≤ d + 1 := by exact_mod_cast this
        omega
      have hk' : (k : ℝ) = d + 1 := by ram_grind
      refine ⟨0, 0, le_rfl, zero_le_one, by simp [hx0], by simp_all, ?_⟩
      rw [ht, lerp_one, lerp_zero, Nat.add_assoc, hdk1, Nat.add_zero]
  · rintro ⟨d, t, h0, h1, h2, h3, rfl⟩
    refine ⟨k + d, t, h0, h1, by ram_grind, by ram_grind, ?_⟩
    simp_all +arith

/-! ## Point sets of key intervals -/

/-- **An unwrapped key interval from a walk vertex** is an `oset`. -/
theorem wset_eq_oset (M : Model) {g : ℕ} (hg : g < M.W.n) {x y : ℝ} (hx : 0 ≤ x) :
    ShootCut.wset M ((g : ℝ) + x) ((g : ℝ) + y) = oset M.W g x y := by
  have hn : 0 < M.W.n := by omega
  ext z; constructor
  · rintro ⟨p, t, hp, h0, h1, ⟨X, hX1, hX2, j, hj⟩, rfl⟩
    set K : ℤ := (p : ℤ) - j * M.W.n - g with hK
    have hKr : (K : ℝ) = X - g - t := by rw [hK]; push_cast; linarith
    have hK1 : (-1 : ℝ) ≤ K := by linarith
    have hK1' : -1 ≤ K := by exact_mod_cast hK1
    rcases (show K = -1 ∨ 0 ≤ K by omega) with hKe | hKe
    · have hr : (K : ℝ) = -1 := by exact_mod_cast hKe
      have ht : t = 1 := by linarith
      have hx0 : x = 0 := by linarith
      refine ⟨0, 0, le_rfl, zero_le_one, by simp [hx0], by ram_grind, ?_⟩
      
      have hgp : g = (p + 1) % M.W.n := by
        have h1 : ((g % M.W.n : ℕ) : ℤ) = (((p + 1) % M.W.n : ℕ) : ℤ) := by
          grind [Int.natCast_mod, Int.add_mul_emod_self_right]
        rw [← Nat.mod_eq_of_lt hg]
        omega
      rw [ht, lerp_one, lerp_zero, Nat.add_zero, Nat.mod_eq_of_lt hg, hgp]
      rfl
    · lift K to ℕ using hKe with d hd
      have hdz : ((g + d : ℕ) : ℤ) = (p : ℤ) + (-j) * M.W.n := by ram_grind
      have hKr' : (d : ℝ) = X - g - t := by omega
      have hgd : (g + d) % M.W.n = p := by
        have h1 : (((g + d) % M.W.n : ℕ) : ℤ) = ((p % M.W.n : ℕ) : ℤ) := by
          rw [Int.natCast_mod, Int.natCast_mod, hdz, Int.add_mul_emod_self_right]
        rw [← Nat.mod_eq_of_lt hp]
        omega
      refine ⟨d, t, h0, h1, by linarith, by linarith, ?_⟩
      rw [hgd, show g + d + 1 = (g + d) + 1 by ring, ← Nat.mod_add_mod, hgd]
      rfl
  · rintro ⟨d, t, h0, h1, h2, h3, rfl⟩
    refine ⟨(g + d) % M.W.n, t, Nat.mod_lt _ hn, h0, h1, ⟨g + d + t, by linarith, by linarith,
      -(((g + d) / M.W.n : ℕ) : ℤ), ?_⟩, ?_⟩
    · have e := Nat.mod_add_div (g + d) M.W.n
      have e' : (((g + d) % M.W.n : ℕ) : ℝ) + M.W.n * ((g + d) / M.W.n : ℕ) = g + d := by
        exact_mod_cast e
      simp only [Int.cast_neg, Int.cast_natCast]
      linarith
    · unfold Model.wa Model.wb
      simp_all

/-- **The point set of a closed cyclic key interval** starting inside the walk edge `u` (key
`u + t₁`, `0 ≤ t₁ < 1`) is the `oset` of offsets `[t₁, t₁ + len]`. -/
theorem arcSet_eq_oset (M : Model) {u : ℕ} (hu : u < M.W.n) {t₁ b : ℝ} (ht0 : 0 ≤ t₁)
    (ht1 : t₁ < 1) (hb : 0 ≤ b) (hbn : b < M.W.n) :
    M.arcSet ((u : ℝ) + t₁) b = oset M.W u t₁ (t₁ + ShootCut.len M.W.n ((u : ℝ) + t₁) b) := by
  have hun : (u : ℝ) + 1 ≤ M.W.n := by exact_mod_cast hu
  rw [ShootCut.arcSet_eq_wset M (by positivity) (by linarith) hb hbn, ← wset_eq_oset M hu ht0]
  grind [ShootCut.len]

/-- **The unwrapped length** of the key interval from `u + t₁` to `(u + e) mod n + t₂`, for an
end at offset `e + t₂` within one lap. -/
theorem len_key {n u e : ℕ} (hu : u < n) {t₁ t₂ : ℝ} (ht1 : t₁ < 1) (ht2 : 0 ≤ t₂)
    (hlt : t₁ < e + t₂) (hlap : (e : ℝ) + t₂ ≤ t₁ + n) :
    ShootCut.len n ((u : ℝ) + t₁) (((u + e) % n : ℕ) + t₂) = e + t₂ - t₁ := by
  unfold ShootCut.len
  by_cases h : u + e < n
  · rw [Nat.mod_eq_of_lt h]
    ram_grind
  · have hen : e ≤ n := by
      have : (e : ℝ) < n + 1 := by linarith
      have : e < n + 1 := by exact_mod_cast this
      omega
    have hm : (u + e) % n = u + e - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hm]
    have e1 : ((u + e - n : ℕ) : ℝ) = u + e - n := by
      simp_all
    ram_grind

/-! ## Positions at the same offset -/

section
variable (M : Model) (g d : ℕ)
theorem wa_mod : M.wa ((g + d) % M.W.n) = M.W.vtx ((g + d) % M.W.n) := rfl

theorem wb_mod :
    M.wb ((g + d) % M.W.n) = M.W.vtx ((g + (d + 1)) % M.W.n) := by
  unfold Model.wb
  simp_all +arith


end

section
variable {M M' : Model} {g g' L : ℕ} (hA : WalkEmbed.Agree M.W M'.W g g' L) (Q : Polygon) {d : ℕ} (hd : d < L) (h : ℕ)
include L hA hd
/-- Positions at the same offset of agreeing stretches have the same parameter. -/
theorem param_agree :
    M.param Q ⟨(g + d) % M.W.n, h⟩ = M'.param Q ⟨(g' + d) % M'.W.n, h⟩ := by
  unfold Model.param
  simp only
  rw [wb_mod, wb_mod, wa_mod, wa_mod, hA d hd.le, hA (d + 1) hd]

/-- Positions at the same offset of agreeing stretches have the same point. -/
theorem pos_agree :
    M.pos Q ⟨(g + d) % M.W.n, h⟩ = M'.pos Q ⟨(g' + d) % M'.W.n, h⟩ := by
  unfold Model.pos
  simp only
  rw [param_agree hA Q hd h, wb_mod, wb_mod, wa_mod, wa_mod, hA d hd.le, hA (d + 1) hd]


end

/-- The parameter of a vertex position (height code `0`) is `0`. -/
theorem param_zero (M : Model) (Q : Polygon) (e : ℕ) : M.param Q ⟨e, 0⟩ = 0 := rfl

/-! ## Weights by offsets -/

theorem keyCeil_le {e : ℕ} {f : ℝ} : e ≤ keyCeil e f := by
  core_grind

/-- **The weight of a key interval by offsets.**  If the counted walk edges are `[lo, hi)`,
`hi ≤ n`, the key interval from `u + t₁` (`lo ≤ u`) to `(u + e) mod n + t₂` (within one lap, and
not wrapping past `hi` when `lo > 0`) meets `⌈e + t₂⌉` counted edges. -/
theorem arcWt_off (M : Model) {lo hi : ℕ}
    (hc : ∀ p, p < M.W.n → (M.counted p ↔ lo ≤ p ∧ p < hi)) (hhi : hi ≤ M.W.n) {u e : ℕ}
    (hu : u < M.W.n) (hlo : lo ≤ u) {t₁ t₂ : ℝ} (ht0 : 0 ≤ t₁) (ht1 : t₁ < 1) (ht2 : 0 ≤ t₂)
    (ht21 : t₂ < 1) (hlt : t₁ < e + t₂)
    (hwrap : (lo = 0 ∧ hi = M.W.n ∧ keyCeil e t₂ ≤ M.W.n) ∨ (u + keyCeil e t₂ ≤ hi ∧ hi < M.W.n)) :
    M.arcWt ((u : ℝ) + t₁) (((u + e) % M.W.n : ℕ) + t₂) = keyCeil e t₂ := by
  
  rw [M.arcWt_closed hc hhi ⟨ht0, ht1⟩ ⟨ht2, ht21⟩]
  have hke : keyCeil ((u + e) % M.W.n) t₂ = (u + e) % M.W.n + (keyCeil e t₂ - e) := by
    unfold keyCeil; grind
  have hk1 : keyCeil e t₂ ≤ e + 1 := by grind [keyCeil]
  have hk0 : e ≤ keyCeil e t₂ := keyCeil_le
  have hkp : keyCeil e t₂ = e → t₂ = 0 := by
    simp_all [keyCeil] 
  unfold arcWtNat
  rcases hwrap with ⟨rfl, rfl, hkn⟩ | hwrap
  · by_cases h : u + e < M.W.n
    · rw [Nat.mod_eq_of_lt h] at hke ⊢
      grind
    · have hm : (u + e) % M.W.n = u + e - M.W.n := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [hm] at hke ⊢
      have e1 : ((u + e - M.W.n : ℕ) : ℝ) = u + e - M.W.n := by
        rw [Nat.cast_sub (by omega)]; grind
      have hnot : ¬ ((u : ℝ) + t₁ < ((u + e - M.W.n : ℕ) : ℝ) + t₂) := by
        rw [e1]
        intro hlt'
        -- then `n < e + t₂ - t₁ + …`: the key would lie beyond one lap
        have : (M.W.n : ℝ) + t₁ < e + t₂ := by linarith
        have hkr : (keyCeil e t₂ : ℝ) ≤ M.W.n := by exact_mod_cast hkn
        rcases Nat.lt_or_ge e (keyCeil e t₂) with h2 | h2
        · have : (e : ℝ) + 1 ≤ M.W.n := by
            have : e + 1 ≤ M.W.n := by omega
            exact_mod_cast this
          linarith
        grind
      rw [ite_eq_right hnot, hke]
      simp only [min_eq_left (show u ≤ M.W.n by omega)]
      omega
  · obtain ⟨hwrap, hhn⟩ := hwrap
    have hue : u + e < M.W.n := by omega
    rw [Nat.mod_eq_of_lt hue] at hke ⊢
    rw [ite_eq_left (by grind), hke]
    omega

end

end IOrc

end Chazelle.Core
