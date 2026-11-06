module

public import Chazelle.Core.OracleRay

/-!
# Lemma 3.6 (WP-H), part 4: the two sides of the chain (fold coordinates)

The walk of the chain model traverses the double boundary of the chain once around: tour position
`i` (walk edge `i + 6`, `i < 2 m`) runs along the chain edge between the vertices
`sideE m j`, `sideE m (j + 1)` with `j = (S + i) mod 2 m` (`S = sideS`).  In the **tour
coordinate** `u = j + t ∈ [0, 2 m)` the double boundary is a circle, and the point of the chain
depends only on the fold `u ↦ min(u, 2 m - u)`.

* `cp_inj`: the chain is injective in its coordinate `(k, τ)` (simplicity).
* `tour_pt`: the point of a tour position in chain coordinates.
* `same_point`: **two tour positions have the same point iff their tour coordinates are equal
  or opposite** (`u + u' = 2 m`): this is the mirror used for the zipper edges of the graph of
  Lemma 3.6 (faces of `S*` sharing an edge of the chain, p. 514).
* `pos_on_chain`: every walk position whose point is on the chain is a tour position.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (sidePt sideE)
open Chazelle.Geometry (lerp lerp_zero)

namespace OracleQ

variable (C : Chain)

/-- The chain point with coordinate `(k, τ)`. -/
noncomputable def cp (k : ℕ) (τ : ℝ) : Point := lerp (C.vertex k) (C.vertex (k + 1)) τ

/-- A valid chain coordinate: `k < m`, `τ ∈ [0, 1)`, or the last vertex `(m, 0)`. -/
def CCoord (k : ℕ) (τ : ℝ) : Prop := (k < C.m ∧ 0 ≤ τ ∧ τ < 1) ∨ (k = C.m ∧ τ = 0)

theorem cp_zero (k : ℕ) : cp C k 0 = C.vertex k := lerp_zero _ _

/-- **The chain is injective in its coordinate.** -/
theorem cp_inj (hP : C.P.Simple) {k k' : ℕ} {τ τ' : ℝ} (h : CCoord C k τ) (h' : CCoord C k' τ')
    (heq : cp C k τ = cp C k' τ') : k = k' ∧ τ = τ' := by
  have hk : k ≤ C.m := by rcases h with h | h <;> omega
  have hk' : k' ≤ C.m := by rcases h' with h | h <;> omega
  rcases eq_or_lt_of_le (show 0 ≤ τ by rcases h with h | h <;> [exact h.2.1; exact le_of_eq h.2.symm])
    with hτ | hτ <;>
  rcases eq_or_lt_of_le (show 0 ≤ τ' by rcases h' with h | h <;> [exact h.2.1; exact le_of_eq h.2.symm])
    with hτ' | hτ'
  · subst hτ; subst hτ'
    rw [cp_zero, cp_zero] at heq
    exact ⟨C.sideVertex_inj hP hk hk' heq, rfl⟩
  · exfalso
    subst hτ
    have hk'm : k' < C.m := by rcases h' with h | h <;> [exact h.1; linarith [h.2]]
    have hτ1 : τ' < 1 := by rcases h' with h | h <;> [exact h.2.2; linarith [h.2]]
    rw [cp_zero] at heq
    exact C.sideOpen_ne_vertex hP ⟨hτ', hτ1⟩ heq.symm
  · exfalso
    subst hτ'
    have hkm : k < C.m := by rcases h with h | h <;> [exact h.1; linarith [h.2]]
    have hτ1 : τ < 1 := by rcases h with h | h <;> [exact h.2.2; linarith [h.2]]
    rw [cp_zero] at heq
    exact C.sideOpen_ne_vertex hP ⟨hτ, hτ1⟩ heq
  · have hkm : k < C.m := by rcases h with h | h <;> [exact h.1; linarith [h.2]]
    have hτ1 : τ < 1 := by rcases h with h | h <;> [exact h.2.2; linarith [h.2]]
    have hk'm : k' < C.m := by rcases h' with h | h <;> [exact h.1; linarith [h.2]]
    have hτ1' : τ' < 1 := by rcases h' with h | h <;> [exact h.2.2; linarith [h.2]]
    by_cases hkk : k = k'
    · subst hkk
      refine ⟨rfl, ?_⟩
      have hne := C.sideVertex_succ_ne hP k
      unfold cp lerp at heq
      have h1 := congrArg Prod.fst heq
      have h2 := congrArg Prod.snd heq
      simp only at h1 h2
      by_contra hne'
      apply hne
      have hd : τ - τ' ≠ 0 := sub_ne_zero.2 hne'
      apply Prod.ext
      · have : (τ - τ') * ((C.vertex (k + 1)).1 - (C.vertex k).1) = 0 := by linarith
        have := (mul_eq_zero.1 this).resolve_left hd
        linarith
      · have : (τ - τ') * ((C.vertex (k + 1)).2 - (C.vertex k).2) = 0 := by linarith
        have := (mul_eq_zero.1 this).resolve_left hd
        linarith
    · exfalso
      apply C.sideOpen_not_mem_chainEdge hP hkm hk'm (Ne.symm hkk) ⟨hτ, hτ1⟩
      show cp C k τ ∈ C.chainEdge k'
      rw [heq, C.chainEdge_eq]
      exact Geometry.lerp_mem_segment _ _ hτ'.le hτ1'.le

/-- The tour index on the double circle: `j = (S + i) mod 2 m`. -/
noncomputable def tj (i : ℕ) : ℕ := (C.sideS C.sideBeta + i) % (2 * C.m)

/-- **The tour coordinate** of the tour position `(i, t)`: `u = j + t`. -/
noncomputable def tu (i : ℕ) (t : ℝ) : ℝ := (tj C i : ℝ) + t

theorem tj_lt (i : ℕ) : tj C i < 2 * C.m := Nat.mod_lt _ C.two_m_pos

/-- The chain coordinate of a tour position. -/
noncomputable def tk (i : ℕ) (t : ℝ) : ℕ × ℝ :=
  if tj C i < C.m then (tj C i, t)
  else if t = 0 then (2 * C.m - tj C i, 0) else (2 * C.m - tj C i - 1, 1 - t)

theorem tk_coord (i : ℕ) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    CCoord C (tk C i t).1 (tk C i t).2 := by
  have hj := tj_lt C i
  unfold tk CCoord
  split_ifs with h1 h2
  · exact Or.inl ⟨h1, ht, ht1⟩
  · rcases eq_or_lt_of_le (show 2 * C.m - tj C i ≤ C.m by omega) with e | e
    · exact Or.inr ⟨e, rfl⟩
    · exact Or.inl ⟨e, le_rfl, one_pos⟩
  · exact Or.inl ⟨by omega, by linarith, by
      have : 0 < t := lt_of_le_of_ne ht (Ne.symm h2)
      linarith⟩

/-- **The point of a tour position** in chain coordinates. -/
theorem tour_pt (i : ℕ) (hi : i < 2 * C.m) (t : ℝ) :
    sidePt (C.sideWalk C.sideBeta) (i + 6) t = cp C (tk C i t).1 (tk C i t).2 := by
  rw [C.sidePt_tour C.sideBeta hi]
  unfold Chain.sideTour
  have e1 : C.sideIdx C.sideBeta i = sideE C.m (tj C i) := Chain.sideIdx_eq C C.sideBeta i
  have e2 : C.sideIdx C.sideBeta (i + 1) = sideE C.m (tj C i + 1) := C.sideIdx_succ C.sideBeta i
  have hj := tj_lt C i
  have hm := C.one_le
  rw [e1, e2]
  unfold tk cp
  generalize tj C i = j at hj ⊢
  have sE1 : ∀ x, x ≤ C.m → sideE C.m x = x := fun x hx => by unfold sideE; simp [hx]
  have sE3 : ∀ x, C.m ≤ x → sideE C.m x = 2 * C.m - x := fun x hx => by
    unfold sideE
    rcases eq_or_lt_of_le hx with e | e
    · subst e; simp only [le_refl, ↓reduceIte]; omega
    · simp [show ¬ x ≤ C.m by omega]
  split_ifs with h1 h2
  · simp only
    rw [sE1 j h1.le, sE1 (j + 1) (by omega)]
  · simp only
    subst h2
    rw [lerp_zero, lerp_zero, sE3 j (by omega)]
  · simp only
    rw [Geometry.lerp_symm, sE3 (j + 1) (by omega), sE3 j (by omega)]
    congr 2; omega

/-- **Two tour positions have the same point iff their tour coordinates are equal or opposite.** -/
theorem same_point (hP : C.P.Simple) {i i' : ℕ} (hi : i < 2 * C.m) (hi' : i' < 2 * C.m) {t t' : ℝ}
    (ht : 0 ≤ t) (ht1 : t < 1) (ht' : 0 ≤ t') (ht1' : t' < 1)
    (heq : sidePt (C.sideWalk C.sideBeta) (i + 6) t = sidePt (C.sideWalk C.sideBeta) (i' + 6) t') :
    tu C i t = tu C i' t' ∨ tu C i t + tu C i' t' = 2 * C.m := by
  rw [tour_pt C i hi, tour_pt C i' hi'] at heq
  obtain ⟨hk, hτ⟩ := cp_inj C hP (tk_coord C i ht ht1) (tk_coord C i' ht' ht1') heq
  have hj := tj_lt C i
  have hj' := tj_lt C i'
  unfold tu
  unfold tk at hk hτ
  split_ifs at hk hτ with h1 h2 h3 h4 h5 h6 h7 h8 <;> simp only at hk hτ
  all_goals first
    | (left
       have hc : (tj C i : ℝ) = tj C i' := by exact_mod_cast (by omega : tj C i = tj C i')
       linarith)
    | (right
       have hc : (tj C i : ℝ) + tj C i' = 2 * C.m := by
         exact_mod_cast (by omega : tj C i + tj C i' = 2 * C.m)
       linarith)
    | (right
       have hc : (tj C i : ℝ) + tj C i' + 1 = 2 * C.m := by
         exact_mod_cast (by omega : tj C i + tj C i' + 1 = 2 * C.m)
       linarith)
    | (exfalso; linarith)

/-! ## Positions at a point of the chain -/

/-- **Every walk position whose point is on the chain is a tour position** (or the closing vertex
`2 m + 6`, the top again). -/
theorem pos_on_chain {p : ℕ} (hp : p < 2 * C.m + 7) {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1)
    (hx : sidePt (C.sideWalk C.sideBeta) p t ∈ C.set) :
    (6 ≤ p ∧ p < 2 * C.m + 6) ∨ (p = 2 * C.m + 6 ∧ t = 0) := by
  by_cases h5 : p ≤ 5
  · exact absurd hx (C.sideWalk_box_pt C.sideBeta (Or.inl h5) ht ht1).1
  · by_cases hl : p = 2 * C.m + 6
    · subst hl
      rcases eq_or_lt_of_le ht with h0 | h0
      · exact Or.inr ⟨rfl, h0.symm⟩
      · exact absurd hx (C.sideWalk_box_pt C.sideBeta (Or.inr ⟨rfl, h0⟩) ht ht1).1
    · exact Or.inl ⟨by omega, by omega⟩

/-- The closing vertex of the walk is the top, like the first tour vertex. -/
theorem sidePt_last :
    sidePt (C.sideWalk C.sideBeta) (2 * C.m + 6) 0 = sidePt (C.sideWalk C.sideBeta) (0 + 6) 0 := by
  rw [Chazelle.Chain.sidePt_zero, Chazelle.Chain.sidePt_zero, C.sideWalk_vtx_tour C.sideBeta le_rfl,
    Chain.sideTour_two_m, zero_add, C.sideWalk_vtx_six]

/-- The tour coordinate in terms of the key: `tu i t = S + (6 + i + t) - 6 - 2 m q`. -/
theorem tu_eq (i : ℕ) (t : ℝ) :
    ∃ q : ℕ, tu C i t = (C.sideS C.sideBeta : ℝ) + i + t - 2 * C.m * q := by
  refine ⟨(C.sideS C.sideBeta + i) / (2 * C.m), ?_⟩
  unfold tu tj
  have h := Nat.mod_add_div (C.sideS C.sideBeta + i) (2 * C.m)
  have h' : (((C.sideS C.sideBeta + i) % (2 * C.m) : ℕ) : ℝ) + (2 * C.m : ℕ) *
      (((C.sideS C.sideBeta + i) / (2 * C.m) : ℕ) : ℝ) = (C.sideS C.sideBeta : ℝ) + i := by
    exact_mod_cast h
  push_cast at h'
  linarith

/-- **The mirror of a chain point**: two distinct walk keys `κ ≠ κ'` (positions with parameters in
`[0, 1)`) of the same point of the chain satisfy `κ + κ' ≡ 12 - 2 S (mod 2 m)`, or they are the
two visits `6`, `2 m + 6` of the top at the ends of the tour. -/
theorem mirror_sum (hP : C.P.Simple) {p p' : ℕ} (hp : p < 2 * C.m + 7) (hp' : p' < 2 * C.m + 7)
    {t t' : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (ht' : 0 ≤ t') (ht1' : t' < 1)
    (hx : sidePt (C.sideWalk C.sideBeta) p t ∈ C.set)
    (heq : sidePt (C.sideWalk C.sideBeta) p t = sidePt (C.sideWalk C.sideBeta) p' t')
    (hne : (p : ℝ) + t ≠ p' + t') :
    (∃ n : ℤ, ((p : ℝ) + t) + (p' + t') = 12 - 2 * C.sideS C.sideBeta + 2 * C.m * n) ∨
      ((p : ℝ) + t = 6 ∧ (p' : ℝ) + t' = 2 * C.m + 6) ∨
      ((p : ℝ) + t = 2 * C.m + 6 ∧ (p' : ℝ) + t' = 6) := by
  have hx' : sidePt (C.sideWalk C.sideBeta) p' t' ∈ C.set := heq ▸ hx
  have hm := C.one_le
  -- normalise each position to a tour position `(i, t)` with `i < 2 m` and a shift `e ∈ {0, 2m}`
  have norm : ∀ {p : ℕ} {t : ℝ}, p < 2 * C.m + 7 → 0 ≤ t → t < 1 →
      sidePt (C.sideWalk C.sideBeta) p t ∈ C.set →
      ∃ i : ℕ, ∃ e : ℕ, i < 2 * C.m ∧ (e = 0 ∨ e = 2 * C.m) ∧ (p : ℝ) + t = 6 + i + t + e ∧
        sidePt (C.sideWalk C.sideBeta) p t = sidePt (C.sideWalk C.sideBeta) (i + 6) t ∧
        (e = 2 * C.m → i = 0 ∧ t = 0) := by
    intro p t hp ht ht1 hx
    rcases pos_on_chain C hp ht ht1 hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨p - 6, 0, by omega, Or.inl rfl, ?_, by rw [show p - 6 + 6 = p by omega], by omega⟩
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    · subst h1; subst h2
      refine ⟨0, 2 * C.m, by omega, Or.inr rfl, by push_cast; ring, sidePt_last C, fun _ => ⟨rfl, rfl⟩⟩
  obtain ⟨i, e, hi, he, hk, hpt, he2⟩ := norm hp ht ht1 hx
  obtain ⟨i', e', hi', he', hk', hpt', he2'⟩ := norm hp' ht' ht1' hx'
  have heq' : sidePt (C.sideWalk C.sideBeta) (i + 6) t = sidePt (C.sideWalk C.sideBeta) (i' + 6) t' := by
    rwa [← hpt, ← hpt']
  obtain ⟨q, hq⟩ := tu_eq C i t
  obtain ⟨q', hq'⟩ := tu_eq C i' t'
  rcases same_point C hP hi hi' ht ht1 ht' ht1' heq' with h | h
  · -- equal tour coordinates: the keys differ by a multiple of `2 m`, hence are `6` and `2 m + 6`
    have hdiff : ((i : ℝ) + t) - (i' + t') = 2 * C.m * ((q : ℝ) - q') := by
      rw [hq, hq'] at h; linarith
    -- `|(i + t) - (i' + t')| < 2 m`, so the multiple is `0`
    have hlt1 : (i : ℝ) + t < 2 * C.m := by
      have : (i : ℝ) + 1 ≤ 2 * C.m := by exact_mod_cast hi
      linarith
    have hlt2 : (i' : ℝ) + t' < 2 * C.m := by
      have : (i' : ℝ) + 1 ≤ 2 * C.m := by exact_mod_cast hi'
      linarith
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have hi0' : (0 : ℝ) ≤ i' := Nat.cast_nonneg i'
    have hqq : (q : ℤ) = q' := by
      have h1 : 2 * (C.m : ℝ) * ((q : ℝ) - q') < 2 * C.m := by linarith
      have h2 : -(2 * (C.m : ℝ)) < 2 * C.m * ((q : ℝ) - q') := by linarith
      have h3 : ((q : ℝ) - q') < 1 := by nlinarith
      have h4 : -1 < ((q : ℝ) - q') := by nlinarith
      have h5 : ((q : ℤ) : ℝ) - ((q' : ℤ) : ℝ) < 1 := by push_cast; linarith
      have h6 : -1 < ((q : ℤ) : ℝ) - ((q' : ℤ) : ℝ) := by push_cast; linarith
      have h7 : (q : ℤ) - q' < 1 := by exact_mod_cast h5
      have h8 : -1 < (q : ℤ) - q' := by exact_mod_cast h6
      omega
    have hqq' : (q : ℝ) = q' := by exact_mod_cast hqq
    have hsame : (i : ℝ) + t = i' + t' := by rw [hqq'] at hdiff; linarith
    -- so the keys differ only by the shifts `e, e'`
    right
    rcases he with rfl | rfl <;> rcases he' with rfl | rfl
    · exact absurd (by rw [hk, hk']; push_cast; linarith) hne
    · obtain ⟨rfl, rfl⟩ := he2' rfl
      have : (i : ℝ) + t = 0 := by simpa using hsame
      left; constructor <;> [rw [hk]; rw [hk']] <;> push_cast <;> linarith
    · obtain ⟨rfl, rfl⟩ := he2 rfl
      have : (i' : ℝ) + t' = 0 := by simpa using hsame.symm
      right; constructor <;> [rw [hk]; rw [hk']] <;> push_cast <;> linarith
    · exact absurd (by rw [hk, hk']; push_cast; linarith) hne
  · -- opposite tour coordinates
    left
    rcases he with rfl | rfl <;> rcases he' with rfl | rfl
    · refine ⟨1 + q + q', ?_⟩
      rw [hk, hk']; push_cast; linarith
    · refine ⟨2 + q + q', ?_⟩
      rw [hk, hk']; push_cast; linarith
    · refine ⟨2 + q + q', ?_⟩
      rw [hk, hk']; push_cast; linarith
    · refine ⟨3 + q + q', ?_⟩
      rw [hk, hk']; push_cast; linarith

end OracleQ

end

end Chazelle.Core
