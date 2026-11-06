module

public import Chazelle.Core.WalkEmbed
public import Chazelle.RewriteTactics
public import Chazelle.MiscTactics
public import Chazelle.ChainTactics

/-!
# Walk embeddings, part 2: the walk of a chain model read from a tour position (gap O1)

The walk `sideWalk sideBeta` of the chain model of a chain `C` (`m` edges, `n = 2m + 7` walk
vertices) consists of the box block and the Euler tour of the double boundary of `C`, started at
the tour position `bS C = sideS sideBeta` (a copy of the top vertex).  Read from the walk vertex of
any tour position `J` (key `6 + tpos C J`), the walk visits

* the tour vertices `tourV C J d` for `d ≤ s = 2m - tpos C J` (`walk_tour`),
* then the box block `boxPt C e`, `e ≤ 7` (`walk_box`; it starts and ends at the top vertex),
* then the tour vertices `tourV C J (s + e)` again (`walk_after`).

The counted walk edges are exactly those joining two points of the open box (`counted_iff_box`),
so counting transfers along agreeing stretches of two chain walks with the same box.

For a junction `J` the tours of `C₁ = J.left` and `C₂ = J.right` read from the shared vertex are
the two halves of the tour of `C = J.whole` read from its two copies of the shared vertex
(`tourV_left`, `tourV_right`).
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Chain (sideE sideInArc)

namespace WalkEmbed

section ChainWalk

variable (C : Chain)

/-- The tour position of the box (a copy of the top vertex). -/
noncomputable def bS : ℕ := C.sideS C.sideBeta

theorem bS_le : bS C ≤ 2 * C.m := C.sideS_lt _

/-- The tour offset of the tour position `J` from the box. -/
noncomputable def tpos (J : ℕ) : ℕ := (J + 2 * C.m - bS C) % (2 * C.m)

theorem tpos_lt (J : ℕ) : tpos C J < 2 * C.m := Nat.mod_lt _ C.two_m_pos

/-- The vertex at step `d` of the Euler tour read from the tour position `J`. -/
noncomputable def tourV (J d : ℕ) : Point := C.vertex (sideE C.m ((J + d) % (2 * C.m)))

/-- The box block of the walk, read from the top vertex: the top, the top of the slit, the four
corners, the top of the slit and the top again. -/
noncomputable def boxPt : ℕ → Point
  | 0 => C.top
  | 1 => C.slitTop
  | 2 => (-C.radius, C.radius)
  | 3 => (-C.radius, -C.radius)
  | 4 => (C.radius, -C.radius)
  | 5 => (C.radius, C.radius)
  | 6 => C.slitTop
  | _ => C.top

theorem cm_W : (chainModel C).W = C.sideWalk C.sideBeta := rfl

theorem cm_n : (chainModel C).W.n = 2 * C.m + 7 := C.sideWalk_n _

theorem bS_add_tpos (J : ℕ) : bS C + tpos C J ≡ J [MOD 2 * C.m] := by
  unfold tpos
  have hb := bS_le C
  have e : (bS C + (J + 2 * C.m - bS C) % (2 * C.m)) % (2 * C.m) =
      (bS C + (J + 2 * C.m - bS C)) % (2 * C.m) := Nat.add_mod_mod _ _ _
  unfold Nat.ModEq
  rw [e, show bS C + (J + 2 * C.m - bS C) = J + 2 * C.m by omega, Nat.add_mod_right]

/-- **The walk read from a tour position**: before the box. -/
theorem walk_tour (J d : ℕ) (hd : tpos C J + d ≤ 2 * C.m) :
    (chainModel C).W.vtx ((6 + tpos C J + d) % (chainModel C).W.n) = tourV C J d := by
  rw [cm_n, Nat.mod_eq_of_lt (by omega), cm_W, show 6 + tpos C J + d = (tpos C J + d) + 6 by ring,
    C.sideWalk_vtx_tour _ hd]
  unfold Chain.sideTour tourV
  rw [Chain.sideIdx_eq]
  congr 2
  have h := (bS_add_tpos C J).add_right d
  unfold Nat.ModEq at h
  rw [← Nat.add_assoc]
  exact h

theorem box_mod {e : ℕ} (he0 : 1 ≤ e) (he : e ≤ 7) : (2 * C.m + 6 + e) % (2 * C.m + 7) = e - 1 := by
  rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

/-- **The walk read from a tour position**: the box block. -/
theorem walk_box (J e : ℕ) (he : e ≤ 7) :
    (chainModel C).W.vtx ((6 + tpos C J + (2 * C.m - tpos C J) + e) % (chainModel C).W.n) =
      boxPt C e := by
  have ht := tpos_lt C J
  rw [cm_n, show 6 + tpos C J + (2 * C.m - tpos C J) + e = 2 * C.m + 6 + e by omega, cm_W]
  rcases Nat.eq_zero_or_pos e with rfl | he0
  · rw [Nat.mod_eq_of_lt (by omega), add_zero, C.sideWalk_vtx_tour _ le_rfl, C.sideTour_two_m]
    rfl
  rw [box_mod C he0 he]
  interval_cases e <;> first | rfl | exact C.sideWalk_vtx_six _

/-- **The walk read from a tour position**: after the box. -/
theorem walk_after (J e : ℕ) (he : e ≤ 2 * C.m) :
    (chainModel C).W.vtx ((6 + tpos C J + (2 * C.m - tpos C J) + 7 + e) % (chainModel C).W.n) =
      tourV C J (2 * C.m - tpos C J + e) := by
  have ht := tpos_lt C J
  rw [cm_n, show 6 + tpos C J + (2 * C.m - tpos C J) + 7 + e = (e + 6) + (2 * C.m + 7) by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega), cm_W, C.sideWalk_vtx_tour _ he]
  unfold Chain.sideTour tourV
  rw [Chain.sideIdx_eq]
  congr 2
  -- `J + (2m - tpos) ≡ bS`
  have h1 := bS_add_tpos C J
  have h2 : J + (2 * C.m - tpos C J) ≡ bS C [MOD 2 * C.m] := by
    apply Nat.ModEq.add_right_cancel' (tpos C J)
    rw [show J + (2 * C.m - tpos C J) + tpos C J = J + 2 * C.m by omega]
    calc J + 2 * C.m ≡ J + 0 [MOD 2 * C.m] := Nat.ModEq.add_left J (by simp [Nat.ModEq])
      _ = J := by rw [add_zero]
      _ ≡ bS C + tpos C J [MOD 2 * C.m] := h1.symm
  have h3 := h2.add_right e
  unfold Nat.ModEq at h3
  rw [← Nat.add_assoc]
  exact h3.symm

/-- The top of the slit is not in the open box. -/
theorem slitTop_not_mem_box : C.slitTop ∉ Chain.box C.radius := fun h => by
  have := h.2
  simp only [Chain.slitTop, abs_of_pos C.radius_pos] at this
  exact lt_irrefl _ this

theorem corner_not_mem_box {a b : ℝ} (h : a = C.radius ∨ a = -C.radius) :
    ((a, b) : Point) ∉ Chain.box C.radius := fun hb => by
  have := hb.1
  simp only at this
  rcases h with rfl | rfl
  · rw [abs_of_pos C.radius_pos] at this; exact lt_irrefl _ this
  · rw [abs_neg, abs_of_pos C.radius_pos] at this; exact lt_irrefl _ this

/-- **Counted walk edges are the edges joining two points of the open box.** -/
theorem counted_iff_box {p : ℕ} (hp : p < (chainModel C).W.n) :
    (chainModel C).counted p ↔ (chainModel C).W.vtx p ∈ Chain.box C.radius ∧
      (chainModel C).W.vtx ((p + 1) % (chainModel C).W.n) ∈ Chain.box C.radius := by
  have hn := cm_n C
  rw [hn] at hp ⊢
  show 6 ≤ p ∧ p < 2 * C.m + 6 ↔ _
  rw [cm_W]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨i, rfl⟩ : ∃ i, p = i + 6 := ⟨p - 6, by omega⟩
    rw [C.sideWalk_vtx_tour _ (by omega), show i + 6 + 1 = (i + 1) + 6 by ring,
      Nat.mod_eq_of_lt (by omega), C.sideWalk_vtx_tour _ (by omega)]
    exact ⟨C.set_subset_box (C.vertex_mem_set (C.sideIdx_le _ _)),
      C.set_subset_box (C.vertex_mem_set (C.sideIdx_le _ _))⟩
  · rintro ⟨h1, h2⟩
    by_contra hc
    have hR := C.radius_pos
    rcases (show p ≤ 5 ∨ p = 2 * C.m + 6 by omega) with hp5 | rfl
    · interval_cases p
      · exact slitTop_not_mem_box C h1
      · exact corner_not_mem_box C (Or.inr rfl) h1
      · exact corner_not_mem_box C (Or.inr rfl) h1
      · exact corner_not_mem_box C (Or.inl rfl) h1
      · exact corner_not_mem_box C (Or.inl rfl) h1
      · exact slitTop_not_mem_box C h1
    · rw [box_mod C le_rfl (by omega)] at h2
      exact slitTop_not_mem_box C h2

/-- The box block depends only on the top vertex and the box radius. -/
theorem boxPt_congr {C' : Chain} (ht : C.top = C'.top) (hR : C.radius = C'.radius) (e : ℕ) :
    boxPt C e = boxPt C' e := by
  unfold boxPt Chain.slitTop
  rw [ht, hR]

/-- The top vertex starts the box block. -/
theorem boxPt_zero : boxPt C 0 = C.top := rfl

end ChainWalk

/-! ## Agreement of two chain walks along a common tour stretch -/

section TwoChains

variable {C C' : Chain} {J J' ℓ : ℕ}

/-- **Case N** (no box inside the stretch in either walk): the walks agree along the tour. -/
theorem agree_N (hT : ∀ e, e ≤ ℓ → tourV C J e = tourV C' J' e)
    (hs : ℓ ≤ 2 * C.m - tpos C J) (hs' : ℓ ≤ 2 * C'.m - tpos C' J') :
    Agree (chainModel C).W (chainModel C').W (6 + tpos C J) (6 + tpos C' J') ℓ := by
  intro d hd
  rw [walk_tour C J d (by have := tpos_lt C J; omega),
    walk_tour C' J' d (by have := tpos_lt C' J'; omega)]
  exact hT d hd

/-- The top vertices agree when the boxes sit at the same offset of the stretch. -/
theorem top_eq_of_box (hT : ∀ e, e ≤ ℓ → tourV C J e = tourV C' J' e)
    (hss : 2 * C.m - tpos C J = 2 * C'.m - tpos C' J') (hsl : 2 * C.m - tpos C J ≤ ℓ) :
    C.top = C'.top := by
  have h1 := walk_box C J 0 (by omega)
  have h2 := walk_box C' J' 0 (by omega)
  have h3 := walk_tour C J (2 * C.m - tpos C J) (by have := tpos_lt C J; omega)
  have h4 := walk_tour C' J' (2 * C'.m - tpos C' J') (by have := tpos_lt C' J'; omega)
  rw [add_zero] at h1 h2
  rw [boxPt_zero] at h1 h2
  rw [← h1, h3, ← h2, h4, ← hss]
  exact hT _ hsl

/-- **Case Sh** (the box at the same offset strictly inside the stretch of both walks): the walks
agree along the tour and the box. -/
theorem agree_Sh (hT : ∀ e, e ≤ ℓ → tourV C J e = tourV C' J' e) (hR : C.radius = C'.radius)
    (hℓ : ℓ ≤ 2 * C.m) (hℓ' : ℓ ≤ 2 * C'.m)
    (hss : 2 * C.m - tpos C J = 2 * C'.m - tpos C' J') (hsl : 2 * C.m - tpos C J < ℓ) :
    Agree (chainModel C).W (chainModel C').W (6 + tpos C J) (6 + tpos C' J') (ℓ + 7) := by
  have htop := top_eq_of_box hT hss hsl.le
  have ht := tpos_lt C J
  have ht' := tpos_lt C' J'
  set s := 2 * C.m - tpos C J with hs
  intro d hd
  rcases le_or_gt d s with h1 | h1
  · rw [walk_tour C J d (by omega), walk_tour C' J' d (by omega)]
    exact hT d (by omega)
  rcases le_or_gt d (s + 7) with h2 | h2
  · obtain ⟨e, rfl⟩ : ∃ e, d = s + e := ⟨d - s, by omega⟩
    have hb := walk_box C J e (by omega)
    have hb' := walk_box C' J' e (by omega)
    rw [show 6 + tpos C J + (s + e) = 6 + tpos C J + (2 * C.m - tpos C J) + e by omega, hb,
      show 6 + tpos C' J' + (s + e) = 6 + tpos C' J' + (2 * C'.m - tpos C' J') + e by omega, hb']
    exact boxPt_congr C htop hR e
  · obtain ⟨e, rfl⟩ : ∃ e, d = s + 7 + e := ⟨d - s - 7, by omega⟩
    have hb := walk_after C J e (by omega)
    have hb' := walk_after C' J' e (by omega)
    rw [show 6 + tpos C J + (s + 7 + e) = 6 + tpos C J + (2 * C.m - tpos C J) + 7 + e by omega,
      hb, show 6 + tpos C' J' + (s + 7 + e) = 6 + tpos C' J' + (2 * C'.m - tpos C' J') + 7 + e by
        omega, hb', ← hss]
    exact hT _ (by omega)

/-- **Case G, first piece** (the box strictly inside the stretch of the second walk only): the
walks agree up to the box of the second walk. -/
theorem agree_G1 (hT : ∀ e, e ≤ ℓ → tourV C J e = tourV C' J' e)
    (hs : ℓ ≤ 2 * C.m - tpos C J) (hs' : 2 * C'.m - tpos C' J' < ℓ) :
    Agree (chainModel C).W (chainModel C').W (6 + tpos C J) (6 + tpos C' J')
      (2 * C'.m - tpos C' J') := by
  intro d hd
  rw [walk_tour C J d (by have := tpos_lt C J; omega),
    walk_tour C' J' d (by have := tpos_lt C' J'; omega)]
  exact hT d (by omega)

/-- **Case G, second piece**: the walks agree from the box of the second walk (skipped) to the
end of the stretch. -/
theorem agree_G2 (hT : ∀ e, e ≤ ℓ → tourV C J e = tourV C' J' e) (hℓ' : ℓ ≤ 2 * C'.m)
    (hs : ℓ ≤ 2 * C.m - tpos C J) (hs' : 2 * C'.m - tpos C' J' < ℓ) :
    Agree (chainModel C).W (chainModel C').W
      ((6 + tpos C J + (2 * C'.m - tpos C' J')) % (chainModel C).W.n)
      ((6 + tpos C' J' + (2 * C'.m - tpos C' J') + 7) % (chainModel C').W.n)
      (ℓ - (2 * C'.m - tpos C' J')) := by
  have ht := tpos_lt C J
  have ht' := tpos_lt C' J'
  intro d hd
  rw [Nat.mod_add_mod, Nat.mod_add_mod, Nat.add_assoc (6 + tpos C J),
    walk_tour C J _ (by omega), walk_after C' J' d (by omega)]
  exact hT _ (by omega)

end TwoChains

/-! ## The tours of a junction -/

section Junction

variable (J : Merge.Junction)

/-- **The left half of the tour**: the tour of `C₁` read from the shared vertex is the tour of
`C` read from the copy of the shared vertex left towards `C₁` (tour position `m₁ + 2 m₂`). -/
theorem tourV_left {e : ℕ} (he : e ≤ 2 * J.m₁) :
    tourV J.whole (J.m₁ + 2 * J.m₂) e = tourV J.left J.m₁ e := by
  unfold tourV
  simp only [Merge.Junction.whole_m, Merge.Junction.left_m]
  have h1 := J.one_le_m₁
  have h2 := J.one_le_m₂
  rw [Merge.Junction.whole_vertex]
  congr 1
  rcases Nat.lt_or_ge e J.m₁ with h | h
  · rw [Nat.mod_eq_of_lt (show J.m₁ + 2 * J.m₂ + e < 2 * (J.m₁ + J.m₂) by omega),
      Nat.mod_eq_of_lt (show J.m₁ + e < 2 * J.m₁ by omega)]
    unfold sideE; splao
  · rw [Nat.mod_eq_sub_mod (show 2 * (J.m₁ + J.m₂) ≤ J.m₁ + 2 * J.m₂ + e by omega),
      Nat.mod_eq_of_lt (show J.m₁ + 2 * J.m₂ + e - 2 * (J.m₁ + J.m₂) < 2 * (J.m₁ + J.m₂) by omega),
      Nat.mod_eq_sub_mod (show 2 * J.m₁ ≤ J.m₁ + e by omega),
      Nat.mod_eq_of_lt (show J.m₁ + e - 2 * J.m₁ < 2 * J.m₁ by omega)]
    unfold sideE; splao

/-- **The right half of the tour**: the tour of `C₂` read from the shared vertex (tour position
`0`) is the tour of `C` read from the copy of the shared vertex left towards `C₂` (tour position
`m₁`). -/
theorem tourV_right {e : ℕ} (he : e ≤ 2 * J.m₂) :
    tourV J.whole J.m₁ e = tourV J.right 0 e := by
  unfold tourV
  simp only [Merge.Junction.whole_m, Merge.Junction.right_m, zero_add]
  have h1 := J.one_le_m₁
  have h2 := J.one_le_m₂
  rw [Nat.mod_eq_of_lt (show J.m₁ + e < 2 * (J.m₁ + J.m₂) by omega)]
  rcases Nat.lt_or_ge e (2 * J.m₂) with h | h
  · rw [Nat.mod_eq_of_lt h]
    rcases le_or_gt e J.m₂ with h' | h'
    · have e1 : sideE (J.m₁ + J.m₂) (J.m₁ + e) = J.m₁ + e := by unfold sideE; splao
      have e2 : sideE J.m₂ e = e := by unfold sideE; splao
      rw [e1, e2, Merge.Junction.whole_vertex_add]
    · have e1 : sideE (J.m₁ + J.m₂) (J.m₁ + e) = J.m₁ + (2 * J.m₂ - e) := by
        unfold sideE; splao
      have e2 : sideE J.m₂ e = 2 * J.m₂ - e := by unfold sideE; splao
      rw [e1, e2, Merge.Junction.whole_vertex_add]
  · have he' : e = 2 * J.m₂ := by omega
    subst he'
    rw [Nat.mod_self]
    have e1 : sideE (J.m₁ + J.m₂) (J.m₁ + 2 * J.m₂) = J.m₁ + 0 := by
      unfold sideE; splao
    rw [e1, Chain.sideE_zero, Merge.Junction.whole_vertex_add]

/-- The shared vertex starts the left tour. -/
theorem tourV_left_zero : tourV J.left J.m₁ 0 = J.shared := by
  unfold tourV
  simp only [Merge.Junction.left_m, add_zero]
  rw [Nat.mod_eq_of_lt (by have := J.one_le_m₁; omega)]
  urr sideE [ite_eq_left le_rfl]

/-- The shared vertex ends the left tour. -/
theorem tourV_left_end : tourV J.left J.m₁ (2 * J.m₁) = J.shared := by
  have := tourV_left_zero J
  unfold tourV at this ⊢
  rw [← this]
  congr 2
  simp only [Merge.Junction.left_m]
  rw [show J.m₁ + 2 * J.m₁ = J.m₁ + 0 + 2 * J.m₁ by ring, Nat.add_mod_right]

/-- The shared vertex starts the right tour. -/
theorem tourV_right_zero : tourV J.right 0 0 = J.shared := by
  unfold tourV
  simp only [add_zero, Nat.zero_mod, Chain.sideE_zero]
  exact J.right_vertex_zero

/-- The shared vertex ends the right tour. -/
theorem tourV_right_end : tourV J.right 0 (2 * J.m₂) = J.shared := by
  unfold tourV
  simp only [zero_add, Merge.Junction.right_m, Nat.mod_self, Chain.sideE_zero]
  exact J.right_vertex_zero

/-! ### Where the boxes are -/

/-- If the top of `C` lies strictly inside `C₁`, it is the top of `C₁`. -/
theorem left_topIdx_eq (h : J.whole.topIdx < J.m₁) : J.left.topIdx = J.whole.topIdx := by
  have hT := J.whole.topIdx_le
  apply le_antisymm
  · refine J.left.topIdx_min (by rwo [Merge.Junction.left_m]) fun i hi => ?_
    rw [Merge.Junction.left_m] at hi
    rw [← Merge.Junction.whole_vertex, ← Merge.Junction.whole_vertex]
    exact J.whole.vertex_snd_le_top (by rwo [Merge.Junction.whole_m])
  · have hL := J.left.topIdx_le
    rw [Merge.Junction.left_m] at hL
    refine J.whole.topIdx_min (by rwo [Merge.Junction.whole_m]) fun i hi => ?_
    calc (J.whole.vertex i).2 ≤ J.whole.top.2 := J.whole.vertex_snd_le_top hi
      _ = (J.left.vertex J.whole.topIdx).2 := rfl
      _ ≤ (J.left.vertex J.left.topIdx).2 :=
          J.left.vertex_snd_le_top (by rwo [Merge.Junction.left_m])
      _ = (J.whole.vertex J.left.topIdx).2 := rfl

/-- If the top of `C` lies strictly inside `C₂`, it is the top of `C₂`. -/
theorem right_topIdx_eq (h : J.m₁ < J.whole.topIdx) :
    J.right.topIdx = J.whole.topIdx - J.m₁ := by
  have hT := J.whole.topIdx_le
  rw [Merge.Junction.whole_m] at hT
  have hv : ∀ j, J.right.vertex j = J.whole.vertex (J.m₁ + j) := fun j =>
    (Merge.Junction.whole_vertex_add J j).symm
  apply le_antisymm
  · refine J.right.topIdx_min (by rwo [Merge.Junction.right_m]) fun i hi => ?_
    rw [Merge.Junction.right_m] at hi
    rw [hv, hv, show J.m₁ + (J.whole.topIdx - J.m₁) = J.whole.topIdx by omega]
    exact J.whole.vertex_snd_le_top (by rwo [Merge.Junction.whole_m])
  · have hR := J.right.topIdx_le
    rw [Merge.Junction.right_m] at hR
    suffices J.whole.topIdx ≤ J.m₁ + J.right.topIdx by omega
    refine J.whole.topIdx_min (by rwo [Merge.Junction.whole_m]) fun i hi => ?_
    calc (J.whole.vertex i).2 ≤ J.whole.top.2 := J.whole.vertex_snd_le_top hi
      _ = (J.right.vertex (J.whole.topIdx - J.m₁)).2 := by
          rwr [hv, show J.m₁ + (J.whole.topIdx - J.m₁) = J.whole.topIdx by omega]
      _ ≤ (J.right.vertex J.right.topIdx).2 :=
          J.right.vertex_snd_le_top (by rwo [Merge.Junction.right_m])
      _ = (J.whole.vertex (J.m₁ + J.right.topIdx)).2 := by rw [hv]

theorem left_sideBeta_eq (h : J.whole.topIdx < J.m₁) : J.left.sideBeta = J.whole.sideBeta := by
  have e := left_topIdx_eq J h
  have htop : J.left.top = J.whole.top := by urr Chain.top [e]
  unfold Chain.sideBeta Chain.slitTop
  rw [htop, e]
  rfl

theorem right_sideBeta_eq (h : J.m₁ < J.whole.topIdx) : J.right.sideBeta = J.whole.sideBeta := by
  have e := right_topIdx_eq J h
  have hv : ∀ j, J.right.vertex j = J.whole.vertex (J.m₁ + j) := fun j =>
    (Merge.Junction.whole_vertex_add J j).symm
  have hr : J.right.radius = J.whole.radius := rfl
  have htop : J.right.top = J.whole.top := by
    unfold Chain.top; rw [e, hv, show J.m₁ + (J.whole.topIdx - J.m₁) = J.whole.topIdx by omega]
  unfold Chain.sideBeta Chain.slitTop
  rw [htop, e, hv, hv, hr,
    show J.m₁ + (J.whole.topIdx - J.m₁ + 1) = J.whole.topIdx + 1 by omega,
    show J.m₁ + (J.whole.topIdx - J.m₁ - 1) = J.whole.topIdx - 1 by omega]

/-- **The box of `C` inside the left stretch is the box of `C₁`**: if the box of the walk of `C`
lies strictly inside the stretch read from the copy of the shared vertex left towards `C₁`, then
the box of the walk of `C₁` lies at the same offset of the left tour. -/
theorem left_box_eq (h : 2 * J.whole.m - tpos J.whole (J.m₁ + 2 * J.m₂) < 2 * J.m₁) :
    2 * J.left.m - tpos J.left J.m₁ = 2 * J.whole.m - tpos J.whole (J.m₁ + 2 * J.m₂) := by
  have h1 := J.one_le_m₁
  have h2 := J.one_le_m₂
  have hT := J.whole.topIdx_le
  simp only [Merge.Junction.whole_m, Merge.Junction.left_m] at hT h ⊢
  unfold tpos bS Chain.sideS at *
  simp only [Merge.Junction.whole_m, Merge.Junction.left_m] at *
  -- the top of `C` is inside `C₁`
  have hTl : J.whole.topIdx < J.m₁ := by
    cases hb : J.whole.sideBeta <;> simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
    · by_contra hc
      rw [Nat.mod_eq_sub_mod (show 2 * (J.m₁ + J.m₂) ≤
          J.m₁ + 2 * J.m₂ + 2 * (J.m₁ + J.m₂) - (2 * (J.m₁ + J.m₂) - J.whole.topIdx) by omega),
        Nat.mod_eq_of_lt (by omega)] at h
      omega
    · rw [Nat.mod_eq_sub_mod (show 2 * (J.m₁ + J.m₂) ≤
          J.m₁ + 2 * J.m₂ + 2 * (J.m₁ + J.m₂) - J.whole.topIdx by omega),
        Nat.mod_eq_of_lt (by omega)] at h
      omega
  rw [left_sideBeta_eq J hTl, left_topIdx_eq J hTl]
  cases hb : J.whole.sideBeta <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  · rw [Nat.mod_eq_of_lt (show J.m₁ + 2 * J.m₂ + 2 * (J.m₁ + J.m₂) -
        (2 * (J.m₁ + J.m₂) - J.whole.topIdx) < 2 * (J.m₁ + J.m₂) by omega),
      Nat.mod_eq_of_lt (show J.m₁ + 2 * J.m₁ - (2 * J.m₁ - J.whole.topIdx) < 2 * J.m₁ by omega)]
    omega
  · rw [Nat.mod_eq_sub_mod (show 2 * (J.m₁ + J.m₂) ≤
        J.m₁ + 2 * J.m₂ + 2 * (J.m₁ + J.m₂) - J.whole.topIdx by omega),
      Nat.mod_eq_of_lt (show J.m₁ + 2 * J.m₂ + 2 * (J.m₁ + J.m₂) - J.whole.topIdx -
        2 * (J.m₁ + J.m₂) < 2 * (J.m₁ + J.m₂) by omega),
      Nat.mod_eq_sub_mod (show 2 * J.m₁ ≤ J.m₁ + 2 * J.m₁ - J.whole.topIdx by omega),
      Nat.mod_eq_of_lt (show J.m₁ + 2 * J.m₁ - J.whole.topIdx - 2 * J.m₁ < 2 * J.m₁ by omega)]
    omega

/-- **The box of `C` inside the right stretch is the box of `C₂`.** -/
theorem right_box_eq (h : 2 * J.whole.m - tpos J.whole J.m₁ < 2 * J.m₂) :
    2 * J.right.m - tpos J.right 0 = 2 * J.whole.m - tpos J.whole J.m₁ := by
  have h1 := J.one_le_m₁
  have h2 := J.one_le_m₂
  have hT := J.whole.topIdx_le
  simp only [Merge.Junction.whole_m, Merge.Junction.right_m] at hT h ⊢
  unfold tpos bS Chain.sideS at *
  simp only [Merge.Junction.whole_m, Merge.Junction.right_m] at *
  have hTr : J.m₁ < J.whole.topIdx := by
    cases hb : J.whole.sideBeta <;> simp only [hb, Bool.false_eq_true, ↓reduceIte] at h
    · by_contra hc
      rw [Nat.mod_eq_of_lt (show J.m₁ + 2 * (J.m₁ + J.m₂) -
          (2 * (J.m₁ + J.m₂) - J.whole.topIdx) < 2 * (J.m₁ + J.m₂) by omega)] at h
      omega
    · by_contra hc
      rw [Nat.mod_eq_sub_mod (show 2 * (J.m₁ + J.m₂) ≤
          J.m₁ + 2 * (J.m₁ + J.m₂) - J.whole.topIdx by omega),
        Nat.mod_eq_of_lt (by omega)] at h
      omega
  have hTR := right_topIdx_eq J hTr
  rw [right_sideBeta_eq J hTr, hTR]
  cases hb : J.whole.sideBeta <;> simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
  · rw [Nat.mod_eq_of_lt (show J.m₁ + 2 * (J.m₁ + J.m₂) -
        (2 * (J.m₁ + J.m₂) - J.whole.topIdx) < 2 * (J.m₁ + J.m₂) by omega),
      Nat.mod_eq_of_lt (show 0 + 2 * J.m₂ - (2 * J.m₂ - (J.whole.topIdx - J.m₁)) < 2 * J.m₂ by
        omega)]
    omega
  · rw [Nat.mod_eq_of_lt (show J.m₁ + 2 * (J.m₁ + J.m₂) - J.whole.topIdx < 2 * (J.m₁ + J.m₂) by
        omega),
      Nat.mod_eq_of_lt (show 0 + 2 * J.m₂ - (J.whole.topIdx - J.m₁) < 2 * J.m₂ by omega)]
    omega

end Junction

end WalkEmbed

end

end Chazelle.Core
