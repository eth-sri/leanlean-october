module

public import Chazelle.Golf

public import Chazelle.Core.DownPhaseDrvXDef

/-!
# Down phase, extraction (D6): the corrected walk of a chain from index `0`

For a chain `C` of a simple polygon with `C.s = 0` (chain vertex `k` is `C.P.vtx k`) and the walk
`C.sideWalk C.sideBeta`:

* `walk_vtx`, `walk_next`, `walk_prev`: the tour vertices at, after and before walk edge `p`
  (`tK`, `kNext`, `kPrev`: up on side `A`, down on side `B`);
* `walk_sector_edge`: inside a tour edge the left sector is the left half-plane of the edge;
* `walk_sector_vtx`: at a tour vertex away from the two chain ends the left sector lies in the
  corner `kPrev → tK → kNext` (also at the top vertex next to the slit, `SideGood`);
* `walk_box`: the points of the box and slit edges are far, or above the top vertex.
-/

namespace Chazelle.Core

namespace DrvX

@[expose] public section

open Set
open Chazelle.Chain (sideE sidePt sideLeft sideLeftOf sideCcw)

/-- The next chain vertex along side `A` (up) or `B` (down). -/
def kNext (A : Bool) (k : ℕ) : ℕ := if A then k + 1 else k - 1

/-- The previous chain vertex along side `A` (up) or `B` (down). -/
def kPrev (A : Bool) (k : ℕ) : ℕ := if A then k - 1 else k + 1

variable {C : Chain}

theorem chain_vertex_eq (hs : C.s = 0) {k : ℕ} (hk : k < C.P.n) : C.vertex k = C.P.vtx k := by
  unfold Chain.vertex Chain.edgeIdx; rw [hs, zero_add, Nat.mod_eq_of_lt hk]

theorem sideIdx_eq_tK (β : Bool) (i : ℕ) : C.sideIdx β i = tK C.m C.topIdx β (i + 6) := by
  Ξ Chain.sideIdx_eq
  unfold tK tU tS
  Ξ Nat.add_sub_cancel
  rfl

theorem tU_eq (β : Bool) (i : ℕ) :
    tU C.m C.topIdx β (i + 6) = (C.sideS β + i) % (2 * C.m) := by
  unfold tU tS; rw [Nat.add_sub_cancel]; rfl

/-- **The tour vertex at the start of walk edge `p`.** -/
theorem walk_vtx (hs : C.s = 0) (hm : C.m + 1 = C.P.n) (β : Bool) {p : ℕ} (h6 : 6 ≤ p)
    (hp : p ≤ 2 * C.m + 6) : (C.sideWalk β).vtx p = C.P.vtx (tK C.m C.topIdx β p) := by
  obtain ⟨i, rfl⟩ : ∃ i, p = i + 6 := ⟨p - 6, ⋄⟩
  rw [C.sideWalk_vtx_tour β (⋄)]
  unfold Chain.sideTour
  Ξ sideIdx_eq_tK, chain_vertex_eq hs (by have := tK_le β C.one_le (i + 6) (T := C.topIdx); omega)

theorem sideE_succ' {m u : ℕ} (hu : u < 2 * m) :
    sideE m (u + 1) = kNext (decide (u < m)) (sideE m u) := by
  unfold sideE kNext
  by_cases h : u < m
  · rw [decide_eq_true h]; simp only [ite_true]; split_ifs <;> omega
  · rw [decide_eq_false h]; simp only [Bool.false_eq_true, ite_false]; split_ifs <;> omega

/-- **The tour vertex at the end of walk edge `p`.** -/
theorem walk_next (hs : C.s = 0) (hm : C.m + 1 = C.P.n) (β : Bool) {p : ℕ} (h6 : 6 ≤ p)
    (hp : p < 2 * C.m + 6) :
    (C.sideWalk β).vtx ((p + 1) % (C.sideWalk β).n) =
      C.P.vtx (kNext (decide (tU C.m C.topIdx β p < C.m)) (tK C.m C.topIdx β p)) := by
  obtain ⟨i, rfl⟩ : ∃ i, p = i + 6 := ⟨p - 6, by omega⟩
  have hm1 := C.one_le
  rw [C.sideWalk_next_tour β (by omega), C.sideWalk_vtx_tour β (by omega)]
  unfold Chain.sideTour
  have hle := C.sideIdx_le β (i + 1)
  have hu := Nat.mod_lt (C.sideS β + i) (show 0 < 2 * C.m by omega)
  rw [chain_vertex_eq hs (by omega), C.sideIdx_succ, tK, tU_eq, sideE_succ' hu]

theorem sideE_pred' {m u : ℕ} (hu0 : 1 ≤ u) (hu : u < 2 * m) (hum : u ≠ m) :
    sideE m (u - 1) = kPrev (decide (u < m)) (sideE m u) := by
  unfold sideE kPrev
  by_cases h : u < m
  · rw [decide_eq_true h]; simp only [ite_true]; split_ifs <;> omega
  · rw [decide_eq_false h]; simp only [Bool.false_eq_true, ite_false]; split_ifs <;> omega

theorem mod_pred {x M : ℕ} (hM : 0 < M) (hx : 1 ≤ x % M) : (x - 1) % M = x % M - 1 := by
  have h1 := Nat.div_add_mod x M
  have h2 : x - 1 = M * (x / M) + (x % M - 1) := ⋄
  Ξ h2, Nat.mul_add_mod, Nat.mod_eq_of_lt (by have := Nat.mod_lt x hM; omega)

/-- **The tour vertex before walk edge `p`** (away from the chain ends). -/
theorem walk_prev (hs : C.s = 0) (hm : C.m + 1 = C.P.n) (β : Bool) {p : ℕ} (h7 : 7 ≤ p)
    (hp : p ≤ 2 * C.m + 6) (hu0 : tU C.m C.topIdx β p ≠ 0) (hum : tU C.m C.topIdx β p ≠ C.m) :
    (C.sideWalk β).vtx ((p + (C.sideWalk β).n - 1) % (C.sideWalk β).n) =
      C.P.vtx (kPrev (decide (tU C.m C.topIdx β p < C.m)) (tK C.m C.topIdx β p)) := by
  obtain ⟨i, rfl⟩ : ∃ i, p = (i + 1) + 6 := ⟨p - 7, ⋄⟩
  have hm1 := C.one_le
  rw [C.sideWalk_prev_tour β (⋄) (by omega), C.sideWalk_vtx_tour β (by omega)]
  unfold Chain.sideTour
  have hle := C.sideIdx_le β (i + 1 - 1)
  rw [chain_vertex_eq hs (⋄), Nat.add_sub_cancel, Chain.sideIdx_eq, tK]
  have hu := tU_lt (T := C.topIdx) β hm1 (i + 1 + 6)
  rw [← sideE_pred' (⋄) hu hum]
  congr 1
  rw [tU_eq] at hu0 ⊢
  rw [← mod_pred (⋄) (by omega), show C.sideS β + (i + 1) - 1 = C.sideS β + i by omega]

/-! ## Sectors -/

/-- **Inside a tour edge** the left sector is the left half-plane of the chain edge. -/
theorem walk_sector_edge (hP : C.P.Simple) (hs : C.s = 0) (hm : C.m + 1 = C.P.n) (β : Bool)
    {p : ℕ} (h6 : 6 ≤ p) (hp : p < 2 * C.m + 6) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (x : Point) :
    sideLeft (C.sideWalk β) p t x ↔
      0 < det (C.P.vtx (tK C.m C.topIdx β p))
        (C.P.vtx (kNext (decide (tU C.m C.topIdx β p < C.m)) (tK C.m C.topIdx β p))) x := by
  have hne : (C.sideWalk β).vtx p ≠ (C.sideWalk β).vtx ((p + 1) % (C.sideWalk β).n) := by
    obtain ⟨i, rfl⟩ : ∃ i, p = i + 6 := ⟨p - 6, ⋄⟩
    rw [C.sideWalk_next_tour β (⋄), C.sideWalk_vtx_tour β (by omega),
      C.sideWalk_vtx_tour β (⋄)]
    unfold Chain.sideTour
    rcases C.sideTour_step β i with h | h
    · rw [h]; exact C.sideVertex_succ_ne hP _
    · rw [← h]; exact (C.sideVertex_succ_ne hP _).symm
  Ξ Chazelle.Chain.sideLeft_edge hne ht, walk_vtx hs hm β h6 hp.le, walk_next hs hm β h6 hp

/-- **At a tour vertex** away from the chain ends, the left sector lies in the corner of the
chain on the side of the position (at the top vertex: the sub-corner beside the slit). -/
theorem walk_sector_vtx (hP : C.P.Simple) (hs : C.s = 0) (hm : C.m + 1 = C.P.n) {p : ℕ}
    (h6 : 6 ≤ p) (hp : p ≤ 2 * C.m + 6) (hu0 : tU C.m C.topIdx C.sideBeta p ≠ 0)
    (hum : tU C.m C.topIdx C.sideBeta p ≠ C.m) {x : Point}
    (h : sideLeft (C.sideWalk C.sideBeta) p 0 x) :
    sideLeftOf
      (C.P.vtx (kPrev (decide (tU C.m C.topIdx C.sideBeta p < C.m)) (tK C.m C.topIdx C.sideBeta p)))
      (C.P.vtx (tK C.m C.topIdx C.sideBeta p))
      (C.P.vtx (kNext (decide (tU C.m C.topIdx C.sideBeta p < C.m)) (tK C.m C.topIdx C.sideBeta p)))
      x := by
  set β := C.sideBeta with hβ
  have hm1 := C.one_le
  rcases lt_or_eq_of_le h6 with h7 | h6'
  · rcases lt_or_eq_of_le hp with hp' | hp'
    · -- an inner tour vertex
      obtain ⟨i, rfl⟩ : ∃ i, p = i + 6 := ⟨p - 6, by omega⟩
      rw [C.sideLeft_tour_inner β (by omega) (by omega)] at h
      have e1 := walk_prev hs hm β (show 7 ≤ i + 6 by omega) hp'.le hu0 hum
      have e2 := walk_next hs hm β h6 hp'
      have e3 := walk_vtx hs hm β h6 hp'.le
      rw [C.sideWalk_prev_tour β (by omega) (by omega), C.sideWalk_vtx_tour β (by omega)] at e1
      rw [C.sideWalk_next_tour β (by omega), C.sideWalk_vtx_tour β (by omega)] at e2
      rw [C.sideWalk_vtx_tour β (by omega)] at e3
      rw [← e1, ← e2, ← e3]; exact h
    · -- the last position, up the slit
      subst hp'
      rw [C.sideLeft_tour_last] at h
      have hT : tK C.m C.topIdx β (2 * C.m + 6) = C.topIdx := by
        rw [← sideIdx_eq_tK]; exact C.sideIdx_two_m β
      have hT0 : C.topIdx ≠ 0 := by
        rw [← hT]; exact fun h0 => hu0 ((tK_eq_zero_iff β hm1 _).1 h0)
      have hTm : C.topIdx ≠ C.m := by
        rw [← hT]; exact fun h0 => hum ((tK_eq_m_iff β hm1 _).1 h0)
      have hgood : sideCcw (C.sideTour β 1 - C.top) (C.slitTop - C.top)
          (C.sideTour β (2 * C.m - 1) - C.top) := by
        rcases C.sideGood_sideBeta hP with h' | h' | h'
        · exact absurd h' hT0
        · exact absurd h' hTm
        · exact h'
      have e1 := walk_prev hs hm β (show 7 ≤ 2 * C.m + 6 by omega) le_rfl hu0 hum
      rw [C.sideWalk_prev_tour β (by omega) le_rfl, C.sideWalk_vtx_tour β (by omega)] at e1
      have e2 := walk_next hs hm β (show 6 ≤ 6 by omega) (show 6 < 2 * C.m + 6 by omega)
      rw [show 6 = 0 + 6 from rfl, C.sideWalk_next_tour β (by omega),
        C.sideWalk_vtx_tour β (by omega)] at e2
      have hU : tU C.m C.topIdx β (2 * C.m + 6) = tU C.m C.topIdx β 6 := tU_last _ _ _
      have hK6 : tK C.m C.topIdx β 6 = tK C.m C.topIdx β (2 * C.m + 6) := (tK_last _ _ _).symm
      rw [hK6, ← hU] at e2
      have hTop : C.top = C.P.vtx (tK C.m C.topIdx β (2 * C.m + 6)) := by
        rw [hT]; unfold Chain.top; exact chain_vertex_eq hs (by have := C.topIdx_le; omega)
      rw [← e1, ← hTop]
      rw [← e2]
      unfold sideLeftOf at h ⊢
      exact Chazelle.Chain.sideCcw_sub_right (sub_ne_zero.2 (C.sideTour_one_ne_top hP β))
        (sub_ne_zero.2 C.sideSlitTop_ne_top)
        (sub_ne_zero.2 (C.sideTour_last_ne_top hP β)) hgood h
  · -- the first position, down the slit
    subst h6'
    rw [show (6 : ℕ) = 0 + 6 from rfl, C.sideLeft_tour_first] at h
    have hT : tK C.m C.topIdx β 6 = C.topIdx := by
      rw [show (6 : ℕ) = 0 + 6 from rfl, ← sideIdx_eq_tK]; exact C.sideIdx_zero β
    have hT0 : C.topIdx ≠ 0 := by
      rw [← hT]; exact fun h0 => hu0 ((tK_eq_zero_iff β hm1 _).1 h0)
    have hTm : C.topIdx ≠ C.m := by
      rw [← hT]; exact fun h0 => hum ((tK_eq_m_iff β hm1 _).1 h0)
    have hgood : sideCcw (C.sideTour β 1 - C.top) (C.slitTop - C.top)
        (C.sideTour β (2 * C.m - 1) - C.top) := by
      rcases C.sideGood_sideBeta hP with h' | h' | h'
      · exact absurd h' hT0
      · exact absurd h' hTm
      · exact h'
    have hU : tU C.m C.topIdx β (2 * C.m + 6) = tU C.m C.topIdx β 6 := tU_last _ _ _
    have hK6 : tK C.m C.topIdx β (2 * C.m + 6) = tK C.m C.topIdx β 6 := tK_last _ _ _
    have e1 := walk_prev hs hm β (show 7 ≤ 2 * C.m + 6 by omega) le_rfl
      (by rw [hU]; exact hu0) (by rw [hU]; exact hum)
    rw [C.sideWalk_prev_tour β (by omega) le_rfl, C.sideWalk_vtx_tour β (by omega), hU,
      hK6] at e1
    have e2 := walk_next hs hm β (show 6 ≤ 6 by omega) (show 6 < 2 * C.m + 6 by omega)
    rw [show 6 = 0 + 6 from rfl, C.sideWalk_next_tour β (by omega),
      C.sideWalk_vtx_tour β (by omega)] at e2
    have hTop : C.top = C.P.vtx (tK C.m C.topIdx β (0 + 6)) := by
      rw [show (0 + 6 : ℕ) = 6 from rfl, hT]; unfold Chain.top
      exact chain_vertex_eq hs (by have := C.topIdx_le; omega)
    rw [show (0 + 6 : ℕ) = 6 from rfl] at hTop e2
    rw [← e1, ← hTop, ← e2]
    unfold sideLeftOf at h ⊢
    exact Chazelle.Chain.sideCcw_sub_left (sub_ne_zero.2 (C.sideTour_one_ne_top hP β)) hgood h

/-! ## The box and the slit -/

/-- **The points of the box and slit edges** (and of the slit above the top vertex) are outside
the square of the coordinates of `C.P`, or above all its vertices. -/
theorem walk_box (β : Bool) {p : ℕ} {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t < 1)
    (hp : p ≤ 5 ∨ (p = 2 * C.m + 6 ∧ 0 < t)) :
    Chazelle.Jordan.coordBound C.P < |(sidePt (C.sideWalk β) p t).1| ∨
      Chazelle.Jordan.coordBound C.P < |(sidePt (C.sideWalk β) p t).2| ∨
      C.top.2 < (sidePt (C.sideWalk β) p t).2 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6⟩ := C.sidePt_box β t
  have hr := C.coordBound_lt_radius
  have hr0 := C.radius_pos
  have htr := C.top_snd_lt_radius
  rcases hp with hp | ⟨rfl, ht⟩
  · interval_cases p
    · right; left; rw [b0]; simp only; rw [abs_of_pos hr0]; exact hr
    · left; rw [b1]; simp only; rw [abs_neg, abs_of_pos hr0]; exact hr
    · right; left; rw [b2]; simp only; rw [abs_neg, abs_of_pos hr0]; exact hr
    · left; rw [b3]; simp only; rw [abs_of_pos hr0]; exact hr
    · right; left; rw [b4]; simp only; rw [abs_of_pos hr0]; exact hr
    · right; right; rw [b5]; simp only; nlinarith
  · right; right; rw [b6]; simp only; nlinarith

end

end DrvX

end Chazelle.Core
