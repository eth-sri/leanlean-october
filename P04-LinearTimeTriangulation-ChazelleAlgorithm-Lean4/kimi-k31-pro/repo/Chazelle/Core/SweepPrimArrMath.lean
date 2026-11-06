module

public import Chazelle.Core.SweepPrimLeft
public import Chazelle.RewriteTactics
public import Chazelle.MiscTactics

/-!
# Sweep RAM primitives (WP-D2), part 7: the mathematics of `arrivalPos`

`arrivalPos` (design-merge-v2 §9.6 item 1) finds, for a walk position `x` of `chainModel C` and
a direction `σ`, a walk position `(p, h)` of the point `w = pos x` whose left sector contains the
arriving ray (`Sweep.Arrival`), or reports that there is none.  The positions of `w` on the walk:

* `w` inside a walk edge: the edge, and its **twin** (the same piece of the boundary traversed
  backwards: the other side of a chain edge on the tour, the other slit edge `5 ↔ 2m + 6`), at the
  same height code (`twin_pos_param`, `tour_twin`, `slit_twin`); an open vertical side of the box
  has no twin (`wall_unique`).  Exactly one of the edge and its twin has the arriving ray in its
  (half-plane) sector.
* `w` a vertex `v_k` of the chain: the tour vertices `6 + i` with `sideIdx i = k`, which are
  `candIdx m S k`, `candIdx m S (2m - k)` and, for the top vertex, `2m` (`cand_complete`,
  `vertex_positions`).  `candIdx m S j` inverts `i ↦ (S + i) mod 2m` without leaving `[0, 2m]`.
-/

namespace Chazelle.Core

namespace SweepPrim

open Chazelle.Chain (sideE sideLeft sidePt)

@[expose] public section

/-! ## Inverting the tour index -/

/-- The tour step whose tour position is `j`, by one conditional subtraction. -/
def candIdx (m S j : ℕ) : ℕ := if j < S then j + (2 * m - S) else j - S

theorem candIdx_mod {m S j : ℕ} (hS : S ≤ 2 * m) (hj : j < 2 * m) :
    (S + candIdx m S j) % (2 * m) = j ∧ candIdx m S j < 2 * m := by
  unfold candIdx
  split_ifs with h
  · refine ⟨?_, by omega⟩
    rw [show S + (j + (2 * m - S)) = j + 2 * m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
  · exact ⟨by rw [show S + (j - S) = j by omega, Nat.mod_eq_of_lt hj], by omega⟩

/-- The tour index of a candidate is the chain vertex of the tour position. -/
theorem sideIdx_candIdx (C : Chain) (β : Bool) {j : ℕ} (hj : j ≤ 2 * C.m) :
    candIdx C.m (C.sideS β) j ≤ 2 * C.m ∧ C.sideIdx β (candIdx C.m (C.sideS β) j) = sideE C.m j := by
  have hS := C.sideS_lt β
  have hm := C.one_le
  rcases hj.lt_or_eq with hj | rfl
  · obtain ⟨h1, h2⟩ := candIdx_mod (m := C.m) hS hj
    exact ⟨h2.le, by rw [C.sideIdx_eq, h1]⟩
  · unfold candIdx
    rw [ite_eq_right (by omega)]
    refine ⟨by omega, ?_⟩
    rw [C.sideIdx_eq, show C.sideS β + (2 * C.m - C.sideS β) = 2 * C.m by omega, Nat.mod_self]
    unfold sideE; splao

theorem sideE_rev {m j : ℕ} (hj : j ≤ m) : sideE m (2 * m - j) = j := by
  unfold sideE; splao

/-- **The candidate tour steps of a chain vertex.** -/
theorem cand_vertex (C : Chain) (β : Bool) {k : ℕ} (hk : k ≤ C.m) :
    (candIdx C.m (C.sideS β) k ≤ 2 * C.m ∧ C.sideIdx β (candIdx C.m (C.sideS β) k) = k) ∧
      (candIdx C.m (C.sideS β) (2 * C.m - k) ≤ 2 * C.m ∧
        C.sideIdx β (candIdx C.m (C.sideS β) (2 * C.m - k)) = k) := by
  obtain ⟨a1, a2⟩ := sideIdx_candIdx C β (j := k) (by omega)
  obtain ⟨b1, b2⟩ := sideIdx_candIdx C β (j := 2 * C.m - k) (by omega)
  refine ⟨⟨a1, ?_⟩, ⟨b1, ?_⟩⟩
  · rw [a2]; unfold sideE; split_ifs; omega
  · rw [b2, sideE_rev hk]

/-- **Every tour step of a chain vertex is a candidate.** -/
theorem cand_complete (C : Chain) (β : Bool) {i k : ℕ} (hi : i ≤ 2 * C.m)
    (hk : C.sideIdx β i = k) :
    i = candIdx C.m (C.sideS β) k ∨ i = candIdx C.m (C.sideS β) (2 * C.m - k) ∨ i = 2 * C.m := by
  have hS := C.sideS_lt β
  have hm := C.one_le
  rcases hi.lt_or_eq with hi | hi
  · rw [C.sideIdx_eq] at hk
    have hj := Nat.mod_lt (C.sideS β + i) (show 0 < 2 * C.m by omega)
    set j := (C.sideS β + i) % (2 * C.m) with hjdef
    have hji : i = candIdx C.m (C.sideS β) j := by
      unfold candIdx
      by_cases h : C.sideS β + i < 2 * C.m
      · rw [Nat.mod_eq_of_lt h] at hjdef
        rwo [ite_eq_right (by omega)]
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hjdef
        rwo [ite_eq_left (by omega)]
    have hjk : j = k ∨ j = 2 * C.m - k := by
      rw [← hk]; unfold sideE; splao
    rcases hjk with h | h
    · left; rw [hji, h]
    · right; left; rw [hji, h]
  · exact Or.inr (Or.inr hi)

/-! ## Twin edges -/

/-- **Twin edges**: an edge whose ends are those of `p` swapped carries the same points at the same
height codes, with the complementary parameter. -/
theorem twin_pos_param (M : Model) (Q : Polygon) {p p' h : ℕ} (hh : 1 ≤ h)
    (h1 : M.wa p' = M.wb p) (h2 : M.wb p' = M.wa p) (hne : (M.wa p).2 ≠ (M.wb p).2) :
    M.pos Q ⟨p', h⟩ = M.pos Q ⟨p, h⟩ ∧ M.param Q ⟨p', h⟩ = 1 - M.param Q ⟨p, h⟩ := by
  obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
  have hne'  := sub_ne_zero.2 hne.symm
  have hne''  := sub_ne_zero.2 hne
  have hpar : M.param Q ⟨p', h' + 1⟩ = 1 - M.param Q ⟨p, h' + 1⟩ := by
    unfold Model.param
    simp only
    rw [h1, h2, ite_eq_right (Ne.symm hne), ite_eq_right hne]
    field_simp
    ring
  refine ⟨?_, hpar⟩
  unfold Model.pos
  simp only
  rw [hpar, h1, h2]
  apply Geometry.point_ext <;> simp [Geometry.lerp] <;> ring

/-- The two slit edges are twins. -/
theorem slit_twin (C : Chain) :
    (chainModel C).wa 5 = (chainModel C).wb (2 * C.m + 6) ∧
      (chainModel C).wb 5 = (chainModel C).wa (2 * C.m + 6) := by
  have hm := C.one_le
  have hn := C.sideWalk_n C.sideBeta
  simp only [Model.wa, Model.wb, chainModel]
  refine ⟨?_, ?_⟩
  · rw [C.sideWalk_next_last, C.sideWalk_vtx_five, C.sideWalk_vtx_zero]
  · rw [hn, Nat.mod_eq_of_lt (by omega), C.sideWalk_vtx_six, C.sideWalk_vtx_tour _ le_rfl,
      C.sideTour_two_m]

theorem slit_twin' (C : Chain) :
    (chainModel C).wa (2 * C.m + 6) = (chainModel C).wb 5 ∧
      (chainModel C).wb (2 * C.m + 6) = (chainModel C).wa 5 :=
  ⟨(slit_twin C).2.symm, (slit_twin C).1.symm⟩

/-- The twin tour step of tour edge `i`: the reversed tour position `2m - 1 - j`. -/
noncomputable def tourTwin (C : Chain) (i : ℕ) : ℕ :=
  candIdx C.m (C.sideS C.sideBeta) (2 * C.m - 1 - (C.sideS C.sideBeta + i) % (2 * C.m))

/-- **The twin of a tour edge.** -/
theorem tour_twin (C : Chain) {i : ℕ} (hi : i < 2 * C.m) :
    tourTwin C i < 2 * C.m ∧
      (chainModel C).wa (tourTwin C i + 6) = (chainModel C).wb (i + 6) ∧
      (chainModel C).wb (tourTwin C i + 6) = (chainModel C).wa (i + 6) := by
  have hm := C.one_le
  have hS := C.sideS_lt C.sideBeta
  have hj := Nat.mod_lt (C.sideS C.sideBeta + i) (show 0 < 2 * C.m by omega)
  set j := (C.sideS C.sideBeta + i) % (2 * C.m) with hjdef
  obtain ⟨h1, h2⟩ := candIdx_mod (m := C.m) (j := 2 * C.m - 1 - j) hS (by omega)
  have ht : tourTwin C i = candIdx C.m (C.sideS C.sideBeta) (2 * C.m - 1 - j) := rfl
  rw [← ht] at h1 h2
  refine ⟨h2, ?_, ?_⟩
  · simp only [Model.wa, Model.wb]
    rw [show (chainModel C).W = C.sideWalk C.sideBeta from rfl, C.sideWalk_next_tour _ hi,
      C.sideWalk_vtx_tour _ h2.le, C.sideWalk_vtx_tour _ (by omega)]
    unfold Chain.sideTour
    congr 1
    rw [C.sideIdx_eq, h1, C.sideIdx_succ, ← hjdef]
    unfold sideE; splao
  · simp only [Model.wa, Model.wb]
    rw [show (chainModel C).W = C.sideWalk C.sideBeta from rfl, C.sideWalk_next_tour _ h2,
      C.sideWalk_vtx_tour _ (by omega), C.sideWalk_vtx_tour _ hi.le]
    unfold Chain.sideTour
    congr 1
    rw [C.sideIdx_succ, h1, C.sideIdx_eq, ← hjdef]
    unfold sideE; splao

/-! ## The positions of a point of a vertical side of the box -/

/-- **A point inside an open vertical side of the box has one position.** -/
theorem wall_unique (C : Chain) (hP : C.P.Simple) {e : ℕ} (he : e = 1 ∨ e = 3) {t₀ : ℝ}
    (ht₀ : 0 < t₀) (ht₀1 : t₀ < 1) {p : ℕ} {t : ℝ} (hp : p < (chainModel C).W.n) (ht : 0 ≤ t)
    (ht1 : t < 1) (heq : sidePt (chainModel C).W p t = sidePt (chainModel C).W e t₀) :
    p = e ∧ t = t₀ := by
  have hW : (chainModel C).W = C.sideWalk C.sideBeta := rfl
  rw [hW] at heq hp
  have hR := C.radius_pos
  have hcb := C.coordBound_lt_radius
  obtain ⟨-, e1, -, e3, -, -, -⟩ := C.sidePt_box C.sideBeta t₀
  have hw : |(sidePt (C.sideWalk C.sideBeta) e t₀).1| = C.radius ∧
      |(sidePt (C.sideWalk C.sideBeta) e t₀).2| < C.radius ∧
      ((e = 1 ∧ (sidePt (C.sideWalk C.sideBeta) e t₀).1 = -C.radius) ∨
        (e = 3 ∧ (sidePt (C.sideWalk C.sideBeta) e t₀).1 = C.radius)) := by
    rcases he with rfl | rfl
    · rw [e1]; simp only [abs_neg, abs_of_pos hR, true_and]
      refine ⟨abs_lt.2 ⟨by nlinarith, by nlinarith⟩, by simp⟩
    · rw [e3]; simp only [abs_of_pos hR, true_and]
      refine ⟨abs_lt.2 ⟨by nlinarith, by nlinarith⟩, by simp⟩
  rw [← heq] at hw
  obtain ⟨hw1, hw2, hw3⟩ := hw
  rcases C.sideWalk_pos_cases C.sideBeta hp ht with hbox | ⟨i, hi, rfl, hit⟩
  · obtain ⟨-, hside⟩ := C.sideWalk_box_pt C.sideBeta hbox ht ht1
    obtain ⟨hpe, -⟩ := hside hw1 hw2
    have hpe' : p = e := by
      rcases hpe with ⟨rfl, h1⟩ | ⟨rfl, h1⟩ <;> rcases hw3 with ⟨rfl, h2⟩ | ⟨rfl, h2⟩
      · rfl
      · linarith
      · linarith
      · rfl
    subst hpe'
    refine ⟨rfl, ?_⟩
    have hnd := C.sideWalk_nd hP C.sideBeta p hp
    exact Geometry.lerp_injective hnd heq
  · exfalso
    have hmem := C.sideWalk_tour_pt_mem C.sideBeta hi hit ht ht1
    have := (C.abs_le_coordBound_of_mem_set hmem).1
    linarith

/-! ## The positions of a chain vertex -/

/-- **The positions of a vertex of the chain** are tour vertices of that vertex. -/
theorem vertex_positions (C : Chain) (hP : C.P.Simple) {k : ℕ} (hk : k ≤ C.m) {p : ℕ} {t : ℝ}
    (hp : p < (chainModel C).W.n) (ht : 0 ≤ t) (ht1 : t < 1)
    (heq : sidePt (chainModel C).W p t = C.vertex k) :
    t = 0 ∧ ∃ i, i ≤ 2 * C.m ∧ p = i + 6 ∧ C.sideIdx C.sideBeta i = k := by
  have hW : (chainModel C).W = C.sideWalk C.sideBeta := rfl
  rw [hW] at heq hp
  have hmem := C.vertex_mem_set hk
  rcases C.sideWalk_pos_cases C.sideBeta hp ht with hbox | ⟨i, hi, rfl, hit⟩
  · exact absurd (heq ▸ hmem) (C.sideWalk_box_pt C.sideBeta hbox ht ht1).1
  · have ht0 : t = 0 := by
      rcases hi.lt_or_eq with hi' | hi'
      · by_contra h0
        have htp : t ∈ Set.Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne ht (Ne.symm h0), ht1⟩
        obtain ⟨k', -, s, hs, hpt, -⟩ := C.sideTour_open C.sideBeta hi' htp
        rw [hpt] at heq
        exact C.sideOpen_ne_vertex hP hs heq
      · exact hit hi'
    subst ht0
    refine ⟨rfl, i, hi, rfl, ?_⟩
    rw [Chazelle.Chain.sidePt_zero, C.sideWalk_vtx_tour _ hi] at heq
    exact C.sideVertex_inj hP (C.sideIdx_le _ _) hk heq

end

end SweepPrim

end Chazelle.Core
