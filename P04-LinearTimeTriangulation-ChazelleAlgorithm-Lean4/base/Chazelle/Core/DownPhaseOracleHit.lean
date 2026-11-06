module

public import Chazelle.Core.DownPhaseOracleArc
public import Chazelle.Core.ShootCutOrig

/-!
# WP-M (E7-B, part 4): hit points, origins and inner points

The interior shooter answers with a position of the interior walk, but the chain shooter it
calls answers with a position of the walk of a chain model, possibly on the other side of the
double boundary.  Both name points of the boundary of `Q`, i.e. symbolic points of `Q` that are
vertices or lie strictly inside an edge (`BSym`):

* `hitSym C e h`: the boundary symbolic point of a chain-model position on the chain
  (`hitSym_spec`: it evaluates to the position, and is a boundary point);
* `iPos Q s`: the interior-walk position of a boundary symbolic point (`iPos_spec`: proper,
  on the walk, evaluating to the point).

Inner points (`Model.InnerPt`, finding G2): every point within the coordinate bound of `Q` is an
inner point of a chain model of `Q` (`innerPt_chain`), and inner points of the interior model lie
within that bound (`innerPt_interior_bound`).
-/

namespace Chazelle.Core

namespace IOrc

@[expose] public section

open Set
open Chazelle.Chain (sideInArc sideE)
open Chazelle.Geometry (lerp lerp_zero lerp_one)
open Chazelle.Visibility (xAt)

variable {Q : Polygon}

/-! ## Boundary symbolic points -/

/-- **A boundary symbolic point** of `Q`: a vertex, or a point of an edge strictly between the
heights of its ends. -/
def BSym (Q : Polygon) : SymPt → Prop
  | .vtx q => q < Q.n
  | .onEdge e h => e < Q.n ∧ h < Q.n ∧
      (((Q.vtx e).2 < (Q.vtx h).2 ∧ (Q.vtx h).2 < (Q.vtx ((e + 1) % Q.n)).2) ∨
        ((Q.vtx ((e + 1) % Q.n)).2 < (Q.vtx h).2 ∧ (Q.vtx h).2 < (Q.vtx e).2))

theorem BSym.lt {s : SymPt} (h : BSym Q s) : s.Lt Q.n := by
  cases s with
  | vtx q => exact h
  | onEdge e h' => exact ⟨h.1, h.2.1⟩

theorem iv_iv {q : ℕ} (hq : q < Q.n) : iv Q (iv Q q) = q := by
  unfold iv; split_ifs <;> omega

/-- The edge of the interior walk carrying the edge `e` of `Q`. -/
noncomputable def iEdge (Q : Polygon) (e : ℕ) : ℕ := by
  classical
  exact if Mountain.LeftInside Q then e else if e + 1 < Q.n then Q.n - 2 - e else Q.n - 1

theorem iEdge_lt (hn : 2 ≤ Q.n) {e : ℕ} (he : e < Q.n) : iEdge Q e < Q.n := by
  unfold iEdge; split_ifs <;> omega

/-- The two ends of the interior walk edge `iEdge e` are the ends of the edge `e` of `Q`. -/
theorem iEdge_ends (hn : 3 ≤ Q.n) {e : ℕ} (he : e < Q.n) :
    (iv Q (iEdge Q e) = e ∧ iv Q ((iEdge Q e + 1) % Q.n) = (e + 1) % Q.n) ∨
      (iv Q (iEdge Q e) = (e + 1) % Q.n ∧ iv Q ((iEdge Q e + 1) % Q.n) = e) := by
  unfold iEdge iv
  by_cases hL : Mountain.LeftInside Q
  · simp only [hL, ↓reduceIte]
    left; simp
  · simp only [hL, ↓reduceIte]
    right
    by_cases h1 : e + 1 < Q.n
    · simp only [h1, ↓reduceIte]
      rw [Nat.mod_eq_of_lt (show Q.n - 2 - e + 1 < Q.n by omega), Nat.mod_eq_of_lt h1]
      omega
    · simp only [h1, ↓reduceIte]
      rw [show Q.n - 1 + 1 = Q.n by omega, Nat.mod_self, show e + 1 = Q.n by omega, Nat.mod_self]
      omega

/-- **The interior-walk position of a boundary symbolic point.** -/
noncomputable def iPos (Q : Polygon) : SymPt → WPos
  | .vtx q => ⟨iv Q q, 0⟩
  | .onEdge e h => ⟨iEdge Q e, h + 1⟩

theorem mi_wa {p : ℕ} (hp : p < Q.n) : (interiorModel Q).wa p = Q.vtx (iv Q p) := iw_vtx hp

theorem mi_wb {p : ℕ} (hp : p < Q.n) :
    (interiorModel Q).wb p = Q.vtx (iv Q ((p + 1) % Q.n)) := by
  unfold Model.wb
  rw [mi_n]
  exact iw_vtx (Nat.mod_lt _ (by omega))

/-- The parameter of a height strictly between the heights of the ends. -/
theorem param_between {a b y : ℝ} (h : (a < y ∧ y < b) ∨ (b < y ∧ y < a)) :
    0 < (y - a) / (b - a) ∧ (y - a) / (b - a) < 1 := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hb : 0 < b - a := by linarith
    constructor
    · exact div_pos (by linarith) hb
    · rw [div_lt_one hb]; linarith
  · have hb : b - a < 0 := by linarith
    constructor
    · exact div_pos_of_neg_of_neg (by linarith) hb
    · rw [div_lt_one_of_neg hb]; linarith

/-- **The interior position of a boundary symbolic point** is proper, on the walk, and evaluates
to the point. -/
theorem iPos_spec (hD : DistinctHeights Q) (hn : 3 ≤ Q.n) {s : SymPt} (hs : BSym Q s) :
    ProperPos (interiorModel Q) Q Q.n (iPos Q s) ∧ (iPos Q s).edge < Q.n ∧
      (interiorModel Q).pos Q (iPos Q s) = s.eval Q := by
  cases s with
  | vtx q =>
    have hq : q < Q.n := hs
    refine ⟨⟨le_rfl, zero_lt_one, Nat.zero_le _⟩, iv_lt hq, ?_⟩
    show lerp ((interiorModel Q).wa (iv Q q)) ((interiorModel Q).wb (iv Q q)) 0 = Q.vtx q
    rw [lerp_zero, mi_wa (iv_lt hq), iv_iv hq]
  | onEdge e h =>
    obtain ⟨he, hh, hbt⟩ := hs
    have hp := iEdge_lt (show 2 ≤ Q.n by omega) he
    have hwa := mi_wa hp
    have hwb := mi_wb hp
    have hnh : ((interiorModel Q).wa (iEdge Q e)).2 ≠ ((interiorModel Q).wb (iEdge Q e)).2 := by
      rw [hwa, hwb]
      rcases iEdge_ends hn he with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2]; exact ShootCut.edge_nh hD (by omega) he
      · rw [e1, e2]; exact (ShootCut.edge_nh hD (by omega) he).symm
    -- the parameter lies in `(0, 1)`
    have hpar : 0 < (interiorModel Q).param Q ⟨iEdge Q e, h + 1⟩ ∧
        (interiorModel Q).param Q ⟨iEdge Q e, h + 1⟩ < 1 := by
      unfold Model.param
      simp only
      rw [ite_eq_right hnh, hwa, hwb]
      rcases iEdge_ends hn he with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2]; exact param_between hbt
      · rw [e1, e2]; exact param_between hbt.symm
    refine ⟨⟨hpar.1.le, hpar.2, by show h + 1 ≤ Q.n; omega⟩, hp, ?_⟩
    have hok : HostEdgeOK Q.n (.vtx (iv Q (iEdge Q e))) (.vtx (iv Q ((iEdge Q e + 1) % Q.n))) := by
      rcases iEdge_ends hn he with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2]; exact Or.inl rfl
      · rw [e1, e2]; exact Or.inr rfl
    have := ShootCut.pos_eq_onEdge (interiorModel Q) hD (by omega) (p := iEdge Q e) (h := h)
      (sp₁ := .vtx (iv Q (iEdge Q e))) (sp₂ := .vtx (iv Q ((iEdge Q e + 1) % Q.n))) hwa hwb
      (iv_lt hp) (iv_lt (Nat.mod_lt _ (by omega))) hok hnh
    rw [show iPos Q (.onEdge e h) = ⟨iEdge Q e, h + 1⟩ from rfl, this]
    congr 1
    rcases iEdge_ends hn he with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [e1, e2]; simp [ShootCut.edgeOf]
    · rw [e1, e2]
      simp only [ShootCut.edgeOf]
      rw [ite_eq_right]
      intro hc
      -- `e = (e + 2) mod n` is impossible for `n ≥ 3`
      have : e = (e + 2) % Q.n := by
        rw [Nat.mod_add_mod] at hc; exact hc
      rcases (show e + 2 < Q.n ∨ e + 2 = Q.n ∨ e + 2 = Q.n + 1 by omega) with h1 | h1 | h1
      · rw [Nat.mod_eq_of_lt h1] at this; omega
      · rw [h1, Nat.mod_self] at this; omega
      · rw [h1, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at this; omega

/-! ## Hit points of a chain model -/

section chain

variable (C : Chain)

/-- The vertex of `Q = C.P` at the walk vertex `e` (`6 ≤ e ≤ 2m + 6`) of the chain model. -/
noncomputable def cVtx (e : ℕ) : ℕ := (C.s + C.sideIdx C.sideBeta (e - 6)) % C.P.n

/-- **The boundary symbolic point of a chain-model position on the chain.** -/
noncomputable def hitSym (e h : ℕ) : SymPt := by
  classical
  exact if e < 6 ∨ 2 * C.m + 6 ≤ e then .vtx ((C.s + C.topIdx) % C.P.n)
    else if h = 0 ∨ h - 1 = cVtx C e then .vtx (cVtx C e)
    else .onEdge (ShootCut.edgeOf C.P.n (.vtx (cVtx C e)) (.vtx (cVtx C (e + 1)))) (h - 1)

theorem cVtx_lt (e : ℕ) : cVtx C e < C.P.n := Nat.mod_lt _ C.n_pos

theorem cm_vtx_tour {e : ℕ} (h6 : 6 ≤ e) (he : e ≤ 2 * C.m + 6) :
    (chainModel C).W.vtx e = C.P.vtx (cVtx C e) := by
  obtain ⟨i, rfl⟩ : ∃ i, e = i + 6 := ⟨e - 6, by omega⟩
  show (C.sideWalk C.sideBeta).vtx (i + 6) = _
  rw [C.sideWalk_vtx_tour _ (by omega)]
  unfold Chain.sideTour Chain.vertex Chain.edgeIdx cVtx
  rw [show i + 6 - 6 = i by omega]

/-- The points of the walk edges `0 … 5` of a chain model (the box and the slit down) are not
on the chain. -/
theorem box_pos_not_mem {e : ℕ} (he : e < 6) {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t < 1) :
    lerp ((chainModel C).W.vtx e) ((chainModel C).W.vtx ((e + 1) % (chainModel C).W.n)) t ∉
      C.set := by
  intro hmem
  have hb := C.set_subset_box hmem
  have htop := C.snd_le_top_of_mem_set hmem
  have hR := C.radius_pos
  have hTR := C.top_snd_lt_radius
  have hn : (chainModel C).W.n = 2 * C.m + 7 := chainModel_n C
  have hm := C.one_le
  rw [hn] at hmem hb htop
  simp only [Chain.mem_box_iff] at hb
  have hs : ((chainModel C).W.vtx 6) = C.top := C.sideWalk_vtx_six _
  interval_cases e
  · rw [Nat.mod_eq_of_lt (by omega)] at hb
    have e0 : (chainModel C).W.vtx 0 = C.slitTop := rfl
    have e1 : (chainModel C).W.vtx 1 = (-C.radius, C.radius) := rfl
    rw [e0, e1] at hb
    simp only [Chain.slitTop, Chazelle.Geometry.lerp_snd] at hb
    have : |C.radius + t * (C.radius - C.radius)| = C.radius := by
      rw [sub_self, mul_zero, add_zero, abs_of_pos hR]
    linarith [hb.2]
  · rw [Nat.mod_eq_of_lt (by omega)] at hb
    have e0 : (chainModel C).W.vtx 1 = (-C.radius, C.radius) := rfl
    have e1 : (chainModel C).W.vtx 2 = (-C.radius, -C.radius) := rfl
    rw [e0, e1] at hb
    simp only [Chazelle.Geometry.lerp_fst] at hb
    have : |-C.radius + t * (-C.radius - -C.radius)| = C.radius := by
      rw [sub_self, mul_zero, add_zero, abs_neg, abs_of_pos hR]
    linarith [hb.1]
  · rw [Nat.mod_eq_of_lt (by omega)] at hb
    have e0 : (chainModel C).W.vtx 2 = (-C.radius, -C.radius) := rfl
    have e1 : (chainModel C).W.vtx 3 = (C.radius, -C.radius) := rfl
    rw [e0, e1] at hb
    simp only [Chazelle.Geometry.lerp_snd] at hb
    have : |-C.radius + t * (-C.radius - -C.radius)| = C.radius := by
      rw [sub_self, mul_zero, add_zero, abs_neg, abs_of_pos hR]
    linarith [hb.2]
  · rw [Nat.mod_eq_of_lt (by omega)] at hb
    have e0 : (chainModel C).W.vtx 3 = (C.radius, -C.radius) := rfl
    have e1 : (chainModel C).W.vtx 4 = (C.radius, C.radius) := rfl
    rw [e0, e1] at hb
    simp only [Chazelle.Geometry.lerp_fst] at hb
    have : |C.radius + t * (C.radius - C.radius)| = C.radius := by
      rw [sub_self, mul_zero, add_zero, abs_of_pos hR]
    linarith [hb.1]
  · rw [Nat.mod_eq_of_lt (by omega)] at hb
    have e0 : (chainModel C).W.vtx 4 = (C.radius, C.radius) := rfl
    have e1 : (chainModel C).W.vtx 5 = C.slitTop := rfl
    rw [e0, e1] at hb
    simp only [Chain.slitTop, Chazelle.Geometry.lerp_snd] at hb
    have : |C.radius + t * (C.radius - C.radius)| = C.radius := by
      rw [sub_self, mul_zero, add_zero, abs_of_pos hR]
    linarith [hb.2]
  · rw [Nat.mod_eq_of_lt (by omega)] at htop
    have e0 : (chainModel C).W.vtx 5 = C.slitTop := rfl
    rw [e0, hs] at htop
    simp only [Chain.slitTop, Chazelle.Geometry.lerp_snd] at htop
    nlinarith

/-- **The boundary symbolic point of a hit**: a proper chain-model position (edge `< 2m + 7`)
whose point lies on the chain is a boundary symbolic point of `Q = C.P` with that point. -/
theorem hitSym_spec (hD : DistinctHeights C.P) {e h : ℕ}
    (hp : ProperPos (chainModel C) C.P C.P.n ⟨e, h⟩) (he : e < 2 * C.m + 7)
    (hmem : (chainModel C).pos C.P ⟨e, h⟩ ∈ C.set) :
    BSym C.P (hitSym C e h) ∧ (hitSym C e h).eval C.P = (chainModel C).pos C.P ⟨e, h⟩ := by
  have hn : (chainModel C).W.n = 2 * C.m + 7 := chainModel_n C
  have hm := C.one_le
  have hnP := C.add_one_le
  have hpar0 := hp.1
  have hpar1 := hp.2.1
  unfold hitSym
  by_cases hbox : e < 6
  · exfalso
    exact box_pos_not_mem C hbox hpar0 hpar1 hmem
  by_cases hslit : 2 * C.m + 6 ≤ e
  · -- the slit up from the top: the point is the top
    have he' : e = 2 * C.m + 6 := by omega
    simp only [hbox, hslit, or_true, ↓reduceIte]
    refine ⟨Nat.mod_lt _ C.n_pos, ?_⟩
    have hwa : (chainModel C).wa e = C.top := by
      unfold Model.wa
      rw [he', cm_vtx_tour C (by omega) le_rfl]
      unfold cVtx
      rw [show 2 * C.m + 6 - 6 = 2 * C.m by omega, C.sideIdx_two_m]; rfl
    have hwb : (chainModel C).wb e = C.slitTop := by
      unfold Model.wb; rw [hn, he', show 2 * C.m + 6 + 1 = 2 * C.m + 7 by ring, Nat.mod_self]; rfl
    have htop := C.snd_le_top_of_mem_set hmem
    unfold Model.pos at htop ⊢
    rw [hwa, hwb] at htop ⊢
    simp only [Chain.slitTop, Chazelle.Geometry.lerp_snd] at htop
    have hTR := C.top_snd_lt_radius
    have ht : (chainModel C).param C.P ⟨e, h⟩ = 0 := by nlinarith
    rw [ht, lerp_zero]; rfl
  simp only [hbox, hslit, or_self, ↓reduceIte]
  -- a walk edge of the double boundary
  have hwa : (chainModel C).wa e = C.P.vtx (cVtx C e) := cm_vtx_tour C (by omega) (by omega)
  have hwb : (chainModel C).wb e = C.P.vtx (cVtx C (e + 1)) := by
    unfold Model.wb; rw [hn, Nat.mod_eq_of_lt (by omega)]
    exact cm_vtx_tour C (by omega) (by omega)
  -- the two ends are consecutive vertices of the chain
  have hstep := C.sideTour_step C.sideBeta (e - 6)
  have hk1 := C.sideIdx_le C.sideBeta (e - 6)
  have hk2 := C.sideIdx_le C.sideBeta (e - 6 + 1)
  have e7 : e + 1 - 6 = e - 6 + 1 := by omega
  have hcons : HostEdgeOK C.P.n (.vtx (cVtx C e)) (.vtx (cVtx C (e + 1))) := by
    simp only [HostEdgeOK, cVtx, e7]
    rcases hstep with h1 | h1
    · left; rw [h1, ← Nat.add_assoc, Nat.add_mod]; simp
    · right; rw [← h1, ← Nat.add_assoc, Nat.add_mod (C.s + _)]; simp
  have hne : cVtx C e ≠ cVtx C (e + 1) := by
    unfold cVtx
    rw [e7]
    intro hc
    have := C.sideEdgeIdx_inj (j := C.sideIdx C.sideBeta (e - 6))
      (k := C.sideIdx C.sideBeta (e - 6 + 1)) hk1 hk2 hc
    rcases hstep with h1 | h1 <;> omega
  have hnh : ((chainModel C).wa e).2 ≠ ((chainModel C).wb e).2 := by
    rw [hwa, hwb]; exact hD _ _ (cVtx_lt C e) (cVtx_lt C (e + 1)) hne
  by_cases hv : h = 0 ∨ h - 1 = cVtx C e
  · simp only [hv, ↓reduceIte]
    refine ⟨cVtx_lt C e, ?_⟩
    have ht : (chainModel C).param C.P ⟨e, h⟩ = 0 := by
      by_cases hz : h = 0
      · subst hz; rfl
      · have h0 : h - 1 = cVtx C e := hv.resolve_left hz
        obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
        unfold Model.param
        simp only
        rw [ite_eq_right hnh, hwa]
        simp only [Nat.add_sub_cancel] at h0
        rw [h0, sub_self, zero_div]
    show C.P.vtx (cVtx C e) = lerp _ _ _
    rw [ht, lerp_zero, hwa]
  · simp only [hv, ↓reduceIte]
    push Not at hv
    obtain ⟨h0, hne'⟩ := hv
    obtain ⟨h', rfl⟩ : ∃ h', h = h' + 1 := ⟨h - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hne' ⊢
    have hh' : h' < C.P.n := by have := hp.2.2; simp only at this; omega
    have hpos := ShootCut.pos_eq_onEdge (chainModel C) hD (by omega) (p := e) (h := h')
      (sp₁ := .vtx (cVtx C e)) (sp₂ := .vtx (cVtx C (e + 1))) hwa hwb (cVtx_lt C e)
      (cVtx_lt C (e + 1)) hcons hnh
    refine ⟨?_, hpos.symm⟩
    -- the parameter is in `(0, 1)`: the height lies strictly between the ends
    have hpar : (chainModel C).param C.P ⟨e, h' + 1⟩ =
        ((C.P.vtx h').2 - (C.P.vtx (cVtx C e)).2) /
          ((C.P.vtx (cVtx C (e + 1))).2 - (C.P.vtx (cVtx C e)).2) := by
      unfold Model.param; simp only; rw [ite_eq_right hnh, hwa, hwb]
    have hpos0 : 0 < (chainModel C).param C.P ⟨e, h' + 1⟩ := by
      rcases hpar0.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        rw [hpar] at heq
        have hden : (C.P.vtx (cVtx C (e + 1))).2 - (C.P.vtx (cVtx C e)).2 ≠ 0 := by
          rw [hwa, hwb] at hnh; exact sub_ne_zero.2 (Ne.symm hnh)
        have := hD _ _ hh' (cVtx_lt C e) hne'
        rw [eq_comm, div_eq_zero_iff] at heq
        rcases heq with heq | heq
        · exact this (by linarith)
        · exact hden heq
    have hbt : ((C.P.vtx (cVtx C e)).2 < (C.P.vtx h').2 ∧
        (C.P.vtx h').2 < (C.P.vtx (cVtx C (e + 1))).2) ∨
        ((C.P.vtx (cVtx C (e + 1))).2 < (C.P.vtx h').2 ∧
          (C.P.vtx h').2 < (C.P.vtx (cVtx C e)).2) := by
      rw [hpar] at hpos0 hpar1
      set a := (C.P.vtx (cVtx C e)).2
      set b := (C.P.vtx (cVtx C (e + 1))).2
      set y := (C.P.vtx h').2
      rcases lt_or_gt_of_ne (show b - a ≠ 0 from by
          rw [hwa, hwb] at hnh; exact sub_ne_zero.2 (Ne.symm hnh)) with hd | hd
      · right
        have h1 := (div_pos_iff.1 hpos0)
        rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · linarith
        · rw [div_lt_one_of_neg hd] at hpar1
          constructor <;> linarith
      · left
        have h1 := (div_pos_iff.1 hpos0)
        rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [div_lt_one hd] at hpar1
          constructor <;> linarith
        · linarith
    -- the edge of `Q` carrying the walk edge
    simp only [ShootCut.edgeOf]
    split_ifs with hcase
    · refine ⟨cVtx_lt C e, hh', ?_⟩
      rw [← hcase]; exact hbt
    · refine ⟨cVtx_lt C (e + 1), hh', ?_⟩
      have hc2 : cVtx C e = (cVtx C (e + 1) + 1) % C.P.n := by
        simp only [HostEdgeOK] at hcons
        exact hcons.resolve_left hcase
      rw [← hc2]
      exact hbt.symm

end chain

/-! ## Inner points -/

/-- **Points within the coordinate bound are inner points of a chain model** (the box band). -/
theorem innerPt_chain (C : Chain) {z : Point} (h1 : |z.1| ≤ Jordan.coordBound C.P)
    (h2 : |z.2| ≤ Jordan.coordBound C.P) : (chainModel C).InnerPt z := by
  have hR := C.coordBound_lt_radius
  have hn : (chainModel C).W.n = 2 * C.m + 7 := chainModel_n C
  have hm := C.one_le
  have v1 : (chainModel C).W.vtx 1 = (-C.radius, C.radius) := rfl
  have v2 : (chainModel C).W.vtx 2 = (-C.radius, -C.radius) := rfl
  have v3 : (chainModel C).W.vtx 3 = (C.radius, -C.radius) := rfl
  rw [abs_le] at h1 h2
  refine ⟨⟨2, 1, by omega, by omega, ?_, ?_⟩, ⟨1, 3, by omega, by omega, ?_, ?_⟩⟩
  · rw [v2]; simp only; linarith
  · rw [v1]; simp only; linarith
  · rw [v1]; simp only; linarith
  · rw [v3]; simp only; linarith

/-- **Inner points of the interior model lie within the coordinate bound of `Q`.** -/
theorem innerPt_interior_bound {z : Point} (h : (interiorModel Q).InnerPt z) :
    |z.1| ≤ Jordan.coordBound Q ∧ |z.2| ≤ Jordan.coordBound Q := by
  obtain ⟨⟨p, q, hp, hq, hp1, hq1⟩, ⟨p', q', hp', hq', hp1', hq1'⟩⟩ := h
  rw [mi_n] at hp hq hp' hq'
  have hv : ∀ r, r < Q.n → ((interiorModel Q).W.vtx r) = Q.vtx (iv Q r) := fun r hr => iw_vtx hr
  rw [hv p hp] at hp1
  rw [hv q hq] at hq1
  rw [hv p' hp'] at hp1'
  rw [hv q' hq'] at hq1'
  have a1 := abs_le.1 (Jordan.abs_snd_vtx_le_coordBound Q (iv_lt hp))
  have a2 := abs_le.1 (Jordan.abs_snd_vtx_le_coordBound Q (iv_lt hq))
  have a3 := abs_le.1 (Jordan.abs_fst_vtx_le_coordBound Q (iv_lt hp'))
  have a4 := abs_le.1 (Jordan.abs_fst_vtx_le_coordBound Q (iv_lt hq'))
  refine ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩

end

end IOrc

end Chazelle.Core
