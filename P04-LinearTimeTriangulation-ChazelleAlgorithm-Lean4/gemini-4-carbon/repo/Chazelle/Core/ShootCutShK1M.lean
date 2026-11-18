module

public import Chazelle.Core.ShootCutShK0

/-!
# WP-G, part 49: the hit of a kind-1 piece as a walk position

The Lemma 3.6 query answers a kind-1 piece (a grade chain `[x₀, x₀ + w]` of `Q`, traversed by the
walk edges `p₀ … p₀ + w - 1` upward, `dir = 1`, or downward) with the edge `e'` of `Q` carrying the
first hit `X`, at the height of the vertex `h` of `Q`.  `k1Out` turns this into a walk position
of `X` (`k1_hit`): inside the block, the walk edge of `e'` (or the next walk vertex when `X` is the
far end of the edge); outside the block, `X` is an end of the chain (a simple polygon meets a
non-incident edge only at shared vertices), the walk vertex `p₀` or `p₀ + w`.
-/

namespace Chazelle.Core

@[expose] public section

open Set
open Chazelle.Geometry (lerp lerp_fst lerp_snd)
open Chazelle.Visibility (xAt xAt_lerp edgeX)

namespace ShootCut

/-- **The walk position of the hit** of a kind-1 piece. -/
def k1Out (p₀ x0 w dir e' h : ℕ) : WPos :=
  if x0 ≤ e' ∧ e' < x0 + w then
    (if dir = 1 then (if h = e' + 1 then ⟨p₀ + (e' - x0) + 1, 0⟩ else ⟨p₀ + (e' - x0), h + 1⟩)
     else (if h = e' then ⟨p₀ + (w - 1 - (e' - x0)) + 1, 0⟩
       else ⟨p₀ + (w - 1 - (e' - x0)), h + 1⟩))
  else if dir = 1 then (if h = x0 then ⟨p₀, 0⟩ else ⟨p₀ + w, 0⟩)
  else (if h = x0 then ⟨p₀ + w, 0⟩ else ⟨p₀, 0⟩)

/-- A point of a non-horizontal segment is determined by its height. -/
theorem seg_pt {a b X : Point} (hab : a.2 ≠ b.2) (hX : X ∈ Chazelle.segment a b) :
    X = lerp a b ((X.2 - a.2) / (b.2 - a.2)) ∧ 0 ≤ (X.2 - a.2) / (b.2 - a.2) ∧
      (X.2 - a.2) / (b.2 - a.2) ≤ 1 := by
  obtain ⟨t, h0, h1, rfl⟩ := hX
  have hne : b.2 - a.2 ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have ht : (a.2 + t * (b.2 - a.2) - a.2) / (b.2 - a.2) = t := by field_simp; ring
  simp only
  rw [ht]
  exact ⟨rfl, h0, h1⟩

/-- **A point of a walk edge at the height of a vertex of `Q`** is the position with that height
code; its parameter is below `1` unless it is the end of the edge. -/
theorem walk_pos_at {M : Model} {Q : Polygon} {p h : ℕ} {X : Point}
    (hne : (M.wa p).2 ≠ (M.wb p).2) (hX : X ∈ Chazelle.segment (M.wa p) (M.wb p))
    (hXh : X.2 = (Q.vtx h).2) (hb : X.2 ≠ (M.wb p).2) :
    M.pos Q ⟨p, h + 1⟩ = X ∧ 0 ≤ M.param Q ⟨p, h + 1⟩ ∧ M.param Q ⟨p, h + 1⟩ < 1 := by
  obtain ⟨hXe, h0, h1⟩ := seg_pt hne hX
  have hpar : M.param Q ⟨p, h + 1⟩ = (X.2 - (M.wa p).2) / ((M.wb p).2 - (M.wa p).2) := by
    show (if (M.wa p).2 = (M.wb p).2 then 0 else _) = _
    rw [ite_eq_right hne, hXh]
  have hd : (M.wb p).2 - (M.wa p).2 ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  refine ⟨?_, by rw [hpar]; exact h0, ?_⟩
  · show lerp (M.wa p) (M.wb p) (M.param Q ⟨p, h + 1⟩) = X
    rw [hpar]; exact hXe.symm
  · rw [hpar]
    refine lt_of_le_of_ne h1 fun h => hb ?_
    rw [div_eq_one_iff_eq hd] at h
    linarith

/-- The abscissa of a point of an edge of `Q` at a given height. -/
theorem edge_x {Q : Polygon} {e h : ℕ} {X : Point} (hne : (Q.vtx e).2 ≠ (Q.vtx ((e + 1) % Q.n)).2)
    (hX : X ∈ Q.edge e) (hXh : X.2 = (Q.vtx h).2) : X.1 = ((SymPt.onEdge e h).eval Q).1 := by
  obtain ⟨hXe, -, -⟩ := seg_pt hne hX
  show X.1 = edgeX Q e (Q.vtx h).2
  unfold edgeX
  rw [← hXh]
  conv_lhs => rw [hXe]
  rw [← xAt_lerp hne, ← hXe]

/-- A point of a segment between two points of a box of radius `r` is in it. -/
theorem seg_abs_le {a b X : Point} {r : ℝ} (ha : |a.1| ≤ r) (hb : |b.1| ≤ r)
    (hX : X ∈ Chazelle.segment a b) : |X.1| ≤ r := by
  obtain ⟨t, h0, h1, rfl⟩ := hX
  simp only
  have h' : a.1 + t * (b.1 - a.1) = (1 - t) * a.1 + t * b.1 := by ring
  rw [h', abs_le]
  have := abs_le.1 ha
  have := abs_le.1 hb
  constructor <;> nlinarith

variable {C : Chain} {Q : Polygon}

/-- **The walk position of the hit of a kind-1 piece.** -/
theorem k1_hit (hD : DistinctHeights Q) (hS : Q.Simple) {p₀ x0 w dir : ℕ}
    (hblk : BlockWalk (chainModel C).W Q p₀ x0 w dir) (hw1 : 1 ≤ w) (hxw : x0 + w < Q.n)
    (hp6 : 6 ≤ p₀) (hp : p₀ + w ≤ 2 * C.m + 6) (hdir : dir = 1 ∨ dir = 0) {X : Point} {e' h : ℕ}
    (hXS : X ∈ (chainModel C).arcSet (p₀ : ℝ) ((p₀ + w : ℕ) : ℝ)) (hXe : X ∈ Q.edge e')
    (he' : e' < Q.n) (hh : h < Q.n) (hXh : X.2 = (Q.vtx h).2) :
    (k1Out p₀ x0 w dir e' h).edge < 2 * C.m + 7 ∧
      ProperPos (chainModel C) Q Q.n (k1Out p₀ x0 w dir e' h) ∧
      (chainModel C).pos Q (k1Out p₀ x0 w dir e' h) = X ∧
      X.1 = ((SymPt.onEdge e' h).eval Q).1 ∧ |X.1| < C.radius := by
  set M := chainModel C
  have hnW : M.W.n = 2 * C.m + 7 := chainModel_n C
  have hn2 : 2 ≤ Q.n := by omega
  -- the walk edge of `X`
  obtain ⟨d, hd, hXd⟩ := (arcSet_nat (M := M) (p₀ := p₀) hw1 (by omega) X).1 hXS
  -- abscissa and box
  have hx : X.1 = ((SymPt.onEdge e' h).eval Q).1 :=
    edge_x (SweepPrim.edge_heights_ne hD hn2 he') hXe hXh
  have hmemv : ∀ q, 6 ≤ q → q ≤ 2 * C.m + 6 → |(M.W.vtx q).1| ≤ Chazelle.Jordan.coordBound C.P := fun q h1 h2 => by
    obtain ⟨i, rfl⟩ : ∃ i, q = i + 6 := ⟨q - 6, by omega⟩
    rw [SweepPrim.walk_vtx_tour C (by omega)]
    exact (C.abs_le_coordBound_of_mem_set (C.vertex_mem_set (C.sideIdx_le _ _))).1
  have hbox : |X.1| < C.radius := lt_of_le_of_lt (seg_abs_le (hmemv _ (by omega) (by omega))
    (hmemv _ (by omega) (by omega)) hXd) C.coordBound_lt_radius
  have hpos0 : ∀ q, M.pos Q ⟨q, 0⟩ = M.W.vtx q := fun q => pos_box_vtx C Q q
  have wv : ∀ q, q + 1 < M.W.n → M.wb q = M.W.vtx (q + 1) := fun q hq => by
    unfold Model.wb; rw [Nat.mod_eq_of_lt hq]
  have edge_eq : ∀ k, k + 1 < Q.n → Q.edge k = Chazelle.segment (Q.vtx k) (Q.vtx (k + 1)) :=
    fun k hk => by unfold Polygon.edge; rw [Nat.mod_eq_of_lt hk]
  have hvinj : ∀ i j, i < Q.n → j < Q.n → (Q.vtx i).2 = (Q.vtx j).2 → i = j := fun i j hi hj he => by
    by_contra hne; exact hD i j hi hj hne he
  have atEnd : ∀ {a b : Point}, a.2 ≠ b.2 → X ∈ Chazelle.segment a b → X.2 = b.2 → X = b :=
    fun {a b} hne hX hy => by
      obtain ⟨hXe, -, -⟩ := seg_pt hne hX
      rw [hXe, hy, div_self (sub_ne_zero.2 (Ne.symm hne))]
      ext <;> simp [lerp]
  have hw' : ∀ i j, i < Q.n → j < Q.n → Q.vtx i = Q.vtx j → i = j := fun i j hi hj he =>
    Chazelle.Jordan.simple_vtx_inj hS hi hj he
  have hpp : ∀ q, ProperPos M Q Q.n ⟨q, 0⟩ := fun q => proper_vtx _ _ _ _
  suffices key : ∃ q : WPos, k1Out p₀ x0 w dir e' h = q ∧ q.edge < 2 * C.m + 7 ∧
      ProperPos M Q Q.n q ∧ M.pos Q q = X by
    obtain ⟨q, hq, a, b, c⟩ := key
    rw [hq]; exact ⟨a, b, c, hx, hbox⟩
  unfold k1Out
  by_cases hin : x0 ≤ e' ∧ e' < x0 + w
  · rw [ite_eq_left hin]
    obtain ⟨j, hj⟩ : ∃ j, e' = x0 + j := ⟨e' - x0, by omega⟩
    have hj' : e' - x0 = j := by omega
    rw [hj']
    have hjw : j < w := by omega
    have hEe := SweepPrim.edge_heights_ne hD hn2 he'
    rw [Nat.mod_eq_of_lt (show e' + 1 < Q.n by omega)] at hEe
    have hXe' : X ∈ Chazelle.segment (Q.vtx e') (Q.vtx (e' + 1)) := by
      rw [← edge_eq _ (by omega)]; exact hXe
    rcases hdir with rfl | rfl
    · rw [ite_eq_left rfl]
      have ha : M.W.vtx (p₀ + j) = Q.vtx e' := by
        have := hblk j (by omega); rw [ite_eq_left rfl] at this; rw [this, hj]
      have hb : M.W.vtx (p₀ + j + 1) = Q.vtx (e' + 1) := by
        have := hblk (j + 1) (by omega); rw [ite_eq_left rfl] at this
        rw [show p₀ + j + 1 = p₀ + (j + 1) by ring, this, hj]; ring_nf
      have hwa : M.wa (p₀ + j) = Q.vtx e' := ha
      have hwb : M.wb (p₀ + j) = Q.vtx (e' + 1) := by rw [wv _ (by omega), hb]
      by_cases hhe : h = e' + 1
      · rw [ite_eq_left hhe]
        refine ⟨_, rfl, by simp only; omega, hpp _, ?_⟩
        rw [hpos0, hb]
        exact (atEnd hEe hXe' (by rw [hXh, hhe])).symm
      · rw [ite_eq_right hhe]
        obtain ⟨hp, h0, h1⟩ := walk_pos_at (M := M) (Q := Q) (p := p₀ + j) (h := h)
          (by rw [hwa, hwb]; exact hEe) (by rw [hwa, hwb]; exact hXe') hXh
          (by rw [hwb, hXh]; intro he; exact hhe (hvinj _ _ hh (by omega) he))
        exact ⟨_, rfl, by simp only; omega, ⟨h0, h1, by show h + 1 ≤ Q.n; omega⟩, hp⟩
    · rw [ite_eq_right (by norm_num : ¬ (0 = 1))]
      set p := p₀ + (w - 1 - j)
      have ha : M.W.vtx p = Q.vtx (e' + 1) := by
        have := hblk (w - 1 - j) (by omega); rw [ite_eq_right (by norm_num : ¬ (0 = 1))] at this
        rw [this, hj]; congr 1; omega
      have hb : M.W.vtx (p + 1) = Q.vtx e' := by
        have := hblk (w - 1 - j + 1) (by omega)
        rw [ite_eq_right (by norm_num : ¬ (0 = 1))] at this
        rw [show p + 1 = p₀ + (w - 1 - j + 1) by simp only [p]; ring, this, hj]; congr 1; omega
      have hwa : M.wa p = Q.vtx (e' + 1) := ha
      have hwb : M.wb p = Q.vtx e' := by rw [wv _ (by omega), hb]
      have hXr : X ∈ Chazelle.segment (Q.vtx (e' + 1)) (Q.vtx e') := by
        rw [Chazelle.Geometry.segment_comm]; exact hXe'
      by_cases hhe : h = e'
      · rw [ite_eq_left hhe]
        refine ⟨_, rfl, by simp only; omega, hpp _, ?_⟩
        rw [hpos0, hb]
        exact (atEnd (Ne.symm hEe) hXr (by rw [hXh, hhe])).symm
      · rw [ite_eq_right hhe]
        obtain ⟨hp, h0, h1⟩ := walk_pos_at (M := M) (Q := Q) (p := p) (h := h)
          (by rw [hwa, hwb]; exact Ne.symm hEe) (by rw [hwa, hwb]; exact hXr) hXh
          (by rw [hwb, hXh]; intro he; exact hhe (hvinj _ _ hh he' he))
        exact ⟨_, rfl, by simp only; omega, ⟨h0, h1, by show h + 1 ≤ Q.n; omega⟩, hp⟩
  -- outside the block: `X` is an end of the chain
  rw [ite_eq_right hin]
  obtain ⟨k, hk1, hk2, hXk⟩ : ∃ k, x0 ≤ k ∧ k < x0 + w ∧ X ∈ Q.edge k := by
    rcases hdir with rfl | rfl
    · refine ⟨x0 + d, by omega, by omega, ?_⟩
      rw [edge_eq _ (by omega)]
      have ha := hblk d (by omega); rw [ite_eq_left rfl] at ha
      have hb := hblk (d + 1) (by omega); rw [ite_eq_left rfl] at hb
      rw [ha, show p₀ + d + 1 = p₀ + (d + 1) by ring, hb] at hXd
      rwa [show x0 + (d + 1) = x0 + d + 1 by ring] at hXd
    · refine ⟨x0 + w - d - 1, by omega, by omega, ?_⟩
      rw [edge_eq _ (by omega)]
      have ha := hblk d (by omega); rw [ite_eq_right (by norm_num : ¬ (0 = 1))] at ha
      have hb := hblk (d + 1) (by omega); rw [ite_eq_right (by norm_num : ¬ (0 = 1))] at hb
      rw [ha, show p₀ + d + 1 = p₀ + (d + 1) by ring, hb, Chazelle.Geometry.segment_comm] at hXd
      rwa [show x0 + w - (d + 1) = x0 + w - d - 1 by omega,
        show x0 + w - d = x0 + w - d - 1 + 1 by omega] at hXd
  have hke : k ≠ e' := fun h' => hin (by omega)
  have e1 := Chazelle.Jordan.simple_endpoint_of_mem_two hS (i := k) (j := e') (by omega) he' hke
    hXk hXe
  have e2 := Chazelle.Jordan.simple_endpoint_of_mem_two hS (i := e') (j := k) he' (by omega)
    (Ne.symm hke) hXe hXk
  rw [Nat.mod_eq_of_lt (show k + 1 < Q.n by omega)] at e1
  obtain ⟨v, hv1, hv2, hXv⟩ : ∃ v, x0 ≤ v ∧ v ≤ x0 + w ∧ X = Q.vtx v := by
    rcases e1 with e | e
    · exact ⟨k, by omega, by omega, e⟩
    · exact ⟨k + 1, by omega, by omega, e⟩
  have hhv : h = v := hvinj _ _ hh (by omega) (by rw [← hXh, hXv])
  have hvend : v = x0 ∨ v = x0 + w := by
    by_contra hc
    push Not at hc
    rcases e2 with e | e
    · have := hw' _ _ (by omega) he' (hXv.symm.trans e); exact hin (by omega)
    · rcases Nat.lt_or_ge (e' + 1) Q.n with hl | hl
      · rw [Nat.mod_eq_of_lt hl] at e
        have := hw' _ _ (by omega) hl (hXv.symm.trans e); exact hin (by omega)
      · rw [show e' + 1 = Q.n by omega, Nat.mod_self] at e
        have := hw' _ _ (by omega) (by omega) (hXv.symm.trans e); omega
  have hv0 : M.W.vtx p₀ = Q.vtx (if dir = 1 then x0 else x0 + w) := by
    have := hblk 0 (by omega); rw [Nat.add_zero] at this; rw [this]
    split_ifs <;> simp
  have hvw : M.W.vtx (p₀ + w) = Q.vtx (if dir = 1 then x0 + w else x0) := by
    have := hblk w le_rfl; rw [this]
    split_ifs <;> simp
  rcases hdir with rfl | rfl
  · rw [ite_eq_left rfl]
    rw [ite_eq_left rfl] at hv0 hvw
    by_cases hx0 : h = x0
    · rw [ite_eq_left hx0]
      exact ⟨_, rfl, by simp only; omega, hpp _, by rw [hpos0, hv0, hXv, ← hhv, hx0]⟩
    · rw [ite_eq_right hx0]
      have : v = x0 + w := by omega
      exact ⟨_, rfl, by simp only; omega, hpp _, by rw [hpos0, hvw, hXv, this]⟩
  · rw [ite_eq_right (by norm_num : ¬ (0 = 1))]
    rw [ite_eq_right (by norm_num : ¬ (0 = 1))] at hv0 hvw
    by_cases hx0 : h = x0
    · rw [ite_eq_left hx0]
      exact ⟨_, rfl, by simp only; omega, hpp _, by rw [hpos0, hvw, hXv, ← hhv, hx0]⟩
    · rw [ite_eq_right hx0]
      have : v = x0 + w := by omega
      exact ⟨_, rfl, by simp only; omega, hpp _, by rw [hpos0, hv0, hXv, this]⟩

end ShootCut

end

end Chazelle.Core
