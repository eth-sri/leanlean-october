module

public import Chazelle.Core.OutputGeom
public import Chazelle.Rwx
public import Chazelle.RewriteTactics
public import Chazelle.SimpTactics
public import Chazelle.MiscTactics

/-!
# WP-N, part 2: the interior walk and the side edges of a trapezoid

The walk of the interior model is `interiorWalk Q`: `Q` itself when its interior is on the left
of its edges, the reversed polygon otherwise (`revOf Q = true`).  Index arithmetic:

* `wv b n k`: the vertex of `Q` at walk vertex `k` (`walk_vtx`);
* `inp b n p`: the edge of `Q` carried by walk edge `p` (an involution, `inp_inp`);
* `nxt n p = (p + 1) % n`.

`walk_edge`: walk edge `p` runs from `Q.vtx (inp p)` to `Q.vtx (nxt (inp p))`, or backwards when
the walk is reversed.  Since the interior is on the left of the walk, the walk runs **down the
left side edge** of every trapezoid and **up the right side edge** (`walk_left`, `walk_right`).
-/

namespace Chazelle.Core

namespace OutWalk

open Set Filter Topology Metric
open Chazelle.Visibility
open Chazelle.Mountain (TrapData LeftInside orient)
open Chazelle.Jordan (simple_vtx_inj succIdx_lt)
open Chazelle.Geometry (lerp lerp_fst lerp_snd point_ext point_ext_iff)
open Chazelle.Chain (sidePt)

@[expose] public section

variable {Q : Polygon}

/-! ## Index arithmetic -/

/-- The vertex of `Q` at walk vertex `k` (`b`: the walk is reversed). -/
def wv (b : Bool) (n k : ℕ) : ℕ := if b then n - 1 - k else k

/-- The successor index `(p + 1) % n` (for `p < n`). -/
def nxt (n p : ℕ) : ℕ := if p + 1 < n then p + 1 else 0

/-- The edge of `Q` carried by walk edge `p`. -/
def inp (b : Bool) (n p : ℕ) : ℕ := if b then (if p + 1 < n then n - 2 - p else n - 1) else p

/-- `nxt` is the successor modulo `n`. -/
theorem nxt_eq {n p : ℕ} (hp : p < n) : nxt n p = (p + 1) % n := by
  unfold nxt
  split_ifs with h
  · rw [Nat.mod_eq_of_lt h]
  · rw [show p + 1 = n by omega, Nat.mod_self]

/-- `nxt` stays below `n`. -/
theorem nxt_lt {n p : ℕ} (hp : p < n) : nxt n p < n := by unfold nxt; splao

/-- `inp` stays below `n`. -/
theorem inp_lt {b : Bool} {n p : ℕ} (hp : p < n) : inp b n p < n := by
  unfold inp; splao

/-- `wv` stays below `n`. -/
theorem wv_lt {b : Bool} {n k : ℕ} (hk : k < n) : wv b n k < n := by
  unfold wv; splao

/-- `inp` is an involution below `n`. -/
theorem inp_inp {b : Bool} {n p : ℕ} (hp : p < n) : inp b n (inp b n p) = p := by
  unfold inp; splao

/-- `wv` is an involution below `n`. -/
theorem wv_wv {b : Bool} {n k : ℕ} (hk : k < n) : wv b n (wv b n k) = k := by
  unfold wv; splao

/-- The ends of a walk edge in terms of the carried edge. -/
theorem wv_inp {b : Bool} {n p : ℕ} (hp : p < n) :
    (b = false ∧ wv b n p = inp b n p ∧ wv b n (nxt n p) = nxt n (inp b n p)) ∨
      (b = true ∧ wv b n p = nxt n (inp b n p) ∧ wv b n (nxt n p) = inp b n p) := by
  cases b
  · left; simp [wv, inp]
  · right
    refine ⟨rfl, ?_, ?_⟩ <;> simp only [wv, inp, nxt] <;>
      split_ifs <;> omega

/-! ## The walk -/

open Classical in
/-- Whether the interior walk of `Q` is the reversed polygon. -/
noncomputable def revOf (Q : Polygon) : Bool := decide (¬ LeftInside Q)

/-- The interior walk has `n` vertices. -/
theorem walk_n (Q : Polygon) : (interiorWalk Q).n = Q.n := by
  classical
  unfold interiorWalk
  split_ifs
  · rfl
  · exact FactsInterior.rev_n Q

/-- The walk vertices are vertices of `Q`. -/
theorem walk_vtx (Q : Polygon) {k : ℕ} (hk : k < Q.n) :
    (interiorWalk Q).vtx k = Q.vtx (wv (revOf Q) Q.n k) := by
  classical
  by_cases h : LeftInside Q
  · have e1 : interiorWalk Q = Q := by unfold interiorWalk; simp [h]
    have e2 : revOf Q = false := by unfold revOf; simp [h]
    rwr [e1, e2]
  · have e1 : interiorWalk Q = ⟨Q.vertices.reverse⟩ := by unfold interiorWalk; simp [h]
    have e2 : revOf Q = true := by unfold revOf; simp [h]
    rw [e1, e2]
    exact FactsInterior.rev_vtx Q k hk

/-- The walk successor. -/
theorem walk_succ (Q : Polygon) {p : ℕ} (hp : p < Q.n) :
    (interiorWalk Q).vtx ((p + 1) % (interiorWalk Q).n) = Q.vtx (wv (revOf Q) Q.n (nxt Q.n p)) := by
  rw [walk_n, ← nxt_eq hp, walk_vtx Q (nxt_lt hp)]

/-! ## The direction of a walk edge next to an interior point -/

/-- If the points just right of a point `z` inside walk edge `p` are interior, the walk edge
goes down (interior on the left). -/
theorem walk_down {W : Polygon} (hW : W.Simple) (hL : orient W = 1) {p : ℕ} (hp : p < W.n)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hint : ∀ δ, 0 < δ → δ < δ₀ →
      (((sidePt W p t).1 + δ, (sidePt W p t).2) : Point) ∈ W.filled \ W.boundary) :
    (W.vtx ((p + 1) % W.n)).2 < (W.vtx p).2 := by
  obtain ⟨r, hr, hloc⟩ := FactsInterior.edge_local hW hL hp ht
  set δ := min r δ₀ / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; exact half_pos (lt_min hr hδ₀)
  have hδr : δ < r := by rw [hδ]; linarith [min_le_left r δ₀]
  have hδδ : δ < δ₀ := by rw [hδ]; linarith [min_le_right r δ₀]
  set x : Point := ((sidePt W p t).1 + δ, (sidePt W p t).2) with hx
  have hxb : x ∈ ball (sidePt W p t) r := by
    rw [mem_ball, dist_comm, Prod.dist_eq]
    simp only [hx, Real.dist_eq, sub_self, abs_zero]
    rw [show (sidePt W p t).1 - ((sidePt W p t).1 + δ) = -δ by ring, abs_neg, abs_of_pos hδ0]
    exact max_lt hδr hr
  have hxi := hint δ hδ0 hδδ
  set a := W.vtx p with ha
  set b := W.vtx ((p + 1) % W.n) with hb
  have hdet : det a b x = -δ * (b.2 - a.2) := by
    sir only [det, hx, sidePt, lerp_fst, lerp_snd, ← ha, ← hb]
  rcases lt_trichotomy 0 (det a b x) with h | h | h
  · rwnl [hdet] at h
  · exact absurd ((hloc x hxb).2.2 h.symm) hxi.2
  · exact absurd hxi.1 ((hloc x hxb).2.1 h)

/-- If the points just left of a point `z` inside walk edge `p` are interior, the walk edge goes
up. -/
theorem walk_up {W : Polygon} (hW : W.Simple) (hL : orient W = 1) {p : ℕ} (hp : p < W.n)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hint : ∀ δ, 0 < δ → δ < δ₀ →
      (((sidePt W p t).1 - δ, (sidePt W p t).2) : Point) ∈ W.filled \ W.boundary) :
    (W.vtx p).2 < (W.vtx ((p + 1) % W.n)).2 := by
  obtain ⟨r, hr, hloc⟩ := FactsInterior.edge_local hW hL hp ht
  set δ := min r δ₀ / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; exact half_pos (lt_min hr hδ₀)
  have hδr : δ < r := by rw [hδ]; linarith [min_le_left r δ₀]
  have hδδ : δ < δ₀ := by rw [hδ]; linarith [min_le_right r δ₀]
  set x : Point := ((sidePt W p t).1 - δ, (sidePt W p t).2) with hx
  have hxb : x ∈ ball (sidePt W p t) r := by
    rw [mem_ball, dist_comm, Prod.dist_eq]
    simp only [hx, Real.dist_eq, sub_self, abs_zero]
    rw [show (sidePt W p t).1 - ((sidePt W p t).1 - δ) = δ by ring, abs_of_pos hδ0]
    exact max_lt hδr hr
  have hxi := hint δ hδ0 hδδ
  set a := W.vtx p with ha
  set b := W.vtx ((p + 1) % W.n) with hb
  have hdet : det a b x = δ * (b.2 - a.2) := by
    sir only [det, hx, sidePt, lerp_fst, lerp_snd, ← ha, ← hb]
  rcases lt_trichotomy 0 (det a b x) with h | h | h
  · rwnl [hdet] at h
  · exact absurd ((hloc x hxb).2.2 h.symm) hxi.2
  · exact absurd hxi.1 ((hloc x hxb).2.1 h)

/-! ## The walk along the side edges of a trapezoid -/

/-- A point of the open left side at a middle height, as a point of the open edge `i`. -/
theorem left_mid (hQ : Q.Simple) (D : TrapData Q) :
    ∃ t ∈ Ioo (0 : ℝ) 1, lerp (Q.vtx D.i) (Q.vtx ((D.i + 1) % Q.n)) t =
      ((edgeX Q D.i ((D.y₁ + D.y₂) / 2), (D.y₁ + D.y₂) / 2) : Point) := by
  have h12 := D.isTrap.bot_lt.trans D.isTrap.lt_top
  set ym := (D.y₁ + D.y₂) / 2 with hym
  have hy1 : D.y₁ < ym := by rwli [hym]
  have hy2 : ym < D.y₂ := by rwli [hym]
  have hmem : ((edgeX Q D.i ym, ym) : Point) ∈ Q.edge D.i :=
    D.isTrap.mem_edgeL hy1.le hy2.le rfl
  obtain ⟨t, ht0, ht1, hzt⟩ := hmem
  have hlt := D.isTrap.edgeX_lt hQ D.free hy1 hy2
  have hnv : ∀ k, k < Q.n → Q.vtx k ≠ ((edgeX Q D.i ym, ym) : Point) := by
    intro k hk hkz
    have e1 : (Q.vtx k).1 = edgeX Q D.i ym := by rw [hkz]
    have e2 : (Q.vtx k).2 = ym := by rw [hkz]
    exact D.isTrap.no_vertex k hk (by rwx [e2]) (by rwx [e2])
      (by rw [e1, e2]) (by rw [e1, e2]; exact hlt.le)
  refine ⟨t, ⟨?_, ?_⟩, hzt.symm⟩
  · rcases ht0.lt_or_eq with h | h
    · exact h
    · exfalso; apply hnv D.i D.isTrap.hi
      rw [hzt, ← h]; exact (Geometry.lerp_zero _ _).symm
  · rcases ht1.lt_or_eq with h | h
    · exact h
    · exfalso; apply hnv _ (succIdx_lt Q D.isTrap.hi)
      rw [hzt, h]; exact (Geometry.lerp_one _ _).symm

/-- A point of the open right side at a middle height, as a point of the open edge `j`. -/
theorem right_mid (hQ : Q.Simple) (D : TrapData Q) :
    ∃ t ∈ Ioo (0 : ℝ) 1, lerp (Q.vtx D.j) (Q.vtx ((D.j + 1) % Q.n)) t =
      ((edgeX Q D.j ((D.y₁ + D.y₂) / 2), (D.y₁ + D.y₂) / 2) : Point) := by
  have h12 := D.isTrap.bot_lt.trans D.isTrap.lt_top
  set ym := (D.y₁ + D.y₂) / 2 with hym
  have hy1 : D.y₁ < ym := by rwli [hym]
  have hy2 : ym < D.y₂ := by rwli [hym]
  have hmem : ((edgeX Q D.j ym, ym) : Point) ∈ Q.edge D.j :=
    D.isTrap.mem_edgeR hy1.le hy2.le rfl
  obtain ⟨t, ht0, ht1, hzt⟩ := hmem
  have hlt := D.isTrap.edgeX_lt hQ D.free hy1 hy2
  have hnv : ∀ k, k < Q.n → Q.vtx k ≠ ((edgeX Q D.j ym, ym) : Point) := by
    intro k hk hkz
    have e1 : (Q.vtx k).1 = edgeX Q D.j ym := by rw [hkz]
    have e2 : (Q.vtx k).2 = ym := by rw [hkz]
    exact D.isTrap.no_vertex k hk (by rwx [e2]) (by rwx [e2])
      (by rw [e1, e2]; exact hlt.le) (by rw [e1, e2])
  refine ⟨t, ⟨?_, ?_⟩, hzt.symm⟩
  · rcases ht0.lt_or_eq with h | h
    · exact h
    · exfalso; apply hnv D.j D.isTrap.hj
      rw [hzt, ← h]; exact (Geometry.lerp_zero _ _).symm
  · rcases ht1.lt_or_eq with h | h
    · exact h
    · exfalso; apply hnv _ (succIdx_lt Q D.isTrap.hj)
      rw [hzt, h]; exact (Geometry.lerp_one _ _).symm

/-- The walk point of the open part of an edge of `Q`. -/
theorem walk_pt (_hQ : Q.Simple) {e : ℕ} (he : e < Q.n) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ t' ∈ Ioo (0 : ℝ) 1, sidePt (interiorWalk Q) (inp (revOf Q) Q.n e) t' =
      lerp (Q.vtx e) (Q.vtx ((e + 1) % Q.n)) t := by
  have hp := inp_lt (b := revOf Q) he
  have hpp : inp (revOf Q) Q.n (inp (revOf Q) Q.n e) = e := inp_inp he
  unfold sidePt
  rw [walk_vtx Q hp, walk_succ Q hp, ← nxt_eq he]
  rcases wv_inp (b := revOf Q) hp with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
  · rw [h1, h2, hpp]; exact ⟨t, ht, rfl⟩
  · rw [h1, h2, hpp, Geometry.lerp_symm]
    exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩

/-- **The walk runs down the left side edge**: walk edge `inp i` starts at the upper end of the
left side edge `i` of the trapezoid. -/
theorem walk_left (hQ : Q.Simple) (D : TrapData Q) :
    (Q.vtx (wv (revOf Q) Q.n (nxt Q.n (inp (revOf Q) Q.n D.i)))).2 <
      (Q.vtx (wv (revOf Q) Q.n (inp (revOf Q) Q.n D.i))).2 := by
  obtain ⟨hWs, hWb, hWf, hWo⟩ := FactsInterior.interiorWalk_spec hQ
  have hi := D.isTrap.hi
  have hp := inp_lt (b := revOf Q) hi
  obtain ⟨t, ht, hzt⟩ := left_mid hQ D
  obtain ⟨t', ht', hz'⟩ := walk_pt hQ hi ht
  have hpW : inp (revOf Q) Q.n D.i < (interiorWalk Q).n := by rwx [walk_n]
  have h12 := D.isTrap.bot_lt.trans D.isTrap.lt_top
  have hy1 : D.y₁ < (D.y₁ + D.y₂) / 2 := by linarith
  have hy2 : (D.y₁ + D.y₂) / 2 < D.y₂ := by linarith
  have hlt := D.isTrap.edgeX_lt hQ D.free hy1 hy2
  have := walk_down hWs hWo hpW ht' (sub_pos.2 hlt) (fun δ hδ hδ' => by
    rw [hWf, hWb, hz', hzt]
    exact D.region_subset_interior hQ ⟨hy1, hy2, by sil only, by sil only⟩)
  rwa [walk_succ Q hp, walk_vtx Q hp] at this

/-- **The walk runs up the right side edge**: walk edge `inp j` ends at the upper end of the
right side edge `j` of the trapezoid. -/
theorem walk_right (hQ : Q.Simple) (D : TrapData Q) :
    (Q.vtx (wv (revOf Q) Q.n (inp (revOf Q) Q.n D.j))).2 <
      (Q.vtx (wv (revOf Q) Q.n (nxt Q.n (inp (revOf Q) Q.n D.j)))).2 := by
  obtain ⟨hWs, hWb, hWf, hWo⟩ := FactsInterior.interiorWalk_spec hQ
  have hj := D.isTrap.hj
  have hp := inp_lt (b := revOf Q) hj
  obtain ⟨t, ht, hzt⟩ := right_mid hQ D
  obtain ⟨t', ht', hz'⟩ := walk_pt hQ hj ht
  have hpW : inp (revOf Q) Q.n D.j < (interiorWalk Q).n := by rwx [walk_n]
  have h12 := D.isTrap.bot_lt.trans D.isTrap.lt_top
  have hy1 : D.y₁ < (D.y₁ + D.y₂) / 2 := by linarith
  have hy2 : (D.y₁ + D.y₂) / 2 < D.y₂ := by linarith
  have hlt := D.isTrap.edgeX_lt hQ D.free hy1 hy2
  have := walk_up hWs hWo hpW ht' (sub_pos.2 hlt) (fun δ hδ hδ' => by
    rw [hWf, hWb, hz', hzt]
    exact D.region_subset_interior hQ ⟨hy1, hy2, by sil only, by sil only⟩)
  rwa [walk_succ Q hp, walk_vtx Q hp] at this

/-- The two walk ends of the walk edge carrying edge `e`. -/
theorem walk_ends {b : Bool} {n e : ℕ} (he : e < n) :
    (wv b n (inp b n e) = e ∧ wv b n (nxt n (inp b n e)) = nxt n e) ∨
      (wv b n (inp b n e) = nxt n e ∧ wv b n (nxt n (inp b n e)) = e) := by
  have hp := inp_lt (b := b) he
  rcases wv_inp (b := b) hp with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
  · left; rw [h1, h2, inp_inp he]; exact ⟨rfl, rfl⟩
  · right; rw [h1, h2, inp_inp he]; exact ⟨rfl, rfl⟩

/-- The upper end of the left side edge is the start of its walk edge. -/
theorem walk_left_upper (hQ : Q.Simple) (D : TrapData Q) {v : ℕ}
    (hv : (v = D.i ∧ (Q.vtx ((D.i + 1) % Q.n)).2 < (Q.vtx v).2) ∨
      (v = (D.i + 1) % Q.n ∧ (Q.vtx D.i).2 < (Q.vtx v).2)) :
    wv (revOf Q) Q.n (inp (revOf Q) Q.n D.i) = v := by
  have hw := walk_left hQ D
  rw [← nxt_eq D.isTrap.hi] at hv
  rcases walk_ends (b := revOf Q) D.isTrap.hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hw <;>
    rw [h1] <;> rcases hv with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · rfl
  · exact absurd (h.trans hw) (lt_irrefl _)
  · exact absurd (h.trans hw) (lt_irrefl _)
  · rfl

/-- The lower end of the left side edge is the end of its walk edge. -/
theorem walk_left_lower (hQ : Q.Simple) (D : TrapData Q) {v : ℕ}
    (hv : (v = D.i ∧ (Q.vtx v).2 < (Q.vtx ((D.i + 1) % Q.n)).2) ∨
      (v = (D.i + 1) % Q.n ∧ (Q.vtx v).2 < (Q.vtx D.i).2)) :
    wv (revOf Q) Q.n (nxt Q.n (inp (revOf Q) Q.n D.i)) = v := by
  have hw := walk_left hQ D
  rw [← nxt_eq D.isTrap.hi] at hv
  rcases walk_ends (b := revOf Q) D.isTrap.hi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hw <;>
    rw [h2] <;> rcases hv with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact absurd (h.trans hw) (lt_irrefl _)
  · rfl
  · rfl
  · exact absurd (h.trans hw) (lt_irrefl _)

/-- The lower end of the right side edge is the start of its walk edge. -/
theorem walk_right_lower (hQ : Q.Simple) (D : TrapData Q) {v : ℕ}
    (hv : (v = D.j ∧ (Q.vtx v).2 < (Q.vtx ((D.j + 1) % Q.n)).2) ∨
      (v = (D.j + 1) % Q.n ∧ (Q.vtx v).2 < (Q.vtx D.j).2)) :
    wv (revOf Q) Q.n (inp (revOf Q) Q.n D.j) = v := by
  have hw := walk_right hQ D
  rw [← nxt_eq D.isTrap.hj] at hv
  rcases walk_ends (b := revOf Q) D.isTrap.hj with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hw <;>
    rw [h1] <;> rcases hv with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · rfl
  · exact absurd (hw.trans h) (lt_irrefl _)
  · exact absurd (hw.trans h) (lt_irrefl _)
  · rfl

/-- The upper end of the right side edge is the end of its walk edge. -/
theorem walk_right_upper (hQ : Q.Simple) (D : TrapData Q) {v : ℕ}
    (hv : (v = D.j ∧ (Q.vtx ((D.j + 1) % Q.n)).2 < (Q.vtx v).2) ∨
      (v = (D.j + 1) % Q.n ∧ (Q.vtx D.j).2 < (Q.vtx v).2)) :
    wv (revOf Q) Q.n (nxt Q.n (inp (revOf Q) Q.n D.j)) = v := by
  have hw := walk_right hQ D
  rw [← nxt_eq D.isTrap.hj] at hv
  rcases walk_ends (b := revOf Q) D.isTrap.hj with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hw <;>
    rw [h2] <;> rcases hv with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact absurd (hw.trans h) (lt_irrefl _)
  · rfl
  · rfl
  · exact absurd (hw.trans h) (lt_irrefl _)

end

end OutWalk

end Chazelle.Core
