module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.BruteFar

/-!
# WP-K: the chord list of the brute-force procedure

The list `bruteList C` of chord triples `(h, lp, rp)` that the brute-force procedure writes:
for every tour position `i ≤ 2m` (walk vertex `i + 6`) and direction `d` (`0` east, `1` west)
whose horizontal direction leaves the walk vertex into its left sector (`Emit`), the vertex chord
of `v_{k}`, `k = sideIdx i`, in that direction, with its vertex end at walk position
`(i + 6, h + 1)` and its far end at `farEdge` (a tour edge traversing the candidate chain edge
found by `scan`, or a side of the box).

Main results: `bruteList_ok : ChordTriplesOK (chainModel C) C.P (bruteList C)` and
`lset_bruteList : lset … (bruteList C) = C.chords` (the list is exactly the full map).
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (sideCcw sideCross sideDot sideLeft sideLeftOf sidePt SideAttach)
open Chazelle.Visibility (rayPt OpenEdgePt xAt hseg)

namespace Brute

variable {C : Chain}

/-! ## Tour indices of the chain edges -/

/-- The tour start `sideS sideBeta`. -/
noncomputable def tS (C : Chain) : ℕ := C.sideS C.sideBeta

/-- The tour position traversing chain edge `b` upward in the chain order (`v_b → v_{b+1}`). -/
def fwdIdx (m S b : ℕ) : ℕ := (b + 2 * m - S) % (2 * m)

/-- The tour position traversing chain edge `b` backward (`v_{b+1} → v_b`). -/
def bwdIdx (m S b : ℕ) : ℕ := (2 * m - 1 - b + 2 * m - S) % (2 * m)

theorem fwdIdx_spec {b : ℕ} (hb : b < C.m) :
    fwdIdx C.m (tS C) b < 2 * C.m ∧ C.sideIdx C.sideBeta (fwdIdx C.m (tS C) b) = b ∧
      C.sideIdx C.sideBeta (fwdIdx C.m (tS C) b + 1) = b + 1 := by
  have hm := C.two_m_pos
  have hS := C.sideS_lt C.sideBeta
  have hmod : (C.sideS C.sideBeta + fwdIdx C.m (tS C) b) % (2 * C.m) = b := by
    unfold fwdIdx tS
    rw [Nat.add_mod_mod, show C.sideS C.sideBeta + (b + 2 * C.m - C.sideS C.sideBeta) =
      b + 2 * C.m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  refine ⟨Nat.mod_lt _ hm, ?_, ?_⟩
  · rw [Chain.sideIdx_eq, hmod]; unfold Chain.sideE; rw [ite_eq_left (by omega)]
  · rw [Chain.sideIdx_succ, hmod]; unfold Chain.sideE; rw [ite_eq_left (by omega)]

theorem bwdIdx_spec {b : ℕ} (hb : b < C.m) :
    bwdIdx C.m (tS C) b < 2 * C.m ∧ C.sideIdx C.sideBeta (bwdIdx C.m (tS C) b) = b + 1 ∧
      C.sideIdx C.sideBeta (bwdIdx C.m (tS C) b + 1) = b := by
  have hm := C.two_m_pos
  have hS := C.sideS_lt C.sideBeta
  have hmod : (C.sideS C.sideBeta + bwdIdx C.m (tS C) b) % (2 * C.m) = 2 * C.m - 1 - b := by
    unfold bwdIdx tS
    rw [Nat.add_mod_mod, show C.sideS C.sideBeta + (2 * C.m - 1 - b + 2 * C.m - C.sideS C.sideBeta)
      = (2 * C.m - 1 - b) + 2 * C.m by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  refine ⟨Nat.mod_lt _ hm, ?_, ?_⟩
  · rw [Chain.sideIdx_eq, hmod]; unfold Chain.sideE; split_ifs <;> omega
  · rw [Chain.sideIdx_succ, hmod]; unfold Chain.sideE; split_ifs <;> omega

/-! ## The walk edges of the chain model -/

theorem wb_eq (p : ℕ) :
    (chainModel C).wb p = (chainModel C).W.vtx ((p + 1) % (chainModel C).W.n) := rfl

theorem cwa_tour {i : ℕ} (hi : i ≤ 2 * C.m) : (chainModel C).wa (i + 6) = vPt C i :=
  walk_vtx_tour hi

theorem cwb_tour {i : ℕ} (hi : i < 2 * C.m) : (chainModel C).wb (i + 6) = vPt C (i + 1) := by
  rw [wb_eq, walk_next hi.le]; unfold nextPt; rw [ite_eq_right (⋄)]; rfl

theorem param_hgt {x : WPos} {h : ℕ} (hx : x.hgt = h + 1)
    (hne : ((chainModel C).wa x.edge).2 ≠ ((chainModel C).wb x.edge).2) (Q : Polygon) :
    (chainModel C).param Q x = ((Q.vtx h).2 - ((chainModel C).wa x.edge).2) /
      (((chainModel C).wb x.edge).2 - ((chainModel C).wa x.edge).2) := by
  unfold Model.param; rw [hx]; simp only; Ξ ite_eq_right hne

theorem xAt_comm {u w : Point} (h : u.2 ≠ w.2) (y : ℝ) : xAt w u y = xAt u w y := by
  have h1 := sub_ne_zero.2 h.symm
  have h2 := sub_ne_zero.2 h
  unfold xAt; field_simp; ring

/-- **Attachment at a point inside a walk edge**: if the walk edge `p` straddles the height `y`
of `v_k` and has `v_k` on its left, and the far end of the chord of `v_k` is the point of the edge
at that height, then the position `(p, h + 1)` is that point and attaches the chord. -/
theorem attach_on_edge {p : ℕ} (hp : p < (chainModel C).W.n) {k : ℕ} {σ : ℝ}
    (hne : ((chainModel C).wa p).2 ≠ ((chainModel C).wb p).2)
    (hy1 : min ((chainModel C).wa p).2 ((chainModel C).wb p).2 < (C.vertex k).2)
    (hy2 : (C.vertex k).2 < max ((chainModel C).wa p).2 ((chainModel C).wb p).2)
    (hdet : 0 < det ((chainModel C).wa p) ((chainModel C).wb p) (C.vertex k))
    (hend : C.chordEnd k σ =
      (xAt ((chainModel C).wa p) ((chainModel C).wb p) (C.vertex k).2, (C.vertex k).2)) :
    (chainModel C).pos C.P ⟨p, C.edgeIdx k + 1⟩ = C.chordEnd k σ ∧
      SideAttach (chainModel C).W (C.chordSet k σ) p
        ((chainModel C).param C.P ⟨p, C.edgeIdx k + 1⟩) := by
  set u := (chainModel C).wa p with hu
  set w := (chainModel C).wb p with hw
  have hvk : C.P.vtx (C.edgeIdx k) = C.vertex k := rfl
  have hpar : (chainModel C).param C.P ⟨p, C.edgeIdx k + 1⟩ =
      ((C.vertex k).2 - u.2) / (w.2 - u.2) := by
    Ξ param_hgt (x := ⟨p, C.edgeIdx k + 1⟩) rfl hne, hvk
  have hd : w.2 - u.2 ≠ 0 := sub_ne_zero.2 hne.symm
  set t := ((C.vertex k).2 - u.2) / (w.2 - u.2) with ht
  have ht01 : 0 < t ∧ t < 1 := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [min_eq_left hlt.le] at hy1; rw [max_eq_right hlt.le] at hy2
      exact ⟨div_pos (⟡) (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩
    · rw [min_eq_right hgt.le] at hy1; rw [max_eq_left hgt.le] at hy2
      exact ⟨div_pos_of_neg_of_neg (⟡) (by linarith),
        (div_lt_one_of_neg (⟡)).2 (by linarith)⟩
  have hlerp : Geometry.lerp u w t = C.chordEnd k σ := by
    Ξ hend
    ext
    · simp only [Geometry.lerp_fst]; unfold xAt; rw [ht]; ring
    · simp only [Geometry.lerp_snd]; rw [ht]; field_simp; ring
  have hpos : (chainModel C).pos C.P ⟨p, C.edgeIdx k + 1⟩ = C.chordEnd k σ := by
    unfold Model.pos; rw [hpar]; exact hlerp
  refine ⟨hpos, ?_⟩
  Ξ hpar
  have hspt : sidePt (chainModel C).W p t = C.chordEnd k σ := hlerp
  have hl : sideLeft (chainModel C).W p t (C.vertex k) := by
    rw [Chain.sideLeft_edge (fun e => hne (congrArg Prod.snd e)) ⟨ht01.1, ht01.2⟩]; exact hdet
  have := Chain.sideAttach_of_left hp ht01.1.le ht01.2 hspt hl
  unfold Chain.chordSet
  Ξ Geometry.segment_comm
  exact this

/-! ## The far walk edge -/

/-- The walk edge carrying the far end of the chord of `v_k` in direction `σ`. -/
noncomputable def farEdge (C : Chain) (k : ℕ) (σ : ℝ) : ℕ := by
  classical
  exact match scan C k σ C.m with
    | some b => (if 0 < det (C.vertex b) (C.vertex (b + 1)) (C.vertex k) then fwdIdx C.m (tS C) b
        else bwdIdx C.m (tS C) b) + 6
    | none => if σ = 1 then 3 else 1

theorem det_zero_on_line {u w v : Point} (h : u.2 ≠ w.2) (hd : det u w v = 0) :
    v.1 = xAt u w v.2 := by
  have hne := sub_ne_zero.2 h.symm
  unfold det at hd
  unfold xAt
  field_simp
  linarith

/-- **The far end of every chord is attached at `farEdge`.** -/
theorem far_attach (hDH : DistinctHeights C.P) {k : ℕ} (hk : k ≤ C.m) {σ : ℝ}
    (hσ : σ = 1 ∨ σ = -1) (hf : C.DirFree k σ) :
    farEdge C k σ < (chainModel C).W.n ∧
    (chainModel C).pos C.P ⟨farEdge C k σ, C.edgeIdx k + 1⟩ = C.chordEnd k σ ∧
      SideAttach (chainModel C).W (C.chordSet k σ) (farEdge C k σ)
        ((chainModel C).param C.P ⟨farEdge C k σ, C.edgeIdx k + 1⟩) := by
  have hn := walk_n (C := C)
  have hbox := Chain.mem_box_iff.1 (C.set_subset_box (C.vertex_mem_set hk))
  have hR := C.radius_pos
  have ha1 := abs_lt.1 hbox.1
  have ha2 := abs_lt.1 hbox.2
  have hW : (chainModel C).W = C.sideWalk C.sideBeta := rfl
  obtain ⟨hsome, hnone⟩ := far_end hDH hk hσ hf
  rcases hsc : scan C k σ C.m with _ | b
  · have hend := hnone hsc
    have hfe : farEdge C k σ = if σ = 1 then 3 else 1 := by
      unfold farEdge; simp only [hsc]
    rcases hσ with rfl | rfl
    · Ξ hfe, ite_eq_left rfl
      have e3 : (chainModel C).wa 3 = (C.radius, -C.radius) := rfl
      have e4 : (chainModel C).wb 3 = (C.radius, C.radius) := by
        rw [wb_eq, hn, Nat.mod_eq_of_lt (⋄)]; rfl
      refine ⟨⋄, attach_on_edge (by omega) (by rw [e3, e4]; intro h; simp at h; linarith)
        (by rw [e3, e4, min_eq_left (⟡)]; linarith)
        (by rw [e3, e4, max_eq_right (⟡)]; linarith)
        (by rw [e3, e4]; unfold det; simp only; nlinarith) ?_⟩
      rw [hend, e3, e4]; ext
      · Θ xAt
      · rfl
    · rw [hfe, ite_eq_right (⊛)]
      have e1 : (chainModel C).wa 1 = (-C.radius, C.radius) := rfl
      have e2 : (chainModel C).wb 1 = (-C.radius, -C.radius) := by
        rw [wb_eq, hn, Nat.mod_eq_of_lt (⋄)]; rfl
      refine ⟨⋄, attach_on_edge (by omega) (by rw [e1, e2]; intro h; simp at h; linarith)
        (by rw [e1, e2, min_eq_right (⟡)]; linarith)
        (by rw [e1, e2, max_eq_left (⟡)]; linarith)
        (by rw [e1, e2]; unfold det; simp only; nlinarith) ?_⟩
      rw [hend, e1, e2]; ext
      · Θ xAt
      · rfl
  · obtain ⟨hend, hj, hs, -⟩ := hsome b hsc
    have hne : (C.vertex b).2 ≠ (C.vertex (b + 1)).2 :=
      ChainObs.vertex_snd_ne hDH (⋄) (by omega) (by omega)
    have hstr : min (C.vertex b).2 (C.vertex (b + 1)).2 < (C.vertex k).2 ∧
        (C.vertex k).2 < max (C.vertex b).2 (C.vertex (b + 1)).2 := by
      rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨(min_le_left _ _).trans_lt h1, h2.trans_le (le_max_right _ _)⟩
      · exact ⟨(min_le_right _ _).trans_lt h1, h2.trans_le (le_max_left _ _)⟩
    by_cases hd : 0 < det (C.vertex b) (C.vertex (b + 1)) (C.vertex k)
    · have hfe : farEdge C k σ = fwdIdx C.m (tS C) b + 6 := by
        unfold farEdge; simp only [hsc]; rw [ite_eq_left hd]
      obtain ⟨hi, e1, e2⟩ := fwdIdx_spec (C := C) hj
      have ea : (chainModel C).wa (fwdIdx C.m (tS C) b + 6) = C.vertex b := by
        rw [cwa_tour hi.le]; unfold vPt; rw [e1]
      have eb : (chainModel C).wb (fwdIdx C.m (tS C) b + 6) = C.vertex (b + 1) := by
        rw [cwb_tour hi]; unfold vPt; rw [e2]
      Ξ hfe
      refine ⟨⋄, attach_on_edge (by omega) (by rw [ea, eb]; exact hne)
        (by rw [ea, eb]; exact hstr.1) (by rw [ea, eb]; exact hstr.2) (by rw [ea, eb]; exact hd)
        (by rw [ea, eb, hend]; rfl)⟩
    · have hfe : farEdge C k σ = bwdIdx C.m (tS C) b + 6 := by
        unfold farEdge; simp only [hsc]; rw [ite_eq_right hd]
      obtain ⟨hi, e1, e2⟩ := bwdIdx_spec (C := C) hj
      have ea : (chainModel C).wa (bwdIdx C.m (tS C) b + 6) = C.vertex (b + 1) := by
        rw [cwa_tour hi.le]; unfold vPt; rw [e1]
      have eb : (chainModel C).wb (bwdIdx C.m (tS C) b + 6) = C.vertex b := by
        rw [cwb_tour hi]; unfold vPt; rw [e2]
      have hd0 : det (C.vertex b) (C.vertex (b + 1)) (C.vertex k) ≠ 0 := by
        intro h0
        have hon := det_zero_on_line hne h0
        apply C.chordEnd_ne_vertex hk hσ hf
        rw [hend]; ext
        · exact hon.symm
        · rfl
      have hneg : det (C.vertex b) (C.vertex (b + 1)) (C.vertex k) < 0 :=
        lt_of_le_of_ne (not_lt.1 hd) hd0
      Ξ hfe
      refine ⟨⋄, attach_on_edge (by omega) (by rw [ea, eb]; exact hne.symm)
        (by rw [ea, eb, min_comm]; exact hstr.1) (by rw [ea, eb, max_comm]; exact hstr.2)
        (by rw [ea, eb, Geometry.det_swap12]; linarith)
        (by rw [ea, eb, hend, xAt_comm hne]; rfl)⟩

/-! ## The vertex end -/

/-- **The vertex end**: an emitted direction at tour position `i` is free, and the chord is
attached at the walk vertex `i + 6`, whose position is the vertex. -/
theorem vert_attach (hP : C.P.Simple) (hDH : DistinctHeights C.P) {i : ℕ} (hi : i ≤ 2 * C.m)
    {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (he : emitR (prevPt C i) (vPt C i) (nextPt C i) σ) :
    C.DirFree (C.sideIdx C.sideBeta i) σ ∧
      (chainModel C).pos C.P ⟨i + 6, C.edgeIdx (C.sideIdx C.sideBeta i) + 1⟩ = vPt C i ∧
      SideAttach (chainModel C).W (C.chordSet (C.sideIdx C.sideBeta i) σ) (i + 6)
        ((chainModel C).param C.P ⟨i + 6, C.edgeIdx (C.sideIdx C.sideBeta i) + 1⟩) := by
  have hn := walk_n (C := C)
  have hpar : (chainModel C).param C.P ⟨i + 6, C.edgeIdx (C.sideIdx C.sideBeta i) + 1⟩ = 0 := by
    unfold Model.param
    simp only
    split_ifs
    · rfl
    · Ξ cwa_tour hi
      have : C.P.vtx (C.edgeIdx (C.sideIdx C.sideBeta i)) = vPt C i := rfl
      Ξ this, sub_self, zero_div
  have hpt : sidePt (chainModel C).W (i + 6) 0 = C.vertex (C.sideIdx C.sideBeta i) := by
    rw [Chain.sidePt_zero]; exact walk_vtx_tour hi
  have hl := (corner_iff hDH hi hσ).2 he
  obtain ⟨hf, hA⟩ := FuseMath.sideAttach_chordSet hP (⋄) (C.sideIdx_le _ _) hpt hσ hl
  refine ⟨hf, ?_, by rw [hpar]; exact hA⟩
  unfold Model.pos; rw [hpar, Geometry.lerp_zero]; exact cwa_tour hi

end Brute

end

end Chazelle.Core
