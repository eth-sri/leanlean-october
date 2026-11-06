module

public import Chazelle.Golf

public import Chazelle.Golf

public import Chazelle.Core.Facts2Chain

/-!
# WP-K: the weights of the full visibility map of a chain model

The brute-force procedure of WP-K (`BruteSpec`) computes the **full** vertex-chord map `C.chords`
of a chain and hands it to granularity enforcement, which needs the input to be
`γ`-semigranular.  This file proves the weight bound that makes this work:

* `fullMap_arcWt_le_two`: every arc of every region of the full map meets at most **two** counted
  walk edges, so the full map is `2`-semigranular (`fullMap_semigranular_two`);
* `fullMap_arcWt_le_one`: for a chain of **one** edge, at most one, so the full map is
  `1`-semigranular (`fullMap_semigranular_one`).

The bound `2` is optimal: under a strict local maximum `v` of the chain (for instance the middle
vertex of a two-edge chain whose middle vertex is the top), the sector of the walk below `v` is
convex and contains no horizontal direction, so no chord of any submap is attached there, and the
arc through `v` meets both chain edges at `v` (see the WP-K report: `BruteSpec` is false for
`γ = 1`, `m ≥ 2`).

## Proof

Every region `U` of the full map lies in a trapezoid (`SegObs.Trap.region_subset`) whose two
walls `sL`, `sR` are obstacle segments.  A counted walk edge facing `U` at a parameter whose point
is at no vertex height lies on a wall (`wall_of_faces`): on the left wall it is traversed
downward, on the right wall upward (the region is on the left of the walk).  Each chain edge is
traversed exactly once in each direction by the double-boundary tour (`tour_inj`), so at most one
counted walk edge faces `U` along each wall; for a single edge, the two walls cannot both be the
chain edge.
-/

namespace Chazelle.Core

@[expose] public section

open Set Filter Topology
open Chazelle.Chain (sideInArc regionsIn freeIn)
open Chazelle.Geometry (lerp)

namespace Brute

open SegObs

/-! ## The generic wall lemma (segment obstacles) -/

/-- The abscissa of the line of a segment changes linearly with the height. -/
theorem xAt_sub (s : Point × Point) (y y' : ℝ) :
    xAt s y - xAt s y' = (y - y') * ((s.2.1 - s.1.1) / (s.2.2 - s.1.2)) := by
  unfold xAt; ring

/-- Two points of an obstacle segment: the slope relation. -/
theorem slope_of_mem {s : Point × Point} (hs : s.1.2 < s.2.2) {u v : Point} (hu : u ∈ seg s)
    (hv : v ∈ seg s) : v.1 - u.1 = (v.2 - u.2) * ((s.2.1 - s.1.1) / (s.2.2 - s.1.2)) := by
  Ξ ((mem_seg_iff hs).1 hu).2.2, ((mem_seg_iff hs).1 hv).2.2, xAt_sub

/-- The offset curve tends to the base point. -/
theorem tendsto_offset (u v : Point) (t : ℝ) :
    Tendsto (fun δ => Jordan.offset u v t δ) (𝓝[>] (0 : ℝ)) (𝓝 (lerp u v t)) := by
  have hc : Continuous fun δ : ℝ => Jordan.offset u v t δ := by
    unfold Jordan.offset
    exact continuous_const.add (continuous_id.smul continuous_const)
  have h0 : Jordan.offset u v t 0 = lerp u v t := ⊚ Jordan.offset
  have := hc.tendsto 0
  Ξ' h0 at this
  exact this.mono_left nhdsWithin_le_nhds

variable {R : ℝ} {S : Set (Point × Point)} {q : Point} {sL sR : Point × Point} {y₁ y₂ : ℝ}

/-- **The wall lemma.**  Let `U` be inside the trapezoid of `q`.  If the left side of the segment
`u → v` (an obstacle segment `s`) faces the trapezoid at parameter `t`, and the point of parameter
`t` is at no vertex height, then the segment is the left wall traversed downward, or the right wall
traversed upward. -/
theorem wall_of_faces (hS : Good R S) (h : Trap R S q sL sR y₁ y₂) {s : Point × Point}
    (hs : s ∈ S) {u v : Point} (hseg : seg s = Chazelle.segment u v) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hnv : ∀ w, IsVert S w → w.2 ≠ (lerp u v t).2)
    (hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), Jordan.offset u v t δ ∈ tr sL sR y₁ y₂) :
    (v.2 < u.2 ∧ s = sL) ∨ (u.2 < v.2 ∧ s = sR) := by
  set z := lerp u v t with hzdef
  have hz : z ∈ seg s := by rw [hseg]; exact Geometry.lerp_mem_segment u v ht0 ht1
  have hsu := hS.up s hs
  have huS : u ∈ seg s := by rw [hseg]; exact Geometry.left_mem_segment _ _
  have hvS : v ∈ seg s := by rw [hseg]; exact Geometry.right_mem_segment _ _
  have hzc : z ∈ ctr sL sR y₁ y₂ :=
    closure_tr_subset _ _ _ _ (mem_closure_of_tendsto (tendsto_offset u v t) hev)
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hzc
  have hy1 : y₁ < z.2 := by
    refine lt_of_le_of_ne hp1 fun e => ?_
    obtain ⟨w, hw, hwy, -⟩ := h.bot_vertex
    exact hnv w hw (hwy.trans e)
  have hy2 : z.2 < y₂ := by
    refine lt_of_le_of_ne hp2 fun e => ?_
    obtain ⟨w, hw, hwy, -⟩ := h.top_vertex
    exact hnv w hw (hwy.trans e.symm)
  -- a point of the offset curve in the trapezoid
  obtain ⟨δ, hδin, hδ⟩ := (hev.and self_mem_nhdsWithin).exists
  have hδ0 := hδ
  obtain ⟨-, -, hoL, hoR⟩ := hδin
  Ξ' Jordan.offset_fst, Jordan.offset_snd at hoL hoR
  have hz1 : z.1 = u.1 + t * (v.1 - u.1) := rfl
  have hz2 : z.2 = u.2 + t * (v.2 - u.2) := rfl
  have huv : u.2 ≠ v.2 := by
    intro e
    have h1 : s.1 ∈ Chazelle.segment u v := hseg ▸ lo_mem_seg s
    have h2 : s.2 ∈ Chazelle.segment u v := hseg ▸ hi_mem_seg s
    obtain ⟨a, -, -, ha⟩ := h1
    obtain ⟨b, -, -, hb⟩ := h2
    have e1 : s.1.2 = u.2 := by rw [ha]; Θ e
    have e2 : s.2.2 = u.2 := by rw [hb]; Θ e
    linarith
  rcases lt_or_eq_of_le hp3 with hlt | heqL
  · rcases lt_or_eq_of_le hp4 with hlt' | heqR
    · exact absurd (h.no_obs hS (seg_subset_obs hs hz) hy1 hy2 hlt hlt') id
    · -- on the right wall
      have hzR : z ∈ seg sR := (mem_seg_iff (hS.up sR h.hR)).2
        ⟨h.botR.trans hy1.le, hy2.le.trans h.topR, heqR⟩
      have hsR : s = sR := by
        by_contra hne
        exact hnv z (hS.cross s hs sR h.hR hne z hz hzR) rfl
      subst hsR
      refine Or.inr ⟨lt_of_le_of_ne ?_ huv, rfl⟩
      by_contra hlt2
      push Not at hlt2
      have hk := slope_of_mem hsu huS hvS
      have hx := xAt_sub s (u.2 + t * (v.2 - u.2) + δ * (v.1 - u.1)) z.2
      Ξ' ← heqR, hz2 at hx
      set k := (s.2.1 - s.1.1) / (s.2.2 - s.1.2)
      have hd : 0 < u.2 - v.2 := ⟡
      have e : xAt s (u.2 + t * (v.2 - u.2) + δ * (v.1 - u.1)) - z.1 =
          δ * (v.2 - u.2) * k ^ 2 := by rw [hx, hk]; ring
      have h1 : δ * (v.2 - u.2) * k ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (⊞) (sq_nonneg k)
      have h2 : δ * (v.2 - u.2) < 0 := ⊞
      Ξ' ← hz1 at hoR
      linarith
  · -- on the left wall
    have hzL : z ∈ seg sL := (mem_seg_iff (hS.up sL h.hL)).2
      ⟨h.botL.trans hy1.le, hy2.le.trans h.topL, heqL.symm⟩
    have hsL : s = sL := by
      by_contra hne
      exact hnv z (hS.cross s hs sL h.hL hne z hz hzL) rfl
    subst hsL
    refine Or.inl ⟨lt_of_le_of_ne ?_ (Ne.symm huv), rfl⟩
    by_contra hlt2
    push Not at hlt2
    have hk := slope_of_mem hsu huS hvS
    have hx := xAt_sub s (u.2 + t * (v.2 - u.2) + δ * (v.1 - u.1)) z.2
    Ξ' heqL, hz2 at hx
    set k := (s.2.1 - s.1.1) / (s.2.2 - s.1.2)
    have hd : 0 < v.2 - u.2 := ⟡
    have e : xAt s (u.2 + t * (v.2 - u.2) + δ * (v.1 - u.1)) - z.1 =
        δ * (v.2 - u.2) * k ^ 2 := by rw [hx, hk]; ring
    have h1 : 0 ≤ δ * (v.2 - u.2) * k ^ 2 := mul_nonneg (mul_pos hδ0 hd).le (sq_nonneg k)
    have h2 : 0 < δ * (v.2 - u.2) := mul_pos hδ0 hd
    Ξ' ← hz1 at hoL
    linarith

/-! ## Small facts about the tour of the double boundary -/

/-- `ord` does not depend on the order of two points at different heights. -/
theorem ord_comm {u w : Point} (h : u.2 ≠ w.2) : ChainObs.ord u w = ChainObs.ord w u := by
  rcases lt_or_gt_of_ne h with h' | h' <;> Θ ChainObs.ord, h', not_lt.2 h'.le

/-- `ord` of a downward pair. -/
theorem ord_down {u w : Point} (h : w.2 < u.2) : ChainObs.ord u w = (w, u) := by
  Θ ChainObs.ord, not_lt.2 h.le

/-- `ord` of an upward pair. -/
theorem ord_upward {u w : Point} (h : u.2 < w.2) : ChainObs.ord u w = (u, w) := by
  Θ ChainObs.ord, h

/-- The positions of the Euler tour of the path are determined by the pair of consecutive
vertices they visit. -/
theorem sideE_pair_inj {m j j' : ℕ} (hj : j < 2 * m) (hj' : j' < 2 * m)
    (h1 : Chain.sideE m j = Chain.sideE m j') (h2 : Chain.sideE m (j + 1) = Chain.sideE m (j' + 1)) :
    j = j' := by
  unfold Chain.sideE at h1 h2; split_ifs at h1 h2 <;> omega

variable {C : Chain}

/-- **Each walk edge of the double boundary is determined by its two ends** (the tour traverses
each chain edge once in each direction). -/
theorem tour_inj (β : Bool) {i i' : ℕ} (hi : i < 2 * C.m) (hi' : i' < 2 * C.m)
    (h1 : C.sideIdx β i = C.sideIdx β i') (h2 : C.sideIdx β (i + 1) = C.sideIdx β (i' + 1)) :
    i = i' := by
  have hm := C.two_m_pos
  Ξ' Chain.sideIdx_eq, Chain.sideIdx_eq at h1
  Ξ' Chain.sideIdx_succ, Chain.sideIdx_succ at h2
  have hj := sideE_pair_inj (Nat.mod_lt _ hm) (Nat.mod_lt _ hm) h1 h2
  have h3 := hj
  exact Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_left_cancel' _ h3) hi hi'

/-- The walk edge `i + 6` of the chain model starts at the tour vertex `i`. -/
theorem wa_tour (β : Bool) {i : ℕ} (hi : i < 2 * C.m) :
    (C.sideWalk β).vtx (i + 6) = C.vertex (C.sideIdx β i) :=
  C.sideWalk_vtx_tour β (⋄)

/-- The walk edge `i + 6` of the chain model ends at the tour vertex `i + 1`. -/
theorem wb_tour (β : Bool) {i : ℕ} (hi : i < 2 * C.m) :
    (C.sideWalk β).vtx ((i + 6 + 1) % (C.sideWalk β).n) = C.vertex (C.sideIdx β (i + 1)) := by
  Ξ C.sideWalk_n, Nat.mod_eq_of_lt (⋄), show i + 6 + 1 = (i + 1) + 6 by ring
  exact C.sideWalk_vtx_tour β (⋄)

/-- The ends of a walk edge of the double boundary span a chain edge. -/
theorem tour_edge (hDH : DistinctHeights C.P) (β : Bool) (i : ℕ) :
    (C.vertex (C.sideIdx β i)).2 ≠ (C.vertex (C.sideIdx β (i + 1))).2 ∧
      ∃ k < C.m, ChainObs.ord (C.vertex (C.sideIdx β i)) (C.vertex (C.sideIdx β (i + 1))) =
        ChainObs.ord (C.vertex k) (C.vertex (k + 1)) := by
  have hl := C.sideIdx_le β i
  have hl' := C.sideIdx_le β (i + 1)
  have hs := C.sideTour_step β i
  have hne : C.sideIdx β i ≠ C.sideIdx β (i + 1) := by rcases hs with h | h <;> omega
  have hv := ChainObs.vertex_snd_ne hDH hl hl' hne
  refine ⟨hv, ?_⟩
  rcases hs with h | h
  · exact ⟨C.sideIdx β i, ⋄, Ρ h⟩
  · refine ⟨C.sideIdx β (i + 1), ⋄, ?_⟩
    Ξ ord_comm hv, h

/-! ## The classification of the counted walk edges facing a region of the full map -/

/-- The set of keys inside an arc is open. -/
theorem isOpen_sideInArc (a b : ℝ) : IsOpen {x : ℝ | sideInArc a b x} := by
  by_cases hab : a < b
  · ϴ sideInArc, hab, ite_true
    exact (isOpen_lt continuous_const continuous_id).inter (isOpen_lt continuous_id continuous_const)
  · ϴ sideInArc, hab, ite_false
    exact (isOpen_lt continuous_const continuous_id).union (isOpen_lt continuous_id continuous_const)

/-- A point of an open set of reals can be moved off a finite set. -/
theorem exists_avoid {O : Set ℝ} (hO : IsOpen O) {t : ℝ} (ht : t ∈ O) {B : Set ℝ}
    (hB : B.Finite) : ∃ t' ∈ O, t' ∉ B := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO t ht
  have hinf : (Metric.ball t ε).Infinite := by
    rw [Real.ball_eq_Ioo]; exact Set.Ioo_infinite (⟡)
  obtain ⟨t', ht'1, ht'2⟩ := (hinf.sdiff hB).nonempty
  exact ⟨t', hball ht'1, ht'2⟩

/-- **The classification.**  Let `U` be the region of `z` in the full map, with trapezoid data
`sL, sR`.  A counted walk edge `i + 6` whose open key interval part `(p + t)`, `0 < t < 1`, lies in
an arc of `U` is the left wall traversed downward or the right wall traversed upward. -/
theorem arc_edge_class (hP : C.P.Simple) (hDH : DistinctHeights C.P) {z : Point}
    {sL sR : Point × Point} {y₁ y₂ : ℝ} (hT : Trap C.radius (ChainObs.segs C) z sL sR y₁ y₂)
    (hU : connectedComponentIn (freeIn C.dom C.chords) z ⊆ tr sL sR y₁ y₂) {a b : ℝ}
    (hab : (chainModel C).IsArc C.chords (connectedComponentIn (freeIn C.dom C.chords) z) a b)
    {i : ℕ} (hi : i < 2 * C.m) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hin : sideInArc a b ((i + 6 : ℕ) + t)) :
    ((C.vertex (C.sideIdx C.sideBeta (i + 1))).2 < (C.vertex (C.sideIdx C.sideBeta i)).2 ∧
        ChainObs.ord (C.vertex (C.sideIdx C.sideBeta i))
          (C.vertex (C.sideIdx C.sideBeta (i + 1))) = sL) ∨
      ((C.vertex (C.sideIdx C.sideBeta i)).2 < (C.vertex (C.sideIdx C.sideBeta (i + 1))).2 ∧
        ChainObs.ord (C.vertex (C.sideIdx C.sideBeta i))
          (C.vertex (C.sideIdx C.sideBeta (i + 1))) = sR) := by
  have hS := ChainObs.good hP hDH
  set u := C.vertex (C.sideIdx C.sideBeta i) with hu
  set v := C.vertex (C.sideIdx C.sideBeta (i + 1)) with hv
  obtain ⟨huv, k, hk, hord⟩ := tour_edge hDH C.sideBeta i
  have hs : ChainObs.ord u v ∈ ChainObs.segs C := Or.inl ⟨k, hk, hord⟩
  have hseg : seg (ChainObs.ord u v) = Chazelle.segment u v := ChainObs.seg_ord u v
  -- the parameters of the edge inside the arc
  set O : Set ℝ := {t' | 0 < t' ∧ t' < 1 ∧ sideInArc a b ((i + 6 : ℕ) + t')} with hO
  have hOopen : IsOpen O := by
    refine (isOpen_lt continuous_const continuous_id).inter
      ((isOpen_lt continuous_id continuous_const).inter ?_)
    exact (isOpen_sideInArc a b).preimage (continuous_const.add continuous_id)
  set B : Set ℝ := (fun w : Point => (w.2 - u.2) / (v.2 - u.2)) '' {w | IsVert (ChainObs.segs C) w}
    with hB
  have hBfin : B.Finite := (finite_verts hS).image _
  obtain ⟨t', ⟨ht'0, ht'1, ht'in⟩, ht'B⟩ := exists_avoid hOopen ⟨ht0, ht1, hin⟩ hBfin
  have hnv : ∀ w, IsVert (ChainObs.segs C) w → w.2 ≠ (lerp u v t').2 := by
    intro w hw e
    apply ht'B
    refine ⟨w, hw, ?_⟩
    ϴ' Geometry.lerp_snd at e
    have hd : v.2 - u.2 ≠ 0 := sub_ne_zero.2 (Ne.symm huv)
    field_simp
    linarith
  -- the edge faces the region
  have hF := hab.2.2.2.2.2.2 (i + 6) t' (by
    show i + 6 < (C.sideWalk C.sideBeta).n; rw [C.sideWalk_n]; omega) ht'0 ht'1 ht'in
  have hF' : ∀ᶠ δ in 𝓝[>] (0 : ℝ), Jordan.offset u v t' δ ∈ tr sL sR y₁ y₂ := by
    have e1 : (chainModel C).wa (i + 6) = u := wa_tour C.sideBeta hi
    have e2 : (chainModel C).wb (i + 6) = v := wb_tour C.sideBeta hi
    unfold Model.Faces at hF
    Ξ' e1, e2 at hF
    exact hF.mono fun δ hδ => hU hδ
  rcases wall_of_faces hS hT hs hseg ht'0.le ht'1.le hnv hF' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩

/-! ## The weight bounds -/

/-- The trapezoid data of a region of the full map. -/
theorem region_trap (hP : C.P.Simple) (hDH : DistinctHeights C.P) {z : Point}
    (hz : z ∈ freeIn C.dom C.chords) :
    ∃ sL sR y₁ y₂, Trap C.radius (ChainObs.segs C) z sL sR y₁ y₂ ∧
      connectedComponentIn (freeIn C.dom C.chords) z ⊆ tr sL sR y₁ y₂ := by
  have hS := ChainObs.good hP hDH
  have hfull : FullAt C.radius (ChainObs.segs C) C.chords := ChainObs.fullAt subset_rfl
  have hdom := ChainObs.dom_eq (C := C)
  Ξ' ← hdom at hz ⊢
  obtain ⟨sL, sR, y₁, y₂, hT⟩ := exists_trap hS hfull hz.1 hz.2
  exact ⟨sL, sR, y₁, y₂, hT, hT.region_subset hS hfull hz⟩

/-- The counted walk edges met by an arc (the set whose size is `arcWt`). -/
def arcEdgeSet (C : Chain) (a b : ℝ) : Set ℕ :=
  {p : ℕ | p < (chainModel C).W.n ∧ (chainModel C).counted p ∧
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ sideInArc a b (p + t)}

theorem arcWt_eq (a b : ℝ) : (chainModel C).arcWt a b = (arcEdgeSet C a b).ncard := rfl

/-- A member of the edge set of an arc of a region of the full map, with its class. -/
theorem arcEdge_class (hP : C.P.Simple) (hDH : DistinctHeights C.P) {z : Point}
    {sL sR : Point × Point} {y₁ y₂ : ℝ} (hT : Trap C.radius (ChainObs.segs C) z sL sR y₁ y₂)
    (hU : connectedComponentIn (freeIn C.dom C.chords) z ⊆ tr sL sR y₁ y₂) {a b : ℝ}
    (hab : (chainModel C).IsArc C.chords (connectedComponentIn (freeIn C.dom C.chords) z) a b)
    {p : ℕ} (hp : p ∈ arcEdgeSet C a b) :
    ∃ i, i < 2 * C.m ∧ p = i + 6 ∧
      (((C.vertex (C.sideIdx C.sideBeta (i + 1))).2 < (C.vertex (C.sideIdx C.sideBeta i)).2 ∧
        ChainObs.ord (C.vertex (C.sideIdx C.sideBeta i))
          (C.vertex (C.sideIdx C.sideBeta (i + 1))) = sL) ∨
      ((C.vertex (C.sideIdx C.sideBeta i)).2 < (C.vertex (C.sideIdx C.sideBeta (i + 1))).2 ∧
        ChainObs.ord (C.vertex (C.sideIdx C.sideBeta i))
          (C.vertex (C.sideIdx C.sideBeta (i + 1))) = sR)) := by
  obtain ⟨-, ⟨hc1, hc2⟩, t, ht0, ht1, hin⟩ := hp
  refine ⟨p - 6, ⋄, ⋄, ?_⟩
  have e : ((p - 6 + 6 : ℕ) : ℝ) = (p : ℝ) := Ρ Nat.sub_add_cancel hc1
  exact arc_edge_class hP hDH hT hU hab (⋄) ht0 ht1 (by rw [e]; exact hin)

/-- Two walk edges of the same class are equal. -/
theorem class_inj (hP : C.P.Simple) {i i' : ℕ} (hi : i < 2 * C.m) (hi' : i' < 2 * C.m)
    (hord : ChainObs.ord (C.vertex (C.sideIdx C.sideBeta i))
        (C.vertex (C.sideIdx C.sideBeta (i + 1))) =
      ChainObs.ord (C.vertex (C.sideIdx C.sideBeta i'))
        (C.vertex (C.sideIdx C.sideBeta (i' + 1))))
    (hdir : (C.vertex (C.sideIdx C.sideBeta i)).2 < (C.vertex (C.sideIdx C.sideBeta (i + 1))).2 ↔
      (C.vertex (C.sideIdx C.sideBeta i')).2 < (C.vertex (C.sideIdx C.sideBeta (i' + 1))).2)
    (hne : (C.vertex (C.sideIdx C.sideBeta i)).2 ≠ (C.vertex (C.sideIdx C.sideBeta (i + 1))).2)
    (hne' : (C.vertex (C.sideIdx C.sideBeta i')).2 ≠
      (C.vertex (C.sideIdx C.sideBeta (i' + 1))).2) : i = i' := by
  have hl := C.sideIdx_le C.sideBeta
  have key : C.vertex (C.sideIdx C.sideBeta i) = C.vertex (C.sideIdx C.sideBeta i') ∧
      C.vertex (C.sideIdx C.sideBeta (i + 1)) = C.vertex (C.sideIdx C.sideBeta (i' + 1)) := by
    rcases lt_or_gt_of_ne hne with h | h
    · Ξ' ord_upward h, ord_upward (hdir.1 h) at hord
      exact ⟨(Prod.ext_iff.1 hord).1, (Prod.ext_iff.1 hord).2⟩
    · have h' : (C.vertex (C.sideIdx C.sideBeta (i' + 1))).2 <
          (C.vertex (C.sideIdx C.sideBeta i')).2 :=
        lt_of_le_of_ne (not_lt.1 fun h2 => absurd (hdir.2 h2) (not_lt.2 h.le)) (Ne.symm hne')
      Ξ' ord_down h, ord_down h' at hord
      exact ⟨(Prod.ext_iff.1 hord).2, (Prod.ext_iff.1 hord).1⟩
  exact tour_inj C.sideBeta hi hi' (C.sideVertex_inj hP (hl _) (hl _) key.1)
    (C.sideVertex_inj hP (hl _) (hl _) key.2)

/-- **The arcs of the full map meet at most two counted walk edges.** -/
theorem fullMap_arcWt_le_two (hP : C.P.Simple) (hDH : DistinctHeights C.P) {U : Set Point}
    (hU : U ∈ (chainModel C).regions C.chords) {a b : ℝ}
    (hab : (chainModel C).IsArc C.chords U a b) : (chainModel C).arcWt a b ≤ 2 := by
  obtain ⟨z, hz, rfl⟩ := hU
  obtain ⟨sL, sR, y₁, y₂, hT, hsub⟩ := region_trap hP hDH hz
  Ξ arcWt_eq
  set A := arcEdgeSet C a b
  set Dn := {p ∈ A | ∀ i, p = i + 6 →
    (C.vertex (C.sideIdx C.sideBeta (i + 1))).2 < (C.vertex (C.sideIdx C.sideBeta i)).2}
  set Up := {p ∈ A | ∀ i, p = i + 6 →
    (C.vertex (C.sideIdx C.sideBeta i)).2 < (C.vertex (C.sideIdx C.sideBeta (i + 1))).2}
  have hfinA : A.Finite := (Set.finite_lt_nat (chainModel C).W.n).subset fun p hp => hp.1
  have hcover : A ⊆ Dn ∪ Up := by
    intro p hp
    obtain ⟨i, -, rfl, hcl⟩ := arcEdge_class hP hDH hT hsub hab hp
    rcases hcl with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl ⟨hp, fun i' e => by rw [show i' = i by omega]; exact h1⟩
    · exact Or.inr ⟨hp, fun i' e => by rw [show i' = i by omega]; exact h1⟩
  have hDn : Dn.ncard ≤ 1 := by
    Ξ Set.ncard_le_one_iff (hfinA.subset fun p hp => hp.1)
    intro p p' hp hp'
    obtain ⟨i, hi, rfl, hcl⟩ := arcEdge_class hP hDH hT hsub hab hp.1
    obtain ⟨i', hi', rfl, hcl'⟩ := arcEdge_class hP hDH hT hsub hab hp'.1
    have hd := hp.2 i rfl
    have hd' := hp'.2 i' rfl
    have hne := (tour_edge hDH C.sideBeta i).1
    have hne' := (tour_edge hDH C.sideBeta i').1
    rcases hcl with ⟨-, h1⟩ | ⟨h1, -⟩
    · rcases hcl' with ⟨-, h1'⟩ | ⟨h1', -⟩
      · rw [class_inj hP hi hi' (h1.trans h1'.symm)
          ⟨fun h => absurd hd (not_lt.2 h.le), fun h => absurd hd' (not_lt.2 h.le)⟩ hne hne']
      · exact absurd hd' (not_lt.2 h1'.le)
    · exact absurd hd (not_lt.2 h1.le)
  have hUp : Up.ncard ≤ 1 := by
    Ξ Set.ncard_le_one_iff (hfinA.subset fun p hp => hp.1)
    intro p p' hp hp'
    obtain ⟨i, hi, rfl, hcl⟩ := arcEdge_class hP hDH hT hsub hab hp.1
    obtain ⟨i', hi', rfl, hcl'⟩ := arcEdge_class hP hDH hT hsub hab hp'.1
    have hd := hp.2 i rfl
    have hd' := hp'.2 i' rfl
    have hne := (tour_edge hDH C.sideBeta i).1
    have hne' := (tour_edge hDH C.sideBeta i').1
    rcases hcl with ⟨h1, -⟩ | ⟨-, h1⟩
    · exact absurd hd (not_lt.2 h1.le)
    · rcases hcl' with ⟨h1', -⟩ | ⟨-, h1'⟩
      · exact absurd hd' (not_lt.2 h1'.le)
      · Ξ class_inj hP hi hi' (h1.trans h1'.symm) ⟨fun _ => hd', fun _ => hd⟩ hne hne'
  calc A.ncard ≤ (Dn ∪ Up).ncard := Set.ncard_le_ncard hcover ((hfinA.subset fun p hp => hp.1).union
        (hfinA.subset fun p hp => hp.1))
    _ ≤ Dn.ncard + Up.ncard := Set.ncard_union_le _ _
    _ ≤ 2 := ⋄

/-- **For a chain of one edge, the arcs of the full map meet at most one counted walk edge.** -/
theorem fullMap_arcWt_le_one (hP : C.P.Simple) (hDH : DistinctHeights C.P) (hm : C.m = 1)
    {U : Set Point} (hU : U ∈ (chainModel C).regions C.chords) {a b : ℝ}
    (hab : (chainModel C).IsArc C.chords U a b) : (chainModel C).arcWt a b ≤ 1 := by
  obtain ⟨z, hz, rfl⟩ := hU
  obtain ⟨sL, sR, y₁, y₂, hT, hsub⟩ := region_trap hP hDH hz
  have hLR : sL ≠ sR := by
    intro e; Ξ' e at hT; exact lt_irrefl _ (hT.lt_q.trans hT.q_lt)
  Ξ arcWt_eq
  have hfinA : (arcEdgeSet C a b).Finite :=
    (Set.finite_lt_nat (chainModel C).W.n).subset fun p hp => hp.1
  Ξ Set.ncard_le_one_iff hfinA
  intro p p' hp hp'
  obtain ⟨i, hi, rfl, hcl⟩ := arcEdge_class hP hDH hT hsub hab hp
  obtain ⟨i', hi', rfl, hcl'⟩ := arcEdge_class hP hDH hT hsub hab hp'
  obtain ⟨hne, k, hk, hord⟩ := tour_edge hDH C.sideBeta i
  obtain ⟨hne', k', hk', hord'⟩ := tour_edge hDH C.sideBeta i'
  have hk0 : k = 0 := ⋄
  have hk0' : k' = 0 := ⋄
  subst hk0 hk0'
  have hsame := hord.trans hord'.symm
  rcases hcl with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hcl' with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
  · rw [class_inj hP hi hi' hsame
      ⟨fun h => absurd h1 (not_lt.2 h.le), fun h => absurd h1' (not_lt.2 h.le)⟩ hne hne']
  · exact absurd (h2.symm.trans (hsame.trans h2')) hLR
  · exact absurd (h2'.symm.trans (hsame.symm.trans h2)) hLR
  · Ξ class_inj hP hi hi' hsame ⟨fun _ => h1', fun _ => h1⟩ hne hne'

/-- **The full map of a chain model is `2`-semigranular** (distinct heights). -/
theorem fullMap_semigranular_two (hP : C.P.Simple) (hDH : DistinctHeights C.P) :
    (chainModel C).Semigranular C.chords 2 := by
  intro U hU
  refine csSup_le' ?_
  rintro w ⟨ab, hab, rfl⟩
  exact fullMap_arcWt_le_two hP hDH hU hab

/-- **The full map of a one-edge chain model is `1`-semigranular** (distinct heights). -/
theorem fullMap_semigranular_one (hP : C.P.Simple) (hDH : DistinctHeights C.P) (hm : C.m = 1) :
    (chainModel C).Semigranular C.chords 1 := by
  intro U hU
  refine csSup_le' ?_
  rintro w ⟨ab, hab, rfl⟩
  exact fullMap_arcWt_le_one hP hDH hm hU hab

/-- **The full map is `γ`-semigranular** for every `γ ≥ 2`, and for `γ ≥ 1` when the chain has
one edge: exactly the granularities of the corrected `BruteSpec` precondition. -/
theorem fullMap_semigranular (hP : C.P.Simple) (hDH : DistinctHeights C.P) {γ : ℕ}
    (hγ : C.m = 1 ∧ 1 ≤ γ ∨ 2 ≤ γ) : (chainModel C).Semigranular C.chords γ := by
  intro U hU
  rcases hγ with ⟨hm, hγ⟩ | hγ
  · exact (fullMap_semigranular_one hP hDH hm U hU).trans hγ
  · exact (fullMap_semigranular_two hP hDH U hU).trans hγ

end Brute

end

end Chazelle.Core
